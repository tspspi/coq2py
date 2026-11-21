(* main.ml -- the coq2py CLI driver.

   This is explicitly *not* part of the proven translator: it is file
   I/O, argument parsing, and declaration-shape dispatch glue around
   proven/extracted entry points (parse_expr_top / real_*_of_module_json
   / real_*_to_expr / translate / py_function). Per GOAL.md, peripheral
   plumbing like this does not need its own correctness proof -- only
   the Gallina pipeline it calls does.

   Two input modes, matching the two JSON shapes this project's
   pipeline actually sees (see docs/roadmap.md's deployment entry for
   why both need to exist for the remote-host workflow, not just the
   first):

   - Default: this project's own hand-rolled [Json.v] wire format for
     a bare [expr] (what every example in examples/ prints via
     [Compute print_expr ...]) -- the format this CLI has always
     accepted.
   - [--real]: a genuine [coqc Extraction Language JSON] module, the
     format a theory-evaluating agent's own freshly-proved [.v] file
     actually produces. [RealIR.v]/[RealJson.v] prove how to recognize
     four declaration shapes inside one (plain, possibly multi-arg,
     non-recursive; single-argument self-recursive; multi-argument
     self-recursive; N-way mutually-recursive) -- tried here in that
     order, first match wins, since a real module's declaration is
     exactly one of these, never more than one. *)

let read_all_stdin () =
  let buf = Buffer.create 4096 in
  (try
     while true do
       Buffer.add_channel buf stdin 4096
     done
   with End_of_file -> ());
  Buffer.contents buf

let usage () =
  Printf.eprintf
    "usage: coq2py <function-name> <param1,param2,...> < input.json\n\
    \       coq2py --real <function-name> < module.json\n\
     \n\
     First form: reads a JSON-encoded expr (see coq/Json.v for the\n\
     restricted grammar; examples/Kinematics.v shows how to produce\n\
     one) on stdin, and prints the translated, generated Python\n\
     function to stdout.\n\
     \n\
     Second form (--real): reads a real coqc 'Extraction Language\n\
     JSON' module (the whole module, as coqc emits it) on stdin,\n\
     looks up <function-name> among its declarations, and prints the\n\
     translated, generated Python function to stdout. Only the\n\
     subset of Coq docs/roadmap.md documents as recognized will\n\
     succeed; anything else is reported as an error on stderr with a\n\
     nonzero exit code, never a silent wrong answer.\n";
  exit 1

(* Apply a already-proven-translatable closure [expr] to a left-to-right
   list of named parameters, [EApp]-ing one at a time -- the same
   calling convention every multi-argument closure in this project's
   own examples/ (e.g. examples/physics/Discretize.v's wave_sim_expr
   call site) already uses before handing a closure to [py_function]. *)
let apply_params (e : Coq2py_core.expr) (params : string list) : Coq2py_core.expr =
  List.fold_left (fun acc p -> Coq2py_core.EApp (acc, Coq2py_core.EVar p)) e params

(* The four recognized real-declaration shapes, tried in order; each
   returns the (parameter names, fully-applied body expr) py_function
   needs, or None if this module/name doesn't match that shape. *)
let try_real_decl (module_json : string) (target : string) :
    (string list * Coq2py_core.expr) option =
  match Coq2py_core.real_decl_of_module_json module_json target with
  | Some rd ->
      (match Coq2py_core.real_decl_to_expr rd with
       | Some e -> Some (rd.Coq2py_core.rd_argnames, e)
       | None -> None)
  | None -> None

let try_real_fix_decl (module_json : string) (target : string) :
    (string list * Coq2py_core.expr) option =
  match Coq2py_core.real_fix_decl_of_module_json module_json target with
  | Some rfd ->
      (match Coq2py_core.real_fix_decl_to_expr rfd with
       | Some e ->
           let params = [ rfd.Coq2py_core.rfd_param ] in
           Some (params, apply_params e params)
       | None -> None)
  | None -> None

let try_real_fix_decl_multi (module_json : string) (target : string) :
    (string list * Coq2py_core.expr) option =
  match Coq2py_core.real_fix_decl_multi_of_module_json module_json target with
  | Some rfdm ->
      (match Coq2py_core.real_fix_decl_multi_to_expr rfdm with
       | Some e ->
           let params = rfdm.Coq2py_core.rfdm_params in
           Some (params, apply_params e params)
       | None -> None)
  | None -> None

let try_real_fix_group_decl (module_json : string) (target : string) :
    (string list * Coq2py_core.expr) option =
  match Coq2py_core.real_fix_group_decl_of_module_json module_json target with
  | Some rfgd ->
      (match Coq2py_core.real_fix_group_decl_to_expr rfgd with
       | Some group_e ->
           (* Each group member is single-argument (RealIR.v's own
              [real_fix_group_decl] header); find [target]'s own
              parameter name among the group's (name, param) pairs --
              it need not match any other member's, and the group may
              be entered from any member, not just the first. *)
           let members = Coq2py_core.rfgd_fns rfgd in
           (match List.find_opt (fun ((n, _), _) -> n = target) members with
            | Some ((_, param), _) ->
                let projected = Coq2py_core.EFieldN (target, group_e) in
                Some ([ param ], apply_params projected [ param ])
            | None -> None)
       | None -> None)
  | None -> None

let run_real (target : string) (module_json : string) : unit =
  let attempts =
    [ try_real_decl; try_real_fix_decl; try_real_fix_decl_multi;
      try_real_fix_group_decl ]
  in
  match
    List.fold_left
      (fun acc f -> match acc with Some _ -> acc | None -> f module_json target)
      None attempts
  with
  | None ->
      Printf.eprintf
        "coq2py: %S was not found, or is not in the recognized Coq subset \
         (see docs/roadmap.md)\n"
        target;
      exit 1
  | Some (params, applied) ->
      let py_ast = Coq2py_core.translate applied in
      print_string (Coq2py_core.py_function target params py_ast)

let run_plain (name : string) (params : string list) (input : string) : unit =
  match Coq2py_core.parse_expr_top input with
  | None ->
      Printf.eprintf "coq2py: could not parse input as a JSON-encoded expr\n";
      exit 1
  | Some (e, leftover) ->
      if String.length leftover > 0 then
        Printf.eprintf
          "coq2py: warning: %d trailing byte(s) after the parsed expr were ignored\n"
          (String.length leftover);
      let py_ast = Coq2py_core.translate e in
      print_string (Coq2py_core.py_function name params py_ast)

let () =
  match Sys.argv with
  | [| _; "--real"; target |] -> run_real target (read_all_stdin ())
  | [| _; name; params_csv |] ->
      run_plain name (String.split_on_char ',' params_csv) (read_all_stdin ())
  | _ -> usage ()
