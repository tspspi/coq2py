(* main.ml -- the coq2py CLI driver.

   This is explicitly *not* part of the proven translator: it is file
   I/O and argument parsing glue around the three proven/extracted
   entry points (parse_expr_top, translate, py_function). Per GOAL.md,
   peripheral plumbing like this does not need its own correctness
   proof -- only the Gallina pipeline it calls does. *)

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
     \n\
     Reads a JSON-encoded expr (see coq/Json.v for the restricted\n\
     grammar; examples/Kinematics.v shows how to produce one) on\n\
     stdin, and prints the translated, generated Python function to\n\
     stdout.\n";
  exit 1

let () =
  if Array.length Sys.argv <> 3 then usage ();
  let name = Sys.argv.(1) in
  let params = String.split_on_char ',' Sys.argv.(2) in
  let input = read_all_stdin () in
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
