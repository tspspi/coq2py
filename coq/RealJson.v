(** RealJson.v

    A real JSON-*text* parser for Coq's own [Extraction Language JSON]
    output -- the piece [RealIR.v]'s header has flagged, since that
    file's very first commit, as "not yet written": until now, every
    [real_decl]/[real_expr] in the examples was built *by hand* to
    match what a probe run of [coqc] was observed to emit, never
    mechanically parsed from the actual JSON bytes. This file closes
    that gap.

    Two layers, kept deliberately separate:
    - [jvalue]/[parse_json]: a small, *generic* JSON value parser
      (objects/arrays/strings/numbers/bools/null), independent of
      anything [RealIR.v]-specific, reusing [Json.v]'s string/number
      lexing ([parse_qtext]/[parse_number]) unchanged. The one
      substantive difference from [Json.v]'s own bespoke grammar: real
      [coqc] extraction output is pretty-printed with embedded
      newlines/indentation (confirmed directly -- [Json.v]'s grammar
      is deliberately whitespace-free), so every token boundary here
      skips whitespace first.
    - [real_expr_of_json]/[real_decl_of_json]/[real_fix_decl_of_json]:
      the [RealIR.v]-specific *interpreter* from [jvalue] into this
      project's already-proven [real_expr]/[real_decl]/
      [real_fix_decl], recognizing exactly the real, [coqc]-confirmed
      shapes: [decl:term] / [decl:fixgroup]'s [fixgroup:item] /
      [expr:lambda] (with a direct, non-curried [argnames] list) /
      [expr:case] + [case] + [pat:constructor] / [expr:apply] /
      [expr:global] / [expr:rel] / [expr:constructor] (covering
      [True]/[False], [Nil]/[Cons], [Pair], [Inl]/[Inr], [Z0]/[Zpos]/
      [Zneg] applied to nested [XI]/[XO]/[XH] for a numeral, and an
      arbitrary N-ary record constructor name for [RRecord3]), a
      self-recursive call recognized as an [expr:apply] whose [func] is
      an [expr:global] naming the enclosing [fixgroup:item] itself, and
      (confirmed against a real, Coquelicot-adjacent probe -- see
      [RealIR.v]'s own header) a Coquelicot-adjacent [R] literal, which
      extracts as [expr:apply]/[expr:global "iZR"] applied to a nested
      [Z] numeral -- recognized specially (via [float_of_Z], turning
      the parsed numeral directly into an [RFLit]) rather than falling
      through to the generic [expr:apply]/[expr:global] dispatch below,
      which would otherwise build an unrecognized [RApp1 "iZR" (RZLit
      z)] (["iZR"] is not a name [RealIR.v]'s [real_eval]/
      [real_to_expr] know, only [RFLit] is).
      Every one of these shapes was confirmed by a *fresh* probe run of
      [coqc] 8.18.0 on genuine, human-written [Definition]s/
      [Fixpoint]s (not reused from this file's own prose, and not
      assumed) -- see the scratch probes this commit's message points
      to. Anything outside the already-recognized [real_expr] fragment
      is simply [None], the same honest partiality [real_to_expr]
      itself already uses.

    One confirmed limitation, not yet handled: Coq's extraction will
    eta-reduce a definition whose body is *exactly* another function
    applied to all its arguments in order (e.g. [Definition getfst p
    := fst p] extracts as a bare [expr:global "fst"], not an
    [expr:lambda] applying it) -- probed directly. [real_decl_of_json]
    does not re-expand this; a [decl:term] whose [value] is not an
    [expr:lambda] is simply not recognized. This does not affect
    ordinary, non-point-free physics/math definitions (the only kind
    this project's examples use), but is worth naming rather than
    silently mishandling.

    Performance: the straightforward version of this parser, run on a
    real 22KB [coqc]-extracted module, took 45 *seconds* -- traced to
    four separate O(n^2) spots in [Json.v]'s/this file's string-scanning
    primitives under [ExtrOcamlNativeString]'s realization of [string]
    pattern-matching (one re-slices the remaining input per character
    consumed) plus [nat]'s default unary representation. Fixed via four
    targeted [Extract Constant] realizers in [Extract.v] -- replacing
    only the *extracted OCaml*, not the Coq-level definitions or any
    proof about them -- bringing the same 22KB module under 0.2
    seconds; see [Extract.v]'s comment for the full before/after
    trail. This is why every entry point below takes a [fuel] derived
    from [String.length s + 1] ([Json.v]'s own [parse_expr_top]
    convention) rather than something tighter: fuel is now cheap to
    have plenty of.

    What is proved here and what is not, stated plainly: [parse_json]
    is a total, fuel-bounded function (it always terminates), but
    unlike [Json.v]'s [parse_print_roundtrip] this file does not yet
    carry a machine-checked roundtrip or soundness theorem of its own;
    the proved, trusted end of the pipeline still starts at
    [real_decl] ([real_decl_to_expr_preserves_semantics], already
    proved, in [RealIR.v]). Correctness of parsing real [coqc] output
    into a [real_decl] is checked, for now, by actually running it on
    real extracted JSON (four confirmed, working instances: [clamp_nonneg]'s
    [if], [classify]'s 2-case sum, [swap_xz]'s 3-field record, and
    [any_true]'s self-recursive [Fixpoint] over a list -- each
    producing, through the full, already-proven rest of the pipeline,
    *exactly* the same generated Python the hand-built [real_decl]/
    [real_fix_decl] for the same source definition already produces in
    [examples/NaturalCoq.v]) -- not yet by proof. Tracked in
    docs/roadmap.md as this file's own next step. *)

From Coq Require Import ZArith String List Bool Ascii Lia.
From Coq Require Import Floats.PrimFloat Floats.FloatOps Floats.SpecFloat.
Import ListNotations.
Require Import Lang.
Require Import RealIR.
Require Import Json.
Open Scope string_scope.
Open Scope nat_scope.

(* ------------------------------------------------------------------ *)
(** * A generic JSON value, and a parser for it *)

Inductive jvalue : Type :=
  | JString (s : string)
  | JBool (b : bool)
  | JNull
  | JNum (z : Z)
  | JArray (vs : list jvalue)
  | JObject (fields : list (string * jvalue)).

Definition is_ws (a : ascii) : bool :=
  orb (Ascii.eqb a " "%char)
      (orb (Ascii.eqb a (ascii_of_nat 10))
           (orb (Ascii.eqb a (ascii_of_nat 13)) (Ascii.eqb a (ascii_of_nat 9)))).

Definition skip_ws (s : string) : string := snd (take_while is_ws s).

(** One [fuel] unit is spent per [jvalue] level of nesting *and* per
    sibling visited inside one [JObject]/[JArray] (both the per-level
    [parse_members]/[parse_elems] loop and [parse_jvalue] itself
    decrement it) -- generous, but always at least the real recursion
    depth, the same margin [Json.v]'s [String.length s + 1] convention
    already relies on elsewhere ([parse_expr_top]). *)
Fixpoint parse_jvalue (fuel : nat) (s : string) : option (jvalue * string) :=
  match fuel with
  | O => None
  | S fuel' =>
      let s := skip_ws s in
      match expect "{" s with
      | Some rest =>
          match
            (fix parse_members (fuel0 : nat) (s0 : string) : option (list (string * jvalue) * string) :=
               match fuel0 with
               | O => None
               | S fuel0' =>
                   let s0 := skip_ws s0 in
                   match expect "}" s0 with
                   | Some rest0 => Some ([], rest0)
                   | None =>
                       match parse_qtext s0 with
                       | Some (key, rest1) =>
                           match expect ":" (skip_ws rest1) with
                           | Some rest2 =>
                               match parse_jvalue fuel0' (skip_ws rest2) with
                               | Some (v, rest3) =>
                                   let rest3 := skip_ws rest3 in
                                   match expect "," rest3 with
                                   | Some rest4 =>
                                       match parse_members fuel0' (skip_ws rest4) with
                                       | Some (fs, rest5) => Some ((key, v) :: fs, rest5)
                                       | None => None
                                       end
                                   | None =>
                                       match expect "}" rest3 with
                                       | Some rest4 => Some ([(key, v)], rest4)
                                       | None => None
                                       end
                                   end
                               | None => None
                               end
                           | None => None
                           end
                       | None => None
                       end
                   end
               end) fuel' (skip_ws rest)
          with
          | Some (fs, rest') => Some (JObject fs, rest')
          | None => None
          end
      | None =>
      match expect "[" s with
      | Some rest =>
          match
            (fix parse_elems (fuel0 : nat) (s0 : string) : option (list jvalue * string) :=
               match fuel0 with
               | O => None
               | S fuel0' =>
                   let s0 := skip_ws s0 in
                   match expect "]" s0 with
                   | Some rest0 => Some ([], rest0)
                   | None =>
                       match parse_jvalue fuel0' s0 with
                       | Some (v, rest1) =>
                           let rest1 := skip_ws rest1 in
                           match expect "," rest1 with
                           | Some rest2 =>
                               match parse_elems fuel0' (skip_ws rest2) with
                               | Some (vs, rest3) => Some (v :: vs, rest3)
                               | None => None
                               end
                           | None =>
                               match expect "]" rest1 with
                               | Some rest2 => Some ([v], rest2)
                               | None => None
                               end
                           end
                       | None => None
                       end
                   end
               end) fuel' (skip_ws rest)
          with
          | Some (vs, rest') => Some (JArray vs, rest')
          | None => None
          end
      | None =>
      match s with
      | String """"%char _ =>
          match parse_qtext s with
          | Some (str, rest) => Some (JString str, rest)
          | None => None
          end
      | _ =>
          match expect "true" s with
          | Some rest => Some (JBool true, rest)
          | None =>
          match expect "false" s with
          | Some rest => Some (JBool false, rest)
          | None =>
          match expect "null" s with
          | Some rest => Some (JNull, rest)
          | None =>
          match parse_number s with
          | Some (z, rest) => Some (JNum z, rest)
          | None => None
          end end end end
      end
      end
      end
  end.

Definition parse_json (s : string) : option jvalue :=
  match parse_jvalue (S (String.length s)) s with
  | Some (v, _) => Some v
  | None => None
  end.

(* ------------------------------------------------------------------ *)
(** * Small [jvalue] accessors *)

Definition jfield (fields : list (string * jvalue)) (key : string) : option jvalue :=
  (fix go (fs : list (string * jvalue)) : option jvalue :=
     match fs with
     | [] => None
     | (k, v) :: rest => if string_dec k key then Some v else go rest
     end) fields.

Definition jwhat (fields : list (string * jvalue)) : option string :=
  match jfield fields "what" with
  | Some (JString w) => Some w
  | _ => None
  end.

Definition jname (fields : list (string * jvalue)) : option string :=
  match jfield fields "name" with
  | Some (JString w) => Some w
  | _ => None
  end.

(* ------------------------------------------------------------------ *)
(** * Reading a [Z] literal back out of its [Z0]/[Zpos]/[Zneg] +
    [XI]/[XO]/[XH] constructor encoding *)

Fixpoint positive_of_json (fuel : nat) (j : jvalue) : option positive :=
  match fuel with
  | O => None
  | S fuel' =>
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "args" with
      | Some "expr:constructor", Some "XH", Some (JArray []) => Some xH
      | Some "expr:constructor", Some "XO", Some (JArray [p]) =>
          match positive_of_json fuel' p with
          | Some p' => Some (xO p')
          | None => None
          end
      | Some "expr:constructor", Some "XI", Some (JArray [p]) =>
          match positive_of_json fuel' p with
          | Some p' => Some (xI p')
          | None => None
          end
      | _, _, _ => None
      end
  | _ => None
  end
  end.

Definition z_of_json (fuel : nat) (j : jvalue) : option Z :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "args" with
      | Some "expr:constructor", Some "Z0", Some (JArray []) => Some Z0
      | Some "expr:constructor", Some "Zpos", Some (JArray [p]) =>
          match positive_of_json fuel p with
          | Some p' => Some (Zpos p')
          | None => None
          end
      | Some "expr:constructor", Some "Zneg", Some (JArray [p]) =>
          match positive_of_json fuel p with
          | Some p' => Some (Zneg p')
          | None => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(** A Coquelicot-adjacent [R] literal always extracts as [iZR] applied
    to a [Z] numeral (confirmed directly against the real [quad]
    probe, `coq/RealIR.v`'s own header) -- [float_of_Z] turns that
    numeral directly into the [PrimFloat.float] [RFLit] needs, via the
    same exact [spec_float] construction `coq/RealIR.v`'s probe already
    confirmed normalizes correctly ([SF2Prim]'s own job, not re-done
    here). Exact as long as [z] actually fits a double's 53-bit
    mantissa -- the same honestly-documented limitation this project
    already accepts for [Z] extracting to a native (not arbitrary-
    precision) [int] (`docs/roadmap.md`); not reconstructing it from
    nested [Zpos]/[XI]/[XO]/[XH] the way [RZLit]'s own [Z] literals are
    confirmed-exact for is a parsing-time convenience, not a new
    correctness claim -- this whole file, per its own header, is
    checked by running it on real JSON, not by a soundness proof. *)
Definition float_of_Z (z : Z) : PrimFloat.float :=
  match z with
  | Z0 => 0%float
  | Zpos p => SF2Prim (S754_finite false p 0)
  | Zneg p => SF2Prim (S754_finite true p 0)
  end.

(* ------------------------------------------------------------------ *)
(** * [jvalue] -> [real_expr]

    [self] names the enclosing [fixgroup:item] (if any): a real,
    self-recursive call extracts as an ordinary [expr:apply] whose
    [func] is an [expr:global] naming *itself* (confirmed directly --
    not an [expr:rel], since the function is not a local binder from
    the body's own point of view), recognized here as [RSelf] only
    when that name matches [self]. *)
Definition is_rel_named (bodyj : jvalue) (x : string) : bool :=
  match bodyj with
  | JObject fs =>
      match jwhat fs, jname fs with
      | Some "expr:rel", Some y => if string_dec x y then true else false
      | _, _ => false
      end
  | _ => false
  end.

Fixpoint real_expr_of_json (self : option var) (siblings : list var) (fuel : nat) (j : jvalue) {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  match j with
  | JObject fs =>
      match jwhat fs with
      | Some "expr:rel" =>
          match jname fs with
          | Some x => Some (RRel x)
          | None => None
          end
      | Some "expr:global" =>
          None (* a bare intrinsic reference with no arguments is not
                  a recognized real_expr shape on its own -- see this
                  file's header on eta-reduced definitions *)
      | Some "expr:constructor" =>
          match z_of_json fuel' j with
          | Some z => Some (RZLit z)
          | None =>
          match jname fs, jfield fs "args" with
          | Some "True", Some (JArray []) => Some (RBoolLit true)
          | Some "False", Some (JArray []) => Some (RBoolLit false)
          | Some "Nil", Some (JArray []) => Some RNil
          | Some "Cons", Some (JArray [h; t]) =>
              match real_expr_of_json self siblings fuel' h, real_expr_of_json self siblings fuel' t with
              | Some h', Some t' => Some (RCons h' t')
              | _, _ => None
              end
          | Some "Pair", Some (JArray [a; b]) =>
              match real_expr_of_json self siblings fuel' a, real_expr_of_json self siblings fuel' b with
              | Some a', Some b' => Some (RPair a' b')
              | _, _ => None
              end
          | _, Some (JArray [a; b; c]) =>
              (* a 3-argument record constructor, any name -- RRecord3 *)
              match real_expr_of_json self siblings fuel' a, real_expr_of_json self siblings fuel' b,
                    real_expr_of_json self siblings fuel' c with
              | Some a', Some b', Some c' => Some (RRecord3 a' b' c')
              | _, _, _ => None
              end
          | _, _ => None
          end
          end
      | Some "expr:apply" =>
          match jfield fs "func", jfield fs "args" with
          | Some (JObject ffs), Some (JArray args) =>
              match jwhat ffs, jname ffs with
              | Some "expr:global", Some fname =>
                  match self with
                  | Some sname =>
                      if string_dec fname sname then
                        match args with
                        | [a] =>
                            match real_expr_of_json self siblings fuel' a with
                            | Some a' => Some (RSelf a')
                            | None => None
                            end
                        | _ => None
                        end
                      else real_call_or_app self siblings fuel' fname args
                  | None => real_call_or_app self siblings fuel' fname args
                  end
              | _, _ => None
              end
          | _, _ => None
          end
      | Some "expr:case" =>
          match jfield fs "expr", jfield fs "cases" with
          | Some scrutinee_j, Some (JArray cases) =>
              match real_expr_of_json self siblings fuel' scrutinee_j with
              | Some scrutinee =>
                  real_case_of_json self siblings fuel' scrutinee cases
              | None => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | _ => None
  end
  end

(** Dispatch an [expr:apply] whose [func] is a plain [expr:global] and
    isn't [self]: a call to a *sibling* in the enclosing N-way
    mutually-recursive fixgroup (recognized as [RCall], by membership
    in [siblings] -- the whole group's own declared names, known to
    the caller before any member's body is parsed, since [coqc]'s own
    [decl:fixgroup] lists every member up front) takes priority over
    an ordinary intrinsic call, the same way a [self]-call already
    does. *)
with real_call_or_app (self : option var) (siblings : list var) (fuel : nat) (fname : string) (args : list jvalue)
    {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  if List.existsb (fun s => if string_dec fname s then true else false) siblings then
    match args with
    | [a] =>
        match real_expr_of_json self siblings fuel' a with
        | Some a' => Some (RCall fname a')
        | None => None
        end
    | _ => None
    end
  else real_app_of_json self siblings fuel' fname args
  end

(** Dispatch an [expr:apply] whose [func] is a plain [expr:global] --
    an intrinsic call ([RApp1]/[RApp2]), arity read off [args]'s own
    length, never guessed. *)
with real_app_of_json (self : option var) (siblings : list var) (fuel : nat) (fname : string) (args : list jvalue)
    {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  match args with
  | [a] =>
      if string_dec fname "iZR" then
        match z_of_json fuel' a with
        | Some z => Some (RFLit (float_of_Z z))
        | None => None
        end
      else
        match real_expr_of_json self siblings fuel' a with
        | Some a' => Some (RApp1 fname a')
        | None => None
        end
  | [a; b] =>
      match real_expr_of_json self siblings fuel' a, real_expr_of_json self siblings fuel' b with
      | Some a', Some b' => Some (RApp2 fname a' b')
      | _, _ => None
      end
  | _ => None
  end
  end

(** Dispatch an [expr:case]'s [cases] list: a 2-way [True]/[False]
    dispatch is [RIfBool]; a 2-way [Inl]/[Inr] dispatch (each binding
    exactly one name) is [RCase]; a single-case [pat:constructor] that
    binds exactly one non-wildcard name among 2 or 3 fields (the rest
    named ["_"], confirmed directly as the real shape a record field
    projection extracts to) is [RProj1]/[RProj2]/[RProj3_1]/
    [RProj3_2]/[RProj3_3]; a single-case, 2-name [Cons]/[Nil] pair is
    [RListMatch]. *)
with real_case_of_json (self : option var) (siblings : list var) (fuel : nat) (scrutinee : real_expr) (cases : list jvalue)
    {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  match cases with
  | [c1] =>
      match c1 with
      | JObject c1fs =>
          match jfield c1fs "pat", jfield c1fs "body" with
          | Some (JObject patfs), Some bodyj =>
              match jname patfs, jfield patfs "argnames" with
              | Some _, Some (JArray [JString "_"; JString x]) =>
                  (* 2-field record, want 2nd *)
                  if is_rel_named bodyj x
                  then Some (RProj2 scrutinee) else None
              | Some _, Some (JArray [JString x; JString "_"]) =>
                  if is_rel_named bodyj x
                  then Some (RProj1 scrutinee) else None
              | Some _, Some (JArray [JString x; JString "_"; JString "_"]) =>
                  if is_rel_named bodyj x then Some (RProj3_1 scrutinee) else None
              | Some _, Some (JArray [JString "_"; JString x; JString "_"]) =>
                  if is_rel_named bodyj x then Some (RProj3_2 scrutinee) else None
              | Some _, Some (JArray [JString "_"; JString "_"; JString x]) =>
                  if is_rel_named bodyj x then Some (RProj3_3 scrutinee) else None
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | [c1; c2] =>
      match c1, c2 with
      | JObject c1fs, JObject c2fs =>
          match jfield c1fs "pat", jfield c1fs "body", jfield c2fs "pat", jfield c2fs "body" with
          | Some (JObject p1), Some b1, Some (JObject p2), Some b2 =>
              match jname p1, jfield p1 "argnames", jname p2, jfield p2 "argnames" with
              | Some "True", Some (JArray []), Some "False", Some (JArray []) =>
                  match real_expr_of_json self siblings fuel' b1, real_expr_of_json self siblings fuel' b2 with
                  | Some t, Some e => Some (RIfBool scrutinee t e)
                  | _, _ => None
                  end
              | Some "Inl", Some (JArray [JString x1]), Some "Inr", Some (JArray [JString x2]) =>
                  match real_expr_of_json self siblings fuel' b1, real_expr_of_json self siblings fuel' b2 with
                  | Some c1', Some c2' => Some (RCase scrutinee x1 c1' x2 c2')
                  | _, _ => None
                  end
              | Some "Nil", Some (JArray []), Some "Cons", Some (JArray [JString h; JString t]) =>
                  match real_expr_of_json self siblings fuel' b1, real_expr_of_json self siblings fuel' b2 with
                  | Some nilc, Some consc => Some (RListMatch scrutinee nilc h t consc)
                  | _, _ => None
                  end
              | Some "Cons", Some (JArray [JString h; JString t]), Some "Nil", Some (JArray []) =>
                  match real_expr_of_json self siblings fuel' b2, real_expr_of_json self siblings fuel' b1 with
                  | Some nilc, Some consc => Some (RListMatch scrutinee nilc h t consc)
                  | _, _ => None
                  end
              | _, _, _, _ => None
              end
          | _, _, _, _ => None
          end
      | _, _ => None
      end
  | _ => None
  end
  end.

(* ------------------------------------------------------------------ *)
(** * [jvalue] -> [real_decl] / [real_fix_decl], and finding a
    declaration by name inside a whole extracted module

    A real [coqc] extraction unit is a [module] wrapping a
    [declarations] array that also carries every transitively-needed
    standard-library declaration (confirmed directly, see this file's
    header and [RealIR.v]'s) -- so ingestion always means "parse the
    whole module, then find *this* declaration by name", never "parse
    just one declaration's own text". *)

Definition jstrings_of_json (xs : list jvalue) : option (list var) :=
  (fix go (xs0 : list jvalue) : option (list var) :=
     match xs0 with
     | [] => Some []
     | JString x :: rest =>
         match go rest with
         | Some r => Some (x :: r)
         | None => None
         end
     | _ => None
     end) xs.

Definition real_decl_of_json (fuel : nat) (argnames : list jvalue) (bodyj : jvalue) : option real_decl :=
  match jstrings_of_json argnames with
  | Some ns =>
      match real_expr_of_json None [] fuel bodyj with
      | Some body => Some (mk_real_decl ns body)
      | None => None
      end
  | None => None
  end.

(** A [decl:term] node, as it appears directly inside [declarations]. *)
Definition decl_term_of_json (fuel : nat) (j : jvalue) : option real_decl :=
  match j with
  | JObject fs =>
      match jwhat fs, jfield fs "value" with
      | Some "decl:term", Some (JObject vfs) =>
          match jwhat vfs, jfield vfs "argnames", jfield vfs "body" with
          | Some "expr:lambda", Some (JArray argnames), Some bodyj =>
              real_decl_of_json fuel argnames bodyj
          | _, _, _ => None
          end
      | _, _ => None
      end
  | _ => None
  end.

(** A [fixgroup:item] node, as it appears inside a [decl:fixgroup]'s
    own [fixlist] -- a single-argument self-recursive [Fixpoint]
    only, [self]-recognized exactly as before ([siblings := []]). For
    the general N-way case, see [decl_fixgroup_of_json] below. *)
Definition decl_fixgroup_item_of_json (fuel : nat) (j : jvalue) : option real_fix_decl :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "value" with
      | Some "fixgroup:item", Some fname, Some (JObject vfs) =>
          match jwhat vfs, jfield vfs "argnames", jfield vfs "body" with
          | Some "expr:lambda", Some (JArray [JString param]), Some bodyj =>
              match real_expr_of_json (Some fname) [] fuel bodyj with
              | Some body => Some (mk_real_fix_decl fname param body)
              | None => None
              end
          | _, _, _ => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(** A single [fixgroup:item] node, parsed as *one member* of a general
    N-way group: [self := None] ([RealIR.v]'s [real_fix_group_decl]
    deliberately never produces [RSelf] -- see its own comment), and
    [siblings] is the *whole* group's names, known up front from
    [names] (every [fixgroup:item] in a [decl:fixgroup]'s [fixlist]
    is visible before any one member's own body is parsed, so this
    is never a chicken-and-egg problem). *)
Definition fixgroup_item_of_json (siblings : list var) (fuel : nat) (j : jvalue)
    : option (var * var * real_expr) :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "value" with
      | Some "fixgroup:item", Some fname, Some (JObject vfs) =>
          match jwhat vfs, jfield vfs "argnames", jfield vfs "body" with
          | Some "expr:lambda", Some (JArray [JString param]), Some bodyj =>
              match real_expr_of_json None siblings fuel bodyj with
              | Some body => Some (fname, param, body)
              | None => None
              end
          | _, _, _ => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(** A [decl:fixgroup] node, as it appears directly inside
    [declarations]: every member's own name is read off [fixlist]
    first ([jname], not re-derived), *then* each member's body is
    parsed against that whole list as [siblings] -- confirmed
    directly against a real extracted [Fixpoint is_even (n : nat) :
    bool := ... with is_odd (n : nat) : bool := ...]: [fixlist] is a
    flat [JArray] of [fixgroup:item]s, group order preserved, no
    separate "names" field to read instead. *)
Definition decl_fixgroup_of_json (fuel : nat) (j : jvalue) : option real_fix_group_decl :=
  match j with
  | JObject fs =>
      match jwhat fs, jfield fs "fixlist" with
      | Some "decl:fixgroup", Some (JArray items) =>
          match
            (fix names_of (its : list jvalue) : option (list var) :=
               match its with
               | [] => Some []
               | JObject ifs :: rest =>
                   match jname ifs with
                   | Some n => match names_of rest with
                               | Some ns => Some (n :: ns)
                               | None => None
                               end
                   | None => None
                   end
               | _ :: _ => None
               end) items
          with
          | Some siblings =>
              match
                (fix go (its : list jvalue) : option (list (var * var * real_expr)) :=
                   match its with
                   | [] => Some []
                   | it :: rest =>
                       match fixgroup_item_of_json siblings fuel it, go rest with
                       | Some m, Some ms => Some (m :: ms)
                       | _, _ => None
                       end
                   end) items
              with
              | Some fns => Some (mk_real_fix_group_decl fns)
              | None => None
              end
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.

(** Search a module's [declarations] array for the node named
    [target] -- either a top-level [decl:term], or a [fixgroup:item]
    buried inside some [decl:fixgroup]'s [fixlist] -- returning that
    node itself (not yet interpreted: the caller picks
    [decl_term_of_json] or [decl_fixgroup_item_of_json] depending on
    which shape it expects). *)
Definition find_decl_by_name (decls : list jvalue) (target : string) : option jvalue :=
  (fix go (ds : list jvalue) : option jvalue :=
     match ds with
     | [] => None
     | JObject fs :: rest =>
         match jwhat fs with
         | Some "decl:term" =>
             match jname fs with
             | Some n => if string_dec n target then Some (JObject fs) else go rest
             | None => go rest
             end
         | Some "decl:fixgroup" =>
             match jfield fs "fixlist" with
             | Some (JArray items) =>
                 match
                   (fix find_item (its : list jvalue) : option jvalue :=
                      match its with
                      | [] => None
                      | JObject ifs :: rest' =>
                          match jname ifs with
                          | Some n => if string_dec n target then Some (JObject ifs) else find_item rest'
                          | None => find_item rest'
                          end
                      | _ :: rest' => find_item rest'
                      end) items
                 with
                 | Some it => Some it
                 | None => go rest
                 end
             | _ => go rest
             end
         | _ => go rest
         end
     | _ :: rest => go rest
     end) decls.

(** Like [find_decl_by_name], but for the N-way case: returns the
    *whole* [decl:fixgroup] node containing a member named [target],
    not that member's own [fixgroup:item] -- [decl_fixgroup_of_json]
    needs every member, not just the one the caller happens to ask
    for by name, to resolve any member's calls to any other. A real
    [decl:fixgroup]'s own ["name"] field is [null] for a genuine
    multi-member group (confirmed directly against the [is_even]/
    [is_odd] probe), so group identity is only ever "which members'
    names does it declare", never a name of its own. *)
Definition find_fixgroup_by_member_name (decls : list jvalue) (target : string) : option jvalue :=
  (fix go (ds : list jvalue) : option jvalue :=
     match ds with
     | [] => None
     | JObject fs :: rest =>
         match jwhat fs with
         | Some "decl:fixgroup" =>
             match jfield fs "fixlist" with
             | Some (JArray items) =>
                 if (fix any_named (its : list jvalue) : bool :=
                       match its with
                       | [] => false
                       | JObject ifs :: rest' =>
                           match jname ifs with
                           | Some n => if string_dec n target then true else any_named rest'
                           | None => any_named rest'
                           end
                       | _ :: rest' => any_named rest'
                       end) items
                 then Some (JObject fs)
                 else go rest
             | _ => go rest
             end
         | _ => go rest
         end
     | _ :: rest => go rest
     end) decls.

Definition module_declarations (s : string) : option (list jvalue) :=
  match parse_json s with
  | Some (JObject mfs) =>
      match jwhat mfs, jfield mfs "declarations" with
      | Some "module", Some (JArray decls) => Some decls
      | _, _ => None
      end
  | _ => None
  end.

(** The two top-level entry points: parse a whole real [coqc]
    [Extraction Language JSON] module ([s]) and pull out one
    non-recursive ([real_decl_of_module_json]) or self-recursive
    ([real_fix_decl_of_module_json]) declaration by name. *)
Definition real_decl_of_module_json (s target : string) : option real_decl :=
  match module_declarations s with
  | Some decls =>
      match find_decl_by_name decls target with
      | Some declj => decl_term_of_json (S (String.length s)) declj
      | None => None
      end
  | None => None
  end.

Definition real_fix_decl_of_module_json (s target : string) : option real_fix_decl :=
  match module_declarations s with
  | Some decls =>
      match find_decl_by_name decls target with
      | Some declj => decl_fixgroup_item_of_json (S (String.length s)) declj
      | None => None
      end
  | None => None
  end.

(** A third entry point, for a general N-way mutually-recursive
    [decl:fixgroup]: [target] names any *one* member (the caller's
    point of entry), but the result carries the *whole* group. *)
Definition real_fix_group_decl_of_module_json (s target : string) : option real_fix_group_decl :=
  match module_declarations s with
  | Some decls =>
      match find_fixgroup_by_member_name decls target with
      | Some declj => decl_fixgroup_of_json (S (String.length s)) declj
      | None => None
      end
  | None => None
  end.
