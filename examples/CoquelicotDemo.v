(** CoquelicotDemo.v

    Closes the loop [RealIR.v]'s own header opens for Coquelicot: a
    real, Coquelicot-proven definition, carried through [real_to_expr]
    and then this project's already-proven [Translate.v]/[Json.v]/
    [PyPrint.v] pipeline, to real, running Python -- the same shape
    [NaturalCoq.v] already does for the [Z]/[bool] fragment, now once
    for the new ["rplus"]/["rmult"] float fragment.

    [quad] below is not invented for this file: it is exactly what was
    typed into a throwaway [.v] file and run through [coqc] with
    [coq-coquelicot] installed (via the [coq-released] opam repo)
    during this session, to find out what a real Coquelicot-adjacent
    definition's extraction actually looks like:

    [[
    From Coquelicot Require Import Coquelicot.
    Require Import Reals.
    Require Coq.extraction.Extraction.
    Open Scope R_scope.

    Definition quad (x : R) : R := x * x + 1.

    Lemma quad_is_derive : forall x, is_derive quad x (2 * x).
    Proof. intro x. unfold quad. auto_derive; auto. ring. Qed.

    Extraction Language JSON.
    Extraction "probe1_quad.json" quad.
    ]]

    The captured JSON's [quad] declaration, reproduced verbatim (only
    the irrelevant surrounding module/[rabst]/[rrepr]/... declarations
    -- [ClassicalDedekindReals]'s own internal cut machinery, never
    looked at by [RealIR.v]'s recognizer -- are elided):

    [[
    {
     "what": "decl:term", "name": "quad",
     "type": { "what": "type:arrow", "left": {...}, "right": {...} },
     "value": {
      "what": "expr:lambda", "argnames": ["x"],
      "body": {
       "what": "expr:apply",
       "func": { "what": "expr:global", "name": "rplus" },
       "args": [
        { "what": "expr:apply",
          "func": { "what": "expr:global", "name": "rmult" },
          "args": [ {"what":"expr:rel","name":"x"}, {"what":"expr:rel","name":"x"} ] },
        { "what": "expr:apply",
          "func": { "what": "expr:global", "name": "iZR" },
          "args": [ {"what":"expr:constructor","name":"Zpos",
                     "args":[{"what":"expr:constructor","name":"XH","args":[]}]} ] }
       ]
      }
     }
    }
    ]]

    [quad_is_derive] itself does not appear anywhere in this JSON --
    Coquelicot's calculus lemmas are [Prop]-sorted and erase to
    nothing under this project's own erasure model (`docs/duality.md`),
    confirmed directly, not just argued.

    [quad_ir] below is that JSON tree, written as a [real_expr] term
    by hand (the textual-JSON-to-[real_expr] parser itself is a
    separate, later step -- see docs/roadmap.md and [RealJson.v]):
    the outer [expr:apply]/[expr:global "rplus"] becomes [RApp2
    "rplus"], its first argument's [expr:apply]/[expr:global "rmult"]
    becomes [RApp2 "rmult" (RRel "x") (RRel "x")], and the
    [iZR (Zpos XH)] literal -- [1] -- becomes [RFLit 1] directly: see
    [RealIR.v]'s header for why this fragment's literals are hand-given
    as the already-known float value rather than reconstructed from
    the nested [Zpos]/[XH] constructors the way [RZLit]'s [Z] literals
    are (a job for the future JSON parser, not this file). *)

From Coq Require Import ZArith String List Bool Lia.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Require Import RealIR.
Require Import RealJson.
Open Scope string_scope.
Open Scope float_scope.

Definition quad_ir : real_expr :=
  RApp2 "rplus" (RApp2 "rmult" (RRel "x") (RRel "x")) (RFLit 1).

(** The new fragment's [real_eval] is deliberately *not* a model of
    Coq's classical [R] (see [RealIR.v]'s header for why that is not
    available) -- it computes directly with [PrimFloat] arithmetic.
    So the "matches the real definition" check here is a concrete
    numeric instance, not a universally-quantified theorem over every
    real [x] the way [clamp_nonneg]'s own check is over every [Z]:
    for the input [3], [quad 3 = 10] exactly (no rounding -- [3*3+1]
    is exact in binary64), checked by direct computation. *)
Example quad_ir_matches_expected_value :
  real_eval [("x", VFloat 3)] quad_ir = Some (VFloat 10).
Proof. reflexivity. Qed.

(** Translating into our existing, already-proven [expr] subset: *)
Definition quad_expr : expr :=
  match real_to_expr quad_ir with
  | Some e => e
  | None => EFConst 0 (* unreachable: quad_ir is in the recognized fragment *)
  end.

Example quad_ir_translates :
  real_to_expr quad_ir = Some quad_expr.
Proof. reflexivity. Qed.

(** [RealIR.v]'s preservation theorem then carries the match proved
    above all the way down to [eval] -- exactly [NaturalCoq.v]'s own
    pattern, just landing on [VFloat] instead of [VZ]: *)
Example quad_expr_matches_expected_value :
  eval 10 [("x", VFloat 3)] quad_expr = Some (VFloat 10).
Proof.
  rewrite (real_to_expr_preserves_semantics quad_ir quad_expr
             quad_ir_translates 10 [("x", VFloat 3)] ltac:(simpl; lia)).
  apply quad_ir_matches_expected_value.
Qed.

Theorem quad_idents_valid :
  expr_idents_valid is_valid_ident quad_expr = true.
Proof. reflexivity. Qed.

Compute print_expr quad_expr.

Corollary quad_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate quad_expr)
      = option_map value_to_pyvalue (eval fuel rho quad_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The real, running Python -- from a real Coquelicot-adjacent
    [Definition], through Coq's own extraction JSON shape (modeled by
    hand here; parsed from the real JSON *text* below instead), through
    every already-proven stage this project has: [translate], [Json.v]'s
    codec, and [PyPrint.v]. *)
Compute py_function "quad" ["x"] (translate quad_expr).

(* ------------------------------------------------------------------ *)
(** * Parsed from the real JSON text, not hand-built

    Everything above builds [quad_ir] by hand, matching the captured
    JSON only by eye (the same way every [NaturalCoq.v] example does
    for the [Z]/[bool] fragment). [RealJson.v]'s own parser was never
    actually exercised on a real captured module in any committed
    example -- confirmed by checking: no [examples/]/[test/] file
    calls [real_decl_of_module_json] anywhere. [quad_decl_json] below
    closes that gap for real, for this fragment: the literal bytes
    [coqc] emitted for [quad]'s own [decl:term] (a single declaration,
    not the whole module -- see the note below on why), run through
    [RealJson.v]'s [real_decl_of_module_json], producing *the same*
    [real_decl] [quad_ir] above was hand-built to match, checked by
    [vm_compute], not asserted.

    Parsing this needed one small addition to [RealJson.v] itself,
    landed alongside this example: a Coquelicot-adjacent [R] literal
    extracts as [expr:apply]/[expr:global "iZR"] applied to a nested
    [Z] numeral (confirmed directly, in the JSON below), which
    [RealJson.v]'s already-existing, fully generic [expr:apply]/
    [expr:global] dispatch would otherwise turn into an *unrecognized*
    [RApp1 "iZR" (RZLit 1)] (["iZR"] was never a name [RealIR.v]'s
    [real_eval]/[real_to_expr] know, only [RFLit] -- see [RealIR.v]'s
    own header for why this fragment's literals are a float, not a
    [Z], from the start). [RealJson.v]'s new [float_of_Z] turns the
    parsed [Z] numeral directly into that [RFLit] instead.

    Why one declaration, not the whole captured module: the full
    [probe1_quad.json] module (~350KB, dominated by
    [ClassicalDedekindReals]'s own internal cut representation --
    [RealBridge.v]'s header already explains why) makes [vm_compute]
    segfault on this machine, confirmed directly -- almost certainly a
    stack-depth issue in how [vm_compute] represents a string that
    large as nested [String] constructors, not a bug in this file's
    own parsing logic (the *same* parser, fed just [quad]'s own
    [decl:term] sub-object -- still real, unedited JSON bytes, just
    not the surrounding 349KB this recognizer was never going to look
    at anyway -- works immediately, as the rest of this section shows).
    Tracked as a real, open performance question (`RealJson.v`'s own
    header already flags performance as a known concern, if for a
    different cause -- [Extract.v]'s realizers speed up the *extracted
    OCaml*, not in-Coq [vm_compute]), not silently worked around. *)

Definition quad_decl_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""quad"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rplus""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rmult""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""x""}]}, {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""iZR""}, ""args"": [{""what"": ""expr:constructor"", ""name"": ""Zpos"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XH"", ""args"": []}]}]}]}}}]}".

Definition quad_decl_parsed : option real_decl := real_decl_of_module_json quad_decl_json "quad".

Example quad_decl_parsed_matches_hand_built :
  quad_decl_parsed = Some {| rd_argnames := ["x"]; rd_body := quad_ir |}.
Proof. vm_compute. reflexivity. Qed.

Definition quad_expr_from_json : expr :=
  match quad_decl_parsed with
  | Some rd =>
      match real_to_expr rd.(rd_body) with
      | Some e => e
      | None => EFConst 0%float
      end
  | None => EFConst 0%float
  end.

(** Parsed from text, translated, evaluated, printed -- the same
    concrete-instance check as [quad_expr_matches_expected_value]
    above, now starting from real JSON bytes instead of a hand-built
    [real_expr]. *)
Example quad_expr_from_json_matches_expected_value :
  eval 10 [("x", VFloat 3)] quad_expr_from_json = Some (VFloat 10).
Proof. vm_compute. reflexivity. Qed.

Compute py_function "quad" (match quad_decl_parsed with Some rd => rd.(rd_argnames) | None => [] end)
  (translate quad_expr_from_json).
