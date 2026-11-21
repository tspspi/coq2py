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
    segfault on this machine at the shell's default stack size.
    Root-caused, not just worked around (`docs/roadmap.md` has the
    full account): confirmed directly to be exactly a stack-size
    limit, not a bug here or in [vm_compute] itself -- raising
    [ulimit -s] to 128MB is already enough for the identical [coqc]
    invocation, on the identical 350KB string, to stop segfaulting
    (it was still running correctly, not crashed, when a 60-second cap
    on that check ran out); given enough stack, it does finish
    correctly, in about 90 seconds -- consistent with this project's
    own already-documented [vm_compute] string-handling cost at this
    scale (`RealJson.v`'s header's 22KB/45s figure, scaled up). Using
    the per-declaration JSON object here stays the right call anyway:
    this recognizer was never going to look at the surrounding 349KB
    of cut-representation bulk either way, and a routine build
    shouldn't need a raised [ulimit] and a 90-second step for a single
    example. *)

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

(* ------------------------------------------------------------------ *)
(** * "ropp", and why it needed a real EFOpp, not a workaround

    A Coquelicot-adjacent [Ropp] (unary negation over [R]) extracts
    the same way [Rplus]/[Rmult] do -- an [expr:apply]/[expr:global
    "ropp"] call -- recognized by [RealIR.v]'s [RApp1]. Translating it
    as [EFSub (EFConst 0) e] (reusing already-existing constructors,
    no new [Lang.v] addition) looked tempting, but is *wrong* for one
    concrete input: IEEE-754 signed zero means [0.0 - 0.0 = +0.0]
    while the true negation, [PrimFloat.opp 0.0], is [-0.0] -- a
    different bit pattern, confirmed directly. [EFOpp] (and its
    [PyLang.v] mirror, [PFOpp]) calls [PrimFloat.opp] directly instead,
    the same way every other float operation in this project calls
    its own primitive directly, so this is exact for every input,
    zero included -- not an approximation with a known edge case. *)
Example ropp_negates_three :
  eval 5 [] (EFOpp (EFConst 3)) = Some (VFloat (-3)).
Proof. reflexivity. Qed.

(** The case a [EFSub (EFConst 0) e]-style workaround would have
    gotten wrong: negating zero must give signed [-0.0], not [+0.0]. *)
Example ropp_negates_zero_with_correct_sign :
  eval 5 [] (EFOpp (EFConst 0)) = Some (VFloat (-0)).
Proof. reflexivity. Qed.

Definition ropp_ir : real_expr := RApp1 "ropp" (RRel "x").

Example ropp_ir_translates :
  real_to_expr ropp_ir = Some (EFOpp (EVar "x")).
Proof. reflexivity. Qed.

Example ropp_ir_matches_expected_value :
  real_eval [("x", VFloat 3)] ropp_ir = Some (VFloat (-3)).
Proof. reflexivity. Qed.

Compute py_function "negate" ["x"] (translate (EFOpp (EVar "x"))).

(* ------------------------------------------------------------------ *)
(** * "rminus"/"rdiv"/"ropp" together, ingested from real JSON text

    One more real probe, closing the loop for the rest of the float
    fragment the same way [quad_decl_json] did for ["rplus"]/
    ["rmult"]: a genuine Coquelicot-adjacent definition exercising
    subtraction, division, *and* negation together, actually run
    through [coqc] with [coq-coquelicot] installed, not assumed to
    extract the way [quad]'s did:

    [[
    Definition combo (x y : R) : R := (x - y) / (- y).

    Lemma combo_is_derive : forall x y, y <> 0 ->
      is_derive (fun x0 => combo x0 y) x (/ (- y)).
    Proof. intros x y Hy. unfold combo. auto_derive; auto. Admitted.

    Extraction Language JSON.
    Extraction "probe2_combo.json" combo.
    ]]

    ([combo_is_derive] is deliberately left [Admitted] in the *probe*
    file this JSON came from -- that file is a throwaway scratch
    artifact used only to run [coqc]'s extraction, never part of this
    project's own proof obligations, and per this project's own
    erasure model it couldn't change [combo]'s own extracted JSON
    either way.) The real captured JSON confirms exactly the shape
    [RealIR.v]'s header already predicted by analogy with ["rplus"]/
    ["rmult"], now actually checked rather than assumed: [combo]'s own
    two-argument [expr:lambda] body is [rdiv (rminus x y) (ropp y)] --
    [RApp2 "rdiv"]/[RApp2 "rminus"]/[RApp1 "ropp"], exactly the shapes
    [RealIR.v]/[RealJson.v] already recognize, no further parser
    changes needed. *)
Definition combo_decl_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""combo"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rdiv""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rminus""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""y""}]}, {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""ropp""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""y""}]}]}}}]}".

Definition combo_decl_parsed : option real_decl := real_decl_of_module_json combo_decl_json "combo".

Example combo_decl_parsed_shape :
  combo_decl_parsed
  = Some {| rd_argnames := ["x"; "y"];
            rd_body := RApp2 "rdiv" (RApp2 "rminus" (RRel "x") (RRel "y"))
                               (RApp1 "ropp" (RRel "y")) |}.
Proof. vm_compute. reflexivity. Qed.

Definition combo_expr : expr :=
  match combo_decl_parsed with
  | Some rd =>
      match real_to_expr rd.(rd_body) with
      | Some e => e
      | None => EFConst 0%float
      end
  | None => EFConst 0%float
  end.

(** [(10 - 4) / (-4) = -1.5] exactly -- no rounding to worry about for
    this concrete instance, the same honest scoping [quad]'s own
    concrete-instance check above already uses. *)
Example combo_expr_matches_expected_value :
  eval 10 [("x", VFloat 10); ("y", VFloat 4)] combo_expr = Some (VFloat (-1.5)).
Proof. vm_compute. reflexivity. Qed.

Compute py_function "combo" (match combo_decl_parsed with Some rd => rd.(rd_argnames) | None => [] end)
  (translate combo_expr).

(* ------------------------------------------------------------------ *)
(** * "rabs", and why it needed a real EFAbs too

    A fresh probe, run the same way [probe2_combo.json] was:

    [[
    Definition absdiff (x y : R) : R := Rabs (x - y).

    Extraction Language JSON.
    Extraction "probe3_absdiff.json" absdiff.
    ]]

    confirms [Rabs] extracts the same way [Ropp] does: a plain unary
    [expr:apply]/[expr:global "rabs"] call, despite [Rabs]'s own
    Gallina definition being a decidability case split
    ([Rcase_abs]/[total_order_T]) rather than anything resembling a
    single primitive -- this project's extraction-shape bet already
    made for ["ropp"] holds for ["rabs"] too, confirmed rather than
    assumed by analogy.

    The same signed-zero trap ["ropp"] had applies here: an
    [EIf]-based workaround ([EIf (EFLt e (EFConst 0)) (EFOpp e) e])
    is *wrong* at [e = -0.0], because [-0.0 < 0.0] is [false] under
    IEEE-754, so the [else] branch returns [-0.0] unchanged, while
    [PrimFloat.abs (-0.0) = 0.0] -- a different, incorrect result. So
    ["rabs"] translates to a real, dedicated [EFAbs] (added to
    [Lang.v] alongside [EFOpp]), calling [PrimFloat.abs] directly, the
    same move as ["ropp"]/[EFOpp]. *)
Example rabs_abs_of_negative_three :
  eval 5 [] (EFAbs (EFConst (-3))) = Some (VFloat 3).
Proof. reflexivity. Qed.

(** The case an [EIf]-based workaround would have gotten wrong:
    [abs] of signed [-0.0] must give [+0.0], not [-0.0] unchanged. *)
Example rabs_abs_of_negative_zero_is_positive_zero :
  eval 5 [] (EFAbs (EFConst (-0))) = Some (VFloat 0).
Proof. reflexivity. Qed.

Definition rabs_ir : real_expr := RApp1 "rabs" (RRel "x").

Example rabs_ir_translates :
  real_to_expr rabs_ir = Some (EFAbs (EVar "x")).
Proof. reflexivity. Qed.

Example rabs_ir_matches_expected_value :
  real_eval [("x", VFloat (-3))] rabs_ir = Some (VFloat 3).
Proof. reflexivity. Qed.

Compute py_function "absval" ["x"] (translate (EFAbs (EVar "x"))).

(** [absdiff]'s own real captured JSON, [rabs (rminus x y)] -- parsed
    from text, not hand-built, the same way [quad_decl_json]/
    [combo_decl_json] were: *)
Definition absdiff_decl_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""absdiff"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rabs""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rminus""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""y""}]}]}}}]}".

Definition absdiff_decl_parsed : option real_decl := real_decl_of_module_json absdiff_decl_json "absdiff".

Example absdiff_decl_parsed_shape :
  absdiff_decl_parsed
  = Some {| rd_argnames := ["x"; "y"];
            rd_body := RApp1 "rabs" (RApp2 "rminus" (RRel "x") (RRel "y")) |}.
Proof. vm_compute. reflexivity. Qed.

Definition absdiff_expr : expr :=
  match absdiff_decl_parsed with
  | Some rd =>
      match real_to_expr rd.(rd_body) with
      | Some e => e
      | None => EFConst 0%float
      end
  | None => EFConst 0%float
  end.

(** [|4 - 10| = 6] exactly -- no rounding, the same honest
    concrete-instance scoping used throughout this file. *)
Example absdiff_expr_matches_expected_value :
  eval 10 [("x", VFloat 4); ("y", VFloat 10)] absdiff_expr = Some (VFloat 6).
Proof. vm_compute. reflexivity. Qed.

Compute py_function "absdiff" (match absdiff_decl_parsed with Some rd => rd.(rd_argnames) | None => [] end)
  (translate absdiff_expr).

(* ------------------------------------------------------------------ *)
(** * "sqrt", the one float op with no workaround to reject at all

    A fresh probe, the same way [probe3_absdiff.json] was:

    [[
    Definition hyp_len (x y : R) : R := sqrt (x * x + y * y).

    Extraction Language JSON.
    Extraction "probe_sqrt.json" hyp_len.
    ]]

    confirms [sqrt] (Coq's own [Reals.R_sqrt.sqrt]) extracts the same
    way [ropp]/[rabs] do: a plain unary [expr:apply]/[expr:global
    "sqrt"] call, despite its own Gallina definition going through
    [Rsqrt_exists] and a classical completeness argument, not
    anything resembling a single primitive.

    Unlike ["ropp"]/["rabs"], there is not even an *almost*-right
    workaround to reject here: nothing already in [expr] -- built
    only from [+]/[-]/[*]/[/] -- can compute a square root at all, so
    a dedicated [EFSqrt] (calling [PrimFloat.sqrt] directly) is not an
    exactness refinement, it is the only way to support this
    operation. Printing it needs no new [Lang.v]/[Translate.v]/
    [PyRename.v] feature once [EFSqrt] exists, but a real printing
    choice: Python's [math.sqrt] needs [math] imported, and
    [py_function] emits a bare [def] with no header to put an import
    in, so [PyPrint.v] renders it as the self-contained *expression*
    [__import__("math").sqrt(...)] -- confirmed directly to compute
    the exact same bits as [math.sqrt] (sign of zero included;
    [x ** 0.5], the importless alternative, was confirmed *wrong* for
    [x = -0.0]: it gives [+0.0], not [-0.0]). *)
Example sqrt_hyp_len_three_four_five :
  eval 10 [] (EFSqrt (EFAdd (EFMul (EFConst 3) (EFConst 3)) (EFMul (EFConst 4) (EFConst 4)))) = Some (VFloat 5).
Proof. reflexivity. Qed.

Definition sqrt_ir : real_expr := RApp1 "sqrt" (RRel "x").

Example sqrt_ir_translates :
  real_to_expr sqrt_ir = Some (EFSqrt (EVar "x")).
Proof. reflexivity. Qed.

Compute py_function "root" ["x"] (translate (EFSqrt (EVar "x"))).

(** [hyp_len]'s own real captured JSON, [sqrt (rplus (rmult x x) (rmult
    y y))] -- parsed from text, not hand-built. [[3; 4; 5]] is a real
    Pythagorean triple, so [hyp_len 3 4 = 5] exactly, no rounding. *)
Definition hyp_len_decl_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""hyp_len"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""sqrt""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rplus""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rmult""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""x""}]}, {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rmult""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""y""}, {""what"": ""expr:rel"", ""name"": ""y""}]}]}]}}}]}".

Definition hyp_len_decl_parsed : option real_decl := real_decl_of_module_json hyp_len_decl_json "hyp_len".

Example hyp_len_decl_parsed_matches_hand_built :
  hyp_len_decl_parsed
  = Some {| rd_argnames := ["x"; "y"];
            rd_body := RApp1 "sqrt" (RApp2 "rplus" (RApp2 "rmult" (RRel "x") (RRel "x"))
                                            (RApp2 "rmult" (RRel "y") (RRel "y"))) |}.
Proof. vm_compute. reflexivity. Qed.

Definition hyp_len_expr : expr :=
  match hyp_len_decl_parsed with
  | Some rd =>
      match real_to_expr rd.(rd_body) with
      | Some e => e
      | None => EFConst 0%float
      end
  | None => EFConst 0%float
  end.

Example hyp_len_expr_matches_expected_value :
  eval 10 [("x", VFloat 3); ("y", VFloat 4)] hyp_len_expr = Some (VFloat 5).
Proof. vm_compute. reflexivity. Qed.

Compute py_function "hyp_len" (match hyp_len_decl_parsed with Some rd => rd.(rd_argnames) | None => [] end)
  (translate hyp_len_expr).


(* ------------------------------------------------------------------ *)
(** * "rinv"/"rmax"/"rmin": a reciprocal needing no new primitive, and
      two that need a Gallina-defined one since PrimFloat has none

    Three more probes, the same way the others were: [inv_sum (x y :
    R) := / (x + y)], [bigger_plus_one (x y : R) := Rmax x y + 1],
    [smaller_plus_one (x y : R) := Rmin x y + 1]. Confirmed directly:
    [/ (x + y)] extracts as [rinv (rplus x y)] (plain unary call, the
    same shape every other float op here has); [Rmax x y]/[Rmin x y]
    extract as plain binary [rmax]/[rmin] calls -- *not* eta-reduced
    the way a bare [Definition bigger (x y : R) : R := Rmax x y.]
    would be (confirmed directly: that exact definition extracts to
    a bare [expr:global "rmax"] with no [expr:lambda] at all, this
    file's header's own eta-reduction limitation; wrapping the call in
    [+ 1] avoids it here, the same way every worked example in this
    file needs a body that isn't point-free). *)
Definition inv_sum_ir : real_expr :=
  RApp1 "rinv" (RApp2 "rplus" (RRel "x") (RRel "y")).

Example inv_sum_ir_translates :
  real_to_expr inv_sum_ir = Some (EFDiv (EFConst 1) (EFAdd (EVar "x") (EVar "y"))).
Proof. reflexivity. Qed.

(** [1 / (3 + 1) = 0.25] exactly -- no rounding, a power-of-two
    denominator. *)
Example inv_sum_ir_matches_expected_value :
  real_eval [("x", VFloat 3); ("y", VFloat 1)] inv_sum_ir = Some (VFloat 0.25).
Proof. reflexivity. Qed.

Compute py_function "inv_sum" ["x"; "y"]
  (translate (EFDiv (EFConst 1) (EFAdd (EVar "x") (EVar "y")))).

Definition bigger_plus_one_ir : real_expr :=
  RApp2 "rplus" (RApp2 "rmax" (RRel "x") (RRel "y")) (RFLit 1).

Example bigger_plus_one_ir_translates :
  real_to_expr bigger_plus_one_ir = Some (EFAdd (EFMax (EVar "x") (EVar "y")) (EFConst 1)).
Proof. reflexivity. Qed.

(** [max(3, 5) + 1 = 6] exactly. *)
Example bigger_plus_one_ir_matches_expected_value :
  real_eval [("x", VFloat 3); ("y", VFloat 5)] bigger_plus_one_ir = Some (VFloat 6).
Proof. reflexivity. Qed.

Definition smaller_plus_one_ir : real_expr :=
  RApp2 "rplus" (RApp2 "rmin" (RRel "x") (RRel "y")) (RFLit 1).

Example smaller_plus_one_ir_translates :
  real_to_expr smaller_plus_one_ir = Some (EFAdd (EFMin (EVar "x") (EVar "y")) (EFConst 1)).
Proof. reflexivity. Qed.

(** [min(3, 5) + 1 = 4] exactly. *)
Example smaller_plus_one_ir_matches_expected_value :
  real_eval [("x", VFloat 3); ("y", VFloat 5)] smaller_plus_one_ir = Some (VFloat 4).
Proof. reflexivity. Qed.

Compute py_function "bigger_plus_one" ["x"; "y"]
  (translate (EFAdd (EFMax (EVar "x") (EVar "y")) (EFConst 1))).
Compute py_function "smaller_plus_one" ["x"; "y"]
  (translate (EFAdd (EFMin (EVar "x") (EVar "y")) (EFConst 1))).

(** Parsed from the real JSON text, not hand-built. *)
Definition inv_sum_module_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""inv_sum"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rinv""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rplus""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""y""}]}]}}}]}".

Definition inv_sum_decl_parsed : option real_decl :=
  real_decl_of_module_json inv_sum_module_json "inv_sum".

Example inv_sum_decl_parsed_matches_hand_built :
  inv_sum_decl_parsed = Some {| rd_argnames := ["x"; "y"]; rd_body := inv_sum_ir |}.
Proof. vm_compute. reflexivity. Qed.

Definition bigger_plus_one_module_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""bigger_plus_one"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rplus""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rmax""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""y""}]}, {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""iZR""}, ""args"": [{""what"": ""expr:constructor"", ""name"": ""Zpos"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XH"", ""args"": []}]}]}]}}}]}".

Definition bigger_plus_one_decl_parsed : option real_decl :=
  real_decl_of_module_json bigger_plus_one_module_json "bigger_plus_one".

Example bigger_plus_one_decl_parsed_matches_hand_built :
  bigger_plus_one_decl_parsed = Some {| rd_argnames := ["x"; "y"]; rd_body := bigger_plus_one_ir |}.
Proof. vm_compute. reflexivity. Qed.

Definition smaller_plus_one_module_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""smaller_plus_one"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rplus""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rmin""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""y""}]}, {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""iZR""}, ""args"": [{""what"": ""expr:constructor"", ""name"": ""Zpos"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XH"", ""args"": []}]}]}]}}}]}".

Definition smaller_plus_one_decl_parsed : option real_decl :=
  real_decl_of_module_json smaller_plus_one_module_json "smaller_plus_one".

Example smaller_plus_one_decl_parsed_matches_hand_built :
  smaller_plus_one_decl_parsed = Some {| rd_argnames := ["x"; "y"]; rd_body := smaller_plus_one_ir |}.
Proof. vm_compute. reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(** * A decimal [R] literal, not an integer one

    One more probe: [decimal_lit (x : R) := x + 3.14]. Confirmed
    directly: a *decimal* literal does not extract as [iZR] the way
    [quad]'s integer literal [1] does -- it extracts as [q2R (Qmake
    num den)], [QArith]'s own rational-to-real coercion applied to a
    [Q] built the same [Zpos]/[Zneg]/[Z0]/[XI]/[XO]/[XH] way an
    ordinary integer literal already is. [num / den] is in general not
    exactly representable in binary64 ([3.14 = 314/100], and [100] is
    not a power of two) -- but that is the same single rounding step
    any decimal-to-float literal already needs, Python's own [3.14]
    included, not a new approximation this project introduces
    ([RealJson.v]'s own header has the full argument). *)
Definition decimal_lit_module_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""decimal_lit"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rplus""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""q2R""}, ""args"": [{""what"": ""expr:constructor"", ""name"": ""Qmake"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""Zpos"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XI"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XI"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XI"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XI"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XH"", ""args"": []}]}]}]}]}]}]}]}]}]}, {""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XI"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XO"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XI"", ""args"": [{""what"": ""expr:constructor"", ""name"": ""XH"", ""args"": []}]}]}]}]}]}]}]}]}]}}}]}".

Definition decimal_lit_decl_parsed : option real_decl :=
  real_decl_of_module_json decimal_lit_module_json "decimal_lit".

(** [3.14]'s own exact binary64 bit pattern, confirmed directly to be
    bit-for-bit the same value real Python's own literal [3.14]
    parses to ([float.fromhex("0x1.91eb851eb851fp+1") == 3.14]). *)
Example decimal_lit_decl_parsed_matches_expected :
  decimal_lit_decl_parsed
  = Some {| rd_argnames := ["x"];
            rd_body := RApp2 "rplus" (RRel "x") (RFLit 0x1.91eb851eb851fp+1) |}.
Proof. vm_compute. reflexivity. Qed.

Definition decimal_lit_expr : expr :=
  match decimal_lit_decl_parsed with
  | Some rd =>
      match real_to_expr rd.(rd_body) with
      | Some e => e
      | None => EFConst 0%float
      end
  | None => EFConst 0%float
  end.

Example decimal_lit_expr_matches_expected_value :
  eval 10 [("x", VFloat 0)] decimal_lit_expr = Some (VFloat 0x1.91eb851eb851fp+1).
Proof. vm_compute. reflexivity. Qed.

Compute py_function "decimal_lit" (match decimal_lit_decl_parsed with Some rd => rd.(rd_argnames) | None => [] end)
  (translate decimal_lit_expr).


(* ------------------------------------------------------------------ *)
(** * Transcendentals: exp/ln/pow, a new and honestly-scoped axiom category

    [PrimFloat] has no native [exp]/[log]/power primitive at all
    (confirmed directly: [Print PrimFloat] -- see [Lang.v]'s header),
    and unlike ["rmax"]/["rmin"] there is no way to build one from
    what [expr] already has either. [Lang.v]'s [prim_exp]/[prim_ln]/
    [prim_pow] are new, project-introduced [Axiom]s closing that gap --
    deliberately the barest possible claim (a function of the right
    *type* exists, nothing about what it computes), so this is a new
    trust category, not a reuse of [PrimFloat]'s own kernel-trusted
    primitives or the stdlib's [FloatAxioms.SF2Prim_Prim2SF]. See that
    file's header for the full rationale.

    Three fresh probes, actually run through [coqc] with
    [coq-coquelicot] installed (not assumed by analogy): [expdiff (x y
    : R) := exp (x - y)], [lnsum (x y : R) := ln (x + y)], [powprod (x
    y z : R) := Rpower x (y * z)] -- each wrapping its transcendental
    inside a non-trivial expression specifically to avoid an
    eta-reduction edge case confirmed separately (a *bare* wrapper
    like [myexp (x : R) := exp x] extracts as argnames [[]] with body
    just the bare global [exp], since Coq's extraction eta-contracts
    the trivial identity application -- the non-trivial bodies here
    sidestep that, the same way [combo]/[absdiff] above already did
    for ["ropp"]/["rdiv"]). Confirmed directly (not assumed): [exp]/
    [ln] extract as plain unary [expr:apply]/[expr:global] calls (the
    same shape [RApp1] already recognizes for ["ropp"]/["rabs"]/
    ["sqrt"]), and [Rpower] extracts as a plain binary call named
    ["rpower"] (the same shape [RApp2] already recognizes for
    ["rmax"]/["rmin"]) -- so no new [RealIR.v] constructor was needed
    at all, only three new names in the existing, generic [RApp1]/
    [RApp2] dispatch. *)
Definition expdiff_ir : real_expr :=
  RApp1 "exp" (RApp2 "rminus" (RRel "x") (RRel "y")).
Definition lnsum_ir : real_expr :=
  RApp1 "ln" (RApp2 "rplus" (RRel "x") (RRel "y")).
Definition powprod_ir : real_expr :=
  RApp2 "rpower" (RRel "x") (RApp2 "rmult" (RRel "y") (RRel "z0")).

(** [real_eval]/[eval] get permanently stuck on [prim_exp]/[prim_ln]/
    [prim_pow] -- they have no Gallina body, by design (this file's
    header, [Lang.v]'s header) -- so the "matches this exact float"
    style check every arithmetic-only example above uses isn't
    available here. What *is* available, and just as strong a
    structural guarantee: a fully symbolic [reflexivity] check (the
    same technique [examples/physics/Discretize.v]'s
    [one_pass_symbolic_7point] uses) showing [real_eval]/[eval] reduce
    *exactly* down to the opaque axiom call and no further, for
    arbitrary float inputs, not just one concrete example. *)
Example expdiff_ir_matches_expected_shape :
  forall x y : PrimFloat.float,
    real_eval [("x", VFloat x); ("y", VFloat y)] expdiff_ir
    = Some (VFloat (prim_exp (PrimFloat.sub x y))).
Proof. intros. reflexivity. Qed.

Example lnsum_ir_matches_expected_shape :
  forall x y : PrimFloat.float,
    real_eval [("x", VFloat x); ("y", VFloat y)] lnsum_ir
    = Some (VFloat (prim_ln (PrimFloat.add x y))).
Proof. intros. reflexivity. Qed.

Example powprod_ir_matches_expected_shape :
  forall x y z : PrimFloat.float,
    real_eval [("x", VFloat x); ("y", VFloat y); ("z0", VFloat z)] powprod_ir
    = Some (VFloat (prim_pow x (PrimFloat.mul y z))).
Proof. intros. reflexivity. Qed.

Definition expdiff_expr : expr :=
  match real_to_expr expdiff_ir with Some e => e | None => EFConst 0 end.
Definition lnsum_expr : expr :=
  match real_to_expr lnsum_ir with Some e => e | None => EFConst 0 end.
Definition powprod_expr : expr :=
  match real_to_expr powprod_ir with Some e => e | None => EFConst 0 end.

Example expdiff_ir_translates : real_to_expr expdiff_ir = Some expdiff_expr.
Proof. reflexivity. Qed.
Example lnsum_ir_translates : real_to_expr lnsum_ir = Some lnsum_expr.
Proof. reflexivity. Qed.
Example powprod_ir_translates : real_to_expr powprod_ir = Some powprod_expr.
Proof. reflexivity. Qed.

Theorem expdiff_idents_valid : expr_idents_valid is_valid_ident expdiff_expr = true.
Proof. reflexivity. Qed.
Theorem lnsum_idents_valid : expr_idents_valid is_valid_ident lnsum_expr = true.
Proof. reflexivity. Qed.
Theorem powprod_idents_valid : expr_idents_valid is_valid_ident powprod_expr = true.
Proof. reflexivity. Qed.

Corollary expdiff_json_roundtrip :
  parse_expr_top (print_expr expdiff_expr) = Some (expdiff_expr, "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip expdiff_expr expdiff_idents_valid
                (String.length (print_expr expdiff_expr) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_append_nil_r in H. exact H.
Qed.

Corollary lnsum_json_roundtrip :
  parse_expr_top (print_expr lnsum_expr) = Some (lnsum_expr, "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip lnsum_expr lnsum_idents_valid
                (String.length (print_expr lnsum_expr) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_append_nil_r in H. exact H.
Qed.

Corollary powprod_json_roundtrip :
  parse_expr_top (print_expr powprod_expr) = Some (powprod_expr, "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip powprod_expr powprod_idents_valid
                (String.length (print_expr powprod_expr) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_append_nil_r in H. exact H.
Qed.

Corollary expdiff_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate expdiff_expr)
      = option_map value_to_pyvalue (eval fuel rho expdiff_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

Corollary lnsum_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate lnsum_expr)
      = option_map value_to_pyvalue (eval fuel rho lnsum_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

Corollary powprod_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate powprod_expr)
      = option_map value_to_pyvalue (eval fuel rho powprod_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

Compute print_expr expdiff_expr.
Compute print_expr lnsum_expr.
Compute print_expr powprod_expr.

(** The real, running Python. [math.pow]'s own domain/edge-case
    footnote is in [PyPrint.v]; nothing here checks it against
    [prim_pow]'s own (unspecified) value -- only that real Python
    actually runs and returns the numerically expected answer for a
    concrete, hand-checked input (confirmed separately: [expdiff(5,2)
    = exp(3) ~ 20.0855], [lnsum(4,3) = ln(7) ~ 1.9459],
    [powprod(2,5,2) = 2**10 = 1024.0]). *)
Compute py_function "expdiff" ["x"; "y"] (translate expdiff_expr).
Compute py_function "lnsum" ["x"; "y"] (translate lnsum_expr).
Compute py_function "powprod" ["x"; "y"; "z0"] (translate powprod_expr).

(* ------------------------------------------------------------------ *)
(** * Parsed from the real JSON text, not hand-built

    [expdiff_module_json]/[lnsum_module_json]/[powprod_module_json]
    below are the literal bytes [coqc] emitted for each declaration
    (one declaration per module object, the same per-declaration shape
    [quad_decl_json] above uses and for the same reason: this
    recognizer was never going to look at anything else in a real
    captured module anyway). *)
Definition expdiff_module_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""expdiff"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""exp""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rminus""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""y""}]}]}}}]}".

Definition expdiff_decl_parsed : option real_decl :=
  real_decl_of_module_json expdiff_module_json "expdiff".

Example expdiff_decl_parsed_matches_hand_built :
  expdiff_decl_parsed = Some {| rd_argnames := ["x"; "y"]; rd_body := expdiff_ir |}.
Proof. vm_compute. reflexivity. Qed.

Definition lnsum_module_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""lnsum"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""ln""}, ""args"": [{""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rplus""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:rel"", ""name"": ""y""}]}]}}}]}".

Definition lnsum_decl_parsed : option real_decl :=
  real_decl_of_module_json lnsum_module_json "lnsum".

Example lnsum_decl_parsed_matches_hand_built :
  lnsum_decl_parsed = Some {| rd_argnames := ["x"; "y"]; rd_body := lnsum_ir |}.
Proof. vm_compute. reflexivity. Qed.

Definition powprod_module_json : string :=
  "{""what"": ""module"", ""name"": ""Main"", ""need_magic"": false, ""need_dummy"": true, ""used_modules"": [], ""declarations"": [{""what"": ""decl:term"", ""name"": ""powprod"", ""type"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:arrow"", ""left"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}, ""right"": {""what"": ""type:glob"", ""name"": ""r"", ""args"": []}}}}, ""value"": {""what"": ""expr:lambda"", ""argnames"": [""x"", ""y"", ""z0""], ""body"": {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rpower""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""x""}, {""what"": ""expr:apply"", ""func"": {""what"": ""expr:global"", ""name"": ""rmult""}, ""args"": [{""what"": ""expr:rel"", ""name"": ""y""}, {""what"": ""expr:rel"", ""name"": ""z0""}]}]}}}]}".

Definition powprod_decl_parsed : option real_decl :=
  real_decl_of_module_json powprod_module_json "powprod".

Example powprod_decl_parsed_matches_hand_built :
  powprod_decl_parsed = Some {| rd_argnames := ["x"; "y"; "z0"]; rd_body := powprod_ir |}.
Proof. vm_compute. reflexivity. Qed.

(** Honest disclosure, not just claimed: confirmed directly (not
    assumed), exactly the three new axioms this section introduces
    ([prim_exp]/[prim_ln]/[prim_pow]) appear below, alongside
    [PrimFloat]'s own pre-existing kernel-trusted primitives
    ([float]/[add]/[sub]/[mul]/[div]/[abs]/[opp]/[sqrt]/[eqb]/[ltb]/
    [leb]) that every float-using file in this project already
    carries -- nothing from [Json.v]'s own [FloatAxioms]/classical
    axioms shows up here at all, since this corollary never goes
    through the JSON float codec. *)
Print Assumptions expdiff_translation_correct.
Print Assumptions lnsum_translation_correct.
Print Assumptions powprod_translation_correct.
