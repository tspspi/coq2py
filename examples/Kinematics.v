(** Kinematics.v

    The running example for coq2py: a single semi-implicit ("symplectic")
    Euler integration step,

        v' = v + a*dt
        x' = x + v'*dt

    returning the pair (x', v') -- exercising pairs/tuples -- plus a
    second example, [landed_expr], exercising general comparisons and
    booleans: "has the projectile reached or passed ground level while
    still moving downward?" -- and two more, [euler_step_float_expr] and
    [landed_float_expr], the same integration step and landing check
    again but over real [PrimFloat.float] state instead of [Z].

    All four are expressed as terms of our supported [expr] subset
    (Lang.v), then run through every stage of the pipeline this repository
    actually proves: JSON round-trip (Json.v), translation to the
    Python-subset AST (Translate.v), and rendering as Python source
    (PyPrint.v). Everything marked [Compute] below is meant to be
    evaluated with [coqc]/[coqtop] and its real output captured into
    docs/examples.md -- nothing in that doc is hand-written/fabricated.

    This is also the first concrete instance of the project's stated goal
    (GOAL.md): "express physics in Coq, extract a Python simulator proven
    correct". Examples 1 and 2 are deliberately tiny instances -- integers
    standing in for what would eventually be a floating-point/numpy state
    vector -- chosen to stay inside the subset that's actually proven
    today rather than gesture at scope the proofs don't yet cover. Examples
    3 and 4 close that gap for a single step (real float arithmetic and
    comparisons, proven the same way) -- see docs/roadmap.md for what's
    still missing before a genuine discretized simulator (bounded
    iteration, arrays). *)

From Coq Require Import ZArith String List Bool Lia.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Open Scope Z_scope.
Open Scope string_scope.

Lemma string_app_nil_r : forall s : string, s ++ "" = s.
Proof.
  induction s as [| c s' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** A reusable tactic, applied below to each (concrete) example term:
    valid identifiers plus the general theorems already proved in Json.v
    and Translate.v are enough to get the JSON round-trip "for free", with
    no new proof obligations. (Kept as a tactic rather than a lemma
    because the fuel side-condition is discharged by [vm_compute], which
    needs the term concrete -- it doesn't go through for an arbitrary
    [e].) *)
Ltac json_roundtrip_corollary e Hvalid :=
  unfold parse_expr_top;
  let H := fresh "H" in
  pose proof (parse_print_roundtrip e Hvalid
                (String.length (print_expr e) + 1)
                ltac:(vm_compute; lia) "") as H;
  rewrite string_app_nil_r in H;
  exact H.

(* ----------------------------------------------------------------- *)
(** * Example 1: one Euler step, returning the pair (x', v') *)

Definition euler_step_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (EPair (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))) (EVar "v2")).

(** This term is within the provably-covered subset: all its identifiers
    are valid, so [parse_print_roundtrip] and [translate_preserves_semantics]
    both apply to it unconditionally. *)
Theorem euler_step_idents_valid :
  expr_idents_valid is_valid_ident euler_step_expr = true.
Proof. reflexivity. Qed.

(** A concrete run: starting at rest (x=0, v=0) with acceleration a=2 for
    one step of dt=1, the new state is (x'=2, v'=2). *)
Example euler_step_concrete :
  eval [("x", VZ 0); ("v", VZ 0); ("a", VZ 2); ("dt", VZ 1)] euler_step_expr
    = Some (VPair (VZ 2) (VZ 2)).
Proof. reflexivity. Qed.

(** The JSON encoding of the example term. *)
Compute print_expr euler_step_expr.

(** Parsing that text back recovers the exact same term (and consumes
    all of it, leaving nothing unparsed) -- an instance of
    [parse_print_roundtrip], not a new proof. *)
Compute parse_expr_top (print_expr euler_step_expr).

Corollary euler_step_json_roundtrip :
  parse_expr_top (print_expr euler_step_expr) = Some (euler_step_expr, "").
Proof. json_roundtrip_corollary euler_step_expr euler_step_idents_valid. Qed.

(** The translated Python-subset AST, evaluated under the formal [peval]
    semantics, agrees with [eval] on the source term (up to the
    value<->pyvalue correspondence) -- an instance of
    [translate_preserves_semantics], not a new proof. *)
Corollary euler_step_translation_correct :
  forall rho,
    peval (env_to_pyenv rho) (translate euler_step_expr)
      = option_map value_to_pyvalue (eval rho euler_step_expr).
Proof. intro rho. apply translate_preserves_semantics. Qed.

(** The actual generated Python source. *)
Compute py_function "euler_step" ["x"; "v"; "a"; "dt"] (translate euler_step_expr).

(* ----------------------------------------------------------------- *)
(** * Example 2: general comparisons and booleans *)

(** Has the projectile reached or passed ground level while still moving
    downward? (Checking the direction of motion too avoids reporting
    "landed" for a projectile that started on or below the ground and is
    still rising.) *)
Definition landed_expr : expr :=
  EAnd (ELe (EVar "x") (EConst 0)) (ELt (EVar "v") (EConst 0)).

Theorem landed_idents_valid :
  expr_idents_valid is_valid_ident landed_expr = true.
Proof. reflexivity. Qed.

Example landed_concrete_true :
  eval [("x", VZ (-1)); ("v", VZ (-3))] landed_expr = Some (VBool true).
Proof. reflexivity. Qed.

Example landed_concrete_false_still_above_ground :
  eval [("x", VZ 5); ("v", VZ (-3))] landed_expr = Some (VBool false).
Proof. reflexivity. Qed.

Example landed_concrete_false_rising :
  eval [("x", VZ (-1)); ("v", VZ 3)] landed_expr = Some (VBool false).
Proof. reflexivity. Qed.

Compute print_expr landed_expr.
Compute parse_expr_top (print_expr landed_expr).

Corollary landed_json_roundtrip :
  parse_expr_top (print_expr landed_expr) = Some (landed_expr, "").
Proof. json_roundtrip_corollary landed_expr landed_idents_valid. Qed.

Corollary landed_translation_correct :
  forall rho,
    peval (env_to_pyenv rho) (translate landed_expr)
      = option_map value_to_pyvalue (eval rho landed_expr).
Proof. intro rho. apply translate_preserves_semantics. Qed.

Compute py_function "landed" ["x"; "v"] (translate landed_expr).

(* ----------------------------------------------------------------- *)
(** * Example 3: the same Euler step, in real floats *)

(** Identical in shape to [euler_step_expr] above, but over
    [PrimFloat.float] state and [EFAdd]/[EFMul] arithmetic instead of
    [Z]/[EAdd]/[EMul] -- the same machine-checked preservation and
    JSON-round-trip theorems apply unconditionally here too, with no
    separate float-specific argument needed. *)
Definition euler_step_float_expr : expr :=
  ELet "v2" (EFAdd (EVar "v") (EFMul (EVar "a") (EVar "dt")))
    (EPair (EFAdd (EVar "x") (EFMul (EVar "v2") (EVar "dt"))) (EVar "v2")).

Theorem euler_step_float_idents_valid :
  expr_idents_valid is_valid_ident euler_step_float_expr = true.
Proof. reflexivity. Qed.

(** Starting at rest (x=0.0, v=0.0) with acceleration a=2.0 for one step
    of dt=1.0, the new state is (x'=2.0, v'=2.0) -- the same answer as
    [euler_step_concrete] above, now computed in real [float]
    arithmetic rather than standing in via [Z]. *)
Example euler_step_float_concrete :
  eval [("x", VFloat 0.0%float); ("v", VFloat 0.0%float);
        ("a", VFloat 2.0%float); ("dt", VFloat 1.0%float)]
    euler_step_float_expr
    = Some (VPair (VFloat 2.0%float) (VFloat 2.0%float)).
Proof. reflexivity. Qed.

Compute print_expr euler_step_float_expr.
Compute parse_expr_top (print_expr euler_step_float_expr).

Corollary euler_step_float_json_roundtrip :
  parse_expr_top (print_expr euler_step_float_expr) = Some (euler_step_float_expr, "").
Proof. json_roundtrip_corollary euler_step_float_expr euler_step_float_idents_valid. Qed.

Corollary euler_step_float_translation_correct :
  forall rho,
    peval (env_to_pyenv rho) (translate euler_step_float_expr)
      = option_map value_to_pyvalue (eval rho euler_step_float_expr).
Proof. intro rho. apply translate_preserves_semantics. Qed.

(** The generated Python: exact, via the [mantissa * (2.0 ** exponent)]
    encoding described in PyPrint.v -- not the shortest decimal a human
    would write, but bit-for-bit the same value as the source float. *)
Compute py_function "euler_step_float" ["x"; "v"; "a"; "dt"] (translate euler_step_float_expr).

(* ----------------------------------------------------------------- *)
(** * Example 4: [landed_expr], over real floats *)

(** [landed_expr] (Example 2) restated with [EFLe]/[EFLt] over real
    [float] position/velocity instead of [ELe]/[ELt] over [Z] -- the
    comparison counterpart to Example 3's arithmetic one. *)
Definition landed_float_expr : expr :=
  EAnd (EFLe (EVar "x") (EFConst 0)) (EFLt (EVar "v") (EFConst 0)).

Theorem landed_float_idents_valid :
  expr_idents_valid is_valid_ident landed_float_expr = true.
Proof. reflexivity. Qed.

Example landed_float_concrete_true :
  eval [("x", VFloat (-1)%float); ("v", VFloat (-3)%float)] landed_float_expr
    = Some (VBool true).
Proof. reflexivity. Qed.

Example landed_float_concrete_false_still_above_ground :
  eval [("x", VFloat 5%float); ("v", VFloat (-3)%float)] landed_float_expr
    = Some (VBool false).
Proof. reflexivity. Qed.

Compute py_function "landed_float" ["x"; "v"] (translate landed_float_expr).
