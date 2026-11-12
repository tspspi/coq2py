(** Kinematics.v

    The running example for coq2py: a single semi-implicit ("symplectic")
    Euler integration step,

        v' = v + a*dt
        x' = x + v'*dt

    expressed as a term of our supported [expr] subset (Lang.v), then run
    through every stage of the pipeline this repository actually proves:
    JSON round-trip (Json.v), translation to the Python-subset AST
    (Translate.v), and rendering as Python source (PyPrint.v). Everything
    marked [Compute] below is meant to be evaluated with [coqc]/[coqtop]
    and its real output captured into docs/examples.md -- nothing in that
    doc is hand-written/fabricated.

    This is also the first concrete instance of the project's stated goal
    (GOAL.md): "express physics in Coq, extract a Python simulator proven
    correct". It's a deliberately tiny instance -- integers standing in
    for what would eventually be a floating-point/numpy state vector --
    chosen to stay inside the subset that's actually proven today rather
    than gesture at scope the proofs don't yet cover. *)

From Coq Require Import ZArith String List Lia.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Open Scope Z_scope.
Open Scope string_scope.

Definition euler_step_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))).

(** This term is within the provably-covered subset: all its identifiers
    are valid, so [parse_print_roundtrip] and [translate_preserves_semantics]
    both apply to it unconditionally. *)
Theorem euler_step_idents_valid :
  expr_idents_valid is_valid_ident euler_step_expr = true.
Proof. reflexivity. Qed.

(** A concrete run: starting at rest (x=0, v=0) with acceleration a=2 for
    one step of dt=1, the new position is 2. *)
Example euler_step_concrete :
  eval [("x", 0); ("v", 0); ("a", 2); ("dt", 1)] euler_step_expr = Some 2.
Proof. reflexivity. Qed.

(** The JSON encoding of the example term. *)
Compute print_expr euler_step_expr.

(** Parsing that text back recovers the exact same term (and consumes
    all of it, leaving nothing unparsed) -- this is
    [parse_print_roundtrip] applied to this specific example, not a new
    proof. *)
Compute parse_expr_top (print_expr euler_step_expr).

Lemma string_app_nil_r : forall s : string, s ++ "" = s.
Proof.
  induction s as [| c s' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Corollary euler_step_json_roundtrip :
  parse_expr_top (print_expr euler_step_expr) = Some (euler_step_expr, "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip euler_step_expr euler_step_idents_valid
                (String.length (print_expr euler_step_expr) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_app_nil_r in H.
  exact H.
Qed.

(** The translated Python-subset AST, evaluated under the formal [peval]
    semantics, agrees with [eval] on the source term -- this is
    [translate_preserves_semantics] applied to this specific example. *)
Corollary euler_step_translation_correct :
  forall rho, peval rho (translate euler_step_expr) = eval rho euler_step_expr.
Proof. intro rho. apply translate_preserves_semantics. Qed.

(** The actual generated Python source. *)
Compute py_function "euler_step" ["x"; "v"; "a"; "dt"] (translate euler_step_expr).
