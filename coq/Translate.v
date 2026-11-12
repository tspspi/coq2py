(** Translate.v

    The proven heart of coq2py: the translation from the source subset
    (Lang.v) to the target subset (PyLang.v), together with a
    machine-checked theorem that it preserves semantics. This is the one
    component GOAL.md calls out as unconditionally requiring proof: it is
    "part of the actual translator". *)

From Coq Require Import ZArith String List.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Open Scope Z_scope.
Open Scope string_scope.

Fixpoint translate (e : expr) : pyexpr :=
  match e with
  | EConst z => PConst z
  | EVar x => PVar x
  | EAdd e1 e2 => PAdd (translate e1) (translate e2)
  | ESub e1 e2 => PSub (translate e1) (translate e2)
  | EMul e1 e2 => PMul (translate e1) (translate e2)
  | EIf0 c e1 e2 => PIf0 (translate c) (translate e1) (translate e2)
  | ELet x e1 e2 => PLet x (translate e1) (translate e2)
  end.

(** The correctness theorem: for every source term and every environment,
    evaluating the translated Python AST under [peval] gives exactly the
    same answer (including "gets stuck", i.e. [None]) as evaluating the
    source term under [eval]. No side conditions, no restriction to
    well-formed or closed terms -- it holds unconditionally over this
    subset. *)
Theorem translate_preserves_semantics :
  forall (e : expr) (rho : env),
    peval rho (translate e) = eval rho e.
Proof.
  induction e as
    [ z
    | x
    | e1 IH1 e2 IH2
    | e1 IH1 e2 IH2
    | e1 IH1 e2 IH2
    | c IHc e1 IH1 e2 IH2
    | x e1 IH1 e2 IH2 ];
  intro rho; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IHc.
    destruct (eval rho c) as [v|].
    + destruct (Z.eqb v 0).
      * apply IH1.
      * apply IH2.
    + reflexivity.
  - rewrite IH1.
    destruct (eval rho e1) as [v1|].
    + apply IH2.
    + reflexivity.
Qed.
