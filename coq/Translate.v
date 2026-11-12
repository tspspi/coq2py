(** Translate.v

    The proven heart of coq2py: the translation from the source subset
    (Lang.v) to the target subset (PyLang.v), together with a
    machine-checked theorem that it preserves semantics. This is the one
    component GOAL.md calls out as unconditionally requiring proof: it is
    "part of the actual translator".

    Since source [value]s and target [pyvalue]s are now separate (mirrored)
    types rather than both being bare [Z], stating "preserves semantics"
    needs an explicit correspondence between them -- [value_to_pyvalue] and
    its lifting to environments, [env_to_pyenv]. Both are structural,
    one-line-per-constructor translations, not meaningful transformations
    in their own right. *)

From Coq Require Import ZArith String List Bool.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Open Scope Z_scope.
Open Scope string_scope.

Fixpoint translate (e : expr) : pyexpr :=
  match e with
  | EConst z => PConst z
  | EBool b => PBool b
  | EVar x => PVar x
  | EAdd e1 e2 => PAdd (translate e1) (translate e2)
  | ESub e1 e2 => PSub (translate e1) (translate e2)
  | EMul e1 e2 => PMul (translate e1) (translate e2)
  | EEq e1 e2 => PEq (translate e1) (translate e2)
  | ELt e1 e2 => PLt (translate e1) (translate e2)
  | ELe e1 e2 => PLe (translate e1) (translate e2)
  | EAnd e1 e2 => PAnd (translate e1) (translate e2)
  | EOr e1 e2 => POr (translate e1) (translate e2)
  | ENot e1 => PNot (translate e1)
  | EIf c e1 e2 => PIf (translate c) (translate e1) (translate e2)
  | EPair e1 e2 => PPair (translate e1) (translate e2)
  | EFst e1 => PFst (translate e1)
  | ESnd e1 => PSnd (translate e1)
  | ELet x e1 e2 => PLet x (translate e1) (translate e2)
  end.

Fixpoint value_to_pyvalue (v : value) : pyvalue :=
  match v with
  | VZ z => PVZ z
  | VBool b => PVBool b
  | VPair v1 v2 => PVPair (value_to_pyvalue v1) (value_to_pyvalue v2)
  end.

Fixpoint env_to_pyenv (rho : env) : pyenv :=
  match rho with
  | [] => []
  | (x, v) :: rest => (x, value_to_pyvalue v) :: env_to_pyenv rest
  end.

Lemma lookup_pyenv :
  forall rho x, plookup (env_to_pyenv rho) x = option_map value_to_pyvalue (lookup rho x).
Proof.
  induction rho as [| [y v] rho' IH]; intro x; simpl.
  - reflexivity.
  - destruct (string_dec x y); [reflexivity | apply IH].
Qed.

(** The correctness theorem: for every source term and every environment,
    evaluating the translated Python AST under [peval] (against the
    pointwise-translated environment) gives exactly the same answer
    (including "gets stuck", i.e. [None]) as evaluating the source term
    under [eval], up to translating the resulting value. No side
    conditions, no restriction to well-formed or closed terms -- it holds
    unconditionally over this subset. *)
Theorem translate_preserves_semantics :
  forall (e : expr) (rho : env),
    peval (env_to_pyenv rho) (translate e) = option_map value_to_pyvalue (eval rho e).
Proof.
  induction e as
    [ z                           (* EConst *)
    | b                           (* EBool *)
    | x                           (* EVar *)
    | e1 IH1 e2 IH2               (* EAdd *)
    | e1 IH1 e2 IH2               (* ESub *)
    | e1 IH1 e2 IH2               (* EMul *)
    | e1 IH1 e2 IH2               (* EEq *)
    | e1 IH1 e2 IH2               (* ELt *)
    | e1 IH1 e2 IH2               (* ELe *)
    | e1 IH1 e2 IH2               (* EAnd *)
    | e1 IH1 e2 IH2               (* EOr *)
    | e1 IH1                      (* ENot *)
    | c IHc e1 IH1 e2 IH2         (* EIf *)
    | e1 IH1 e2 IH2               (* EPair *)
    | e1 IH1                      (* EFst *)
    | e1 IH1                      (* ESnd *)
    | x e1 IH1 e2 IH2 ];          (* ELet *)
  intro rho; simpl.
  - (* EConst *) reflexivity.
  - (* EBool *) reflexivity.
  - (* EVar *) apply lookup_pyenv.
  - (* EAdd *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* ESub *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* EMul *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* EEq *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* ELt *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* ELe *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* EAnd *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* EOr *) rewrite IH1, IH2.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; destruct (eval rho e2) as [[z2|b2|p2a p2b]|]; reflexivity.
  - (* ENot *) rewrite IH1.
    destruct (eval rho e1) as [[z1|b1|p1a p1b]|]; reflexivity.
  - (* EIf *) rewrite IHc.
    destruct (eval rho c) as [[z|b|v1 v2]|].
    + reflexivity.
    + destruct b; [apply IH1 | apply IH2].
    + reflexivity.
    + reflexivity.
  - (* EPair *) rewrite IH1, IH2.
    destruct (eval rho e1); destruct (eval rho e2); reflexivity.
  - (* EFst *) rewrite IH1.
    destruct (eval rho e1) as [[z|b|v1 v2]|]; reflexivity.
  - (* ESnd *) rewrite IH1.
    destruct (eval rho e1) as [[z|b|v1 v2]|]; reflexivity.
  - (* ELet *) rewrite IH1.
    destruct (eval rho e1) as [v1|].
    + exact (IH2 ((x, v1) :: rho)).
    + reflexivity.
Qed.
