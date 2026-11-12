(** PyLang.v

    The target language: a Coq-defined abstract syntax for the subset of
    Python expressions coq2py generates. [peval] is the formal semantics we
    assign to it -- i.e. this is the formal specification of what we claim
    these Python constructs mean. The honest, explicitly-accepted trust
    boundary (see GOAL.md and docs/duality.md) is that *this* semantics
    faithfully describes what the real CPython interpreter does on the
    corresponding generated source text; that correspondence is assumed,
    not proved, here -- exactly the role real hardware/assembly semantics
    play in CompCert's own trusted computing base.

    [pyexpr] mirrors [expr] (Lang.v) constructor-for-constructor in this
    first version. That is not an accident of laziness: it reflects that
    this initial subset of Python (int-valued expressions, conditionals,
    local let-bindings) really is semantically identical to the source
    subset. Divergence between source and target shape is expected once
    the supported subset grows (e.g. numpy array operations with no direct
    Gallina counterpart) -- at that point [pyexpr] grows new constructors
    that [translate] (Translate.v) maps multiple source constructs onto. *)

From Coq Require Import ZArith String List.
Import ListNotations.
Require Import Lang.
Open Scope Z_scope.
Open Scope string_scope.

Inductive pyexpr : Type :=
  | PConst (z : Z)
  | PVar (x : var)
  | PAdd (e1 e2 : pyexpr)
  | PSub (e1 e2 : pyexpr)
  | PMul (e1 e2 : pyexpr)
  | PIf0 (c e1 e2 : pyexpr)
  | PLet (x : var) (e1 e2 : pyexpr).

Fixpoint peval (rho : env) (e : pyexpr) : option Z :=
  match e with
  | PConst z => Some z
  | PVar x => lookup rho x
  | PAdd e1 e2 =>
      match peval rho e1, peval rho e2 with
      | Some v1, Some v2 => Some (v1 + v2)
      | _, _ => None
      end
  | PSub e1 e2 =>
      match peval rho e1, peval rho e2 with
      | Some v1, Some v2 => Some (v1 - v2)
      | _, _ => None
      end
  | PMul e1 e2 =>
      match peval rho e1, peval rho e2 with
      | Some v1, Some v2 => Some (v1 * v2)
      | _, _ => None
      end
  | PIf0 c e1 e2 =>
      match peval rho c with
      | Some v => if Z.eqb v 0 then peval rho e1 else peval rho e2
      | None => None
      end
  | PLet x e1 e2 =>
      match peval rho e1 with
      | Some v1 => peval ((x, v1) :: rho) e2
      | None => None
      end
  end.
