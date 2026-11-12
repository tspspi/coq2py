(** Lang.v

    The source language: the (deliberately small, first) subset of Gallina
    expressions that coq2py's translator accepts. This stands in for the
    restricted "CoqIR" described in GOAL.md until ingestion is wired to
    Coq's own [Extraction Language JSON] output -- see docs/roadmap.md for
    the current, honest status of that gap.

    [eval] is the formal semantics we assign to this subset: what a term
    *means*, independent of any translation target. The translator's
    correctness theorem (see Translate.v) is stated against this. *)

From Coq Require Import ZArith String List.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition var := string.

Inductive expr : Type :=
  | EConst (z : Z)
  | EVar (x : var)
  | EAdd (e1 e2 : expr)
  | ESub (e1 e2 : expr)
  | EMul (e1 e2 : expr)
  | EIf0 (c e1 e2 : expr)        (* if c = 0 then e1 else e2 *)
  | ELet (x : var) (e1 e2 : expr).

(** Runtime environments: a simple association list from variable names to
    integers. This is intentionally the same representation on both the
    source and target side (see PyLang.v) -- for this subset, "the state of
    a running Python interpreter" and "the state of evaluating a Gallina
    term" are both honestly just "a mapping from names to integers". *)
Definition env := list (var * Z).

Fixpoint lookup (rho : env) (x : var) : option Z :=
  match rho with
  | [] => None
  | (y, v) :: rest => if string_dec x y then Some v else lookup rest x
  end.

Fixpoint eval (rho : env) (e : expr) : option Z :=
  match e with
  | EConst z => Some z
  | EVar x => lookup rho x
  | EAdd e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some v1, Some v2 => Some (v1 + v2)
      | _, _ => None
      end
  | ESub e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some v1, Some v2 => Some (v1 - v2)
      | _, _ => None
      end
  | EMul e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some v1, Some v2 => Some (v1 * v2)
      | _, _ => None
      end
  | EIf0 c e1 e2 =>
      match eval rho c with
      | Some v => if Z.eqb v 0 then eval rho e1 else eval rho e2
      | None => None
      end
  | ELet x e1 e2 =>
      match eval rho e1 with
      | Some v1 => eval ((x, v1) :: rho) e2
      | None => None
      end
  end.

(** Identifier validity: the restricted grammar in Json.v only round-trips
    names made of ASCII letters/digits/underscore. This predicate marks
    exactly the [expr] terms whose variable names satisfy that. It is not a
    restriction on the semantics above -- [eval] is total over all [expr]
    values regardless of identifier shape. *)
Fixpoint expr_idents_valid (is_valid_ident : var -> bool) (e : expr) : bool :=
  match e with
  | EConst _ => true
  | EVar x => is_valid_ident x
  | EAdd e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | ESub e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EMul e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EIf0 c e1 e2 =>
      andb (expr_idents_valid is_valid_ident c)
           (andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2))
  | ELet x e1 e2 =>
      andb (is_valid_ident x)
           (andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2))
  end.
