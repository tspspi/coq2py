(** Lang.v

    The source language: the (deliberately small, first) subset of Gallina
    expressions that coq2py's translator accepts. This stands in for the
    restricted "CoqIR" described in GOAL.md until ingestion is wired to
    Coq's own [Extraction Language JSON] output -- see docs/roadmap.md for
    the current, honest status of that gap.

    Values are no longer bare integers: a [value] is an integer, a
    boolean, or a pair of values (recursively), reflecting the addition
    of pairs/tuples and genuine boolean-valued comparisons in place of
    the earlier "if equals zero" hack. [eval] is partial exactly where an
    operation is applied to a value of the wrong shape (e.g. [EAdd]
    applied to a boolean) -- there is no separate static type system here,
    so "ill-typed" terms simply get stuck ([None]), the same way a failed
    variable lookup already did.

    [eval] is the formal semantics we assign to this subset: what a term
    *means*, independent of any translation target. The translator's
    correctness theorem (see Translate.v) is stated against this.

    [VFloat]/[EFConst]/[EFAdd]/[EFSub]/[EFMul]/[EFDiv] add Coq's
    primitive, IEEE-754-backed [PrimFloat.float] as a fourth value shape,
    per docs/roadmap.md's "real target is physics" discussion: this is the
    numeric type the discretized-simulator work needs, chosen over a
    fixed-point encoding over [Z] because it extracts to OCaml's native
    [float] (see Extract.v) with no new dependency, the same way [Z]
    already extracts to native [int]. It is deliberately a same-shape
    value (not mixed into [VZ]/arithmetic on [Z]) -- floats and integers
    don't silently coerce into each other here any more than booleans and
    integers already don't. [EFEq]/[EFLt]/[EFLe] mirror [EEq]/[ELt]/[ELe]
    for floats, returning [VBool] the same way; there is still no
    [EIf]-usable float-to-bool coercion beyond that (a float condition
    gets stuck, same as any other wrong-shape value). *)

From Coq Require Import ZArith String List Bool.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition var := string.

Inductive value : Type :=
  | VZ (z : Z)
  | VBool (b : bool)
  | VPair (v1 v2 : value)
  | VFloat (f : float).

Inductive expr : Type :=
  | EConst (z : Z)
  | EBool (b : bool)
  | EVar (x : var)
  | EAdd (e1 e2 : expr)
  | ESub (e1 e2 : expr)
  | EMul (e1 e2 : expr)
  | EEq (e1 e2 : expr)
  | ELt (e1 e2 : expr)
  | ELe (e1 e2 : expr)
  | EAnd (e1 e2 : expr)
  | EOr (e1 e2 : expr)
  | ENot (e : expr)
  | EIf (c e1 e2 : expr)
  | EPair (e1 e2 : expr)
  | EFst (e : expr)
  | ESnd (e : expr)
  | ELet (x : var) (e1 e2 : expr)
  | EFConst (f : float)
  | EFAdd (e1 e2 : expr)
  | EFSub (e1 e2 : expr)
  | EFMul (e1 e2 : expr)
  | EFDiv (e1 e2 : expr)
  | EFEq (e1 e2 : expr)
  | EFLt (e1 e2 : expr)
  | EFLe (e1 e2 : expr).

(** Runtime environments: a simple association list from variable names to
    values. This is intentionally the same representation on both the
    source and target side (see PyLang.v) -- for this subset, "the state of
    a running Python interpreter" and "the state of evaluating a Gallina
    term" are both honestly just "a mapping from names to values". *)
Definition env := list (var * value).

Fixpoint lookup (rho : env) (x : var) : option value :=
  match rho with
  | [] => None
  | (y, v) :: rest => if string_dec x y then Some v else lookup rest x
  end.

Fixpoint eval (rho : env) (e : expr) : option value :=
  match e with
  | EConst z => Some (VZ z)
  | EBool b => Some (VBool b)
  | EVar x => lookup rho x
  | EAdd e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VZ (v1 + v2))
      | _, _ => None
      end
  | ESub e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VZ (v1 - v2))
      | _, _ => None
      end
  | EMul e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VZ (v1 * v2))
      | _, _ => None
      end
  | EEq e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VBool (Z.eqb v1 v2))
      | _, _ => None
      end
  | ELt e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VBool (Z.ltb v1 v2))
      | _, _ => None
      end
  | ELe e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VBool (Z.leb v1 v2))
      | _, _ => None
      end
  | EAnd e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2))
      | _, _ => None
      end
  | EOr e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VBool b1), Some (VBool b2) => Some (VBool (orb b1 b2))
      | _, _ => None
      end
  | ENot e1 =>
      match eval rho e1 with
      | Some (VBool b) => Some (VBool (negb b))
      | _ => None
      end
  | EIf c e1 e2 =>
      match eval rho c with
      | Some (VBool true) => eval rho e1
      | Some (VBool false) => eval rho e2
      | _ => None
      end
  | EPair e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some v1, Some v2 => Some (VPair v1 v2)
      | _, _ => None
      end
  | EFst e1 =>
      match eval rho e1 with
      | Some (VPair v1 _) => Some v1
      | _ => None
      end
  | ESnd e1 =>
      match eval rho e1 with
      | Some (VPair _ v2) => Some v2
      | _ => None
      end
  | ELet x e1 e2 =>
      match eval rho e1 with
      | Some v1 => eval ((x, v1) :: rho) e2
      | None => None
      end
  | EFConst f => Some (VFloat f)
  | EFAdd e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 + f2)%float)
      | _, _ => None
      end
  | EFSub e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 - f2)%float)
      | _, _ => None
      end
  | EFMul e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 * f2)%float)
      | _, _ => None
      end
  | EFDiv e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 / f2)%float)
      | _, _ => None
      end
  | EFEq e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VBool (f1 =? f2)%float)
      | _, _ => None
      end
  | EFLt e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VBool (f1 <? f2)%float)
      | _, _ => None
      end
  | EFLe e1 e2 =>
      match eval rho e1, eval rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VBool (f1 <=? f2)%float)
      | _, _ => None
      end
  end.

(** Identifier validity: the restricted grammar in Json.v only round-trips
    names made of ASCII letters/digits/underscore. This predicate marks
    exactly the [expr] terms whose variable names satisfy that. It is not a
    restriction on the semantics above -- [eval] is total (modulo the
    "wrong shape of value" / unbound-variable getting-stuck cases already
    described) over all [expr] values regardless of identifier shape. *)
Fixpoint expr_idents_valid (is_valid_ident : var -> bool) (e : expr) : bool :=
  match e with
  | EConst _ => true
  | EBool _ => true
  | EVar x => is_valid_ident x
  | EAdd e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | ESub e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EMul e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EEq e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | ELt e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | ELe e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EAnd e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EOr e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | ENot e1 => expr_idents_valid is_valid_ident e1
  | EIf c e1 e2 =>
      andb (expr_idents_valid is_valid_ident c)
           (andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2))
  | EPair e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EFst e1 => expr_idents_valid is_valid_ident e1
  | ESnd e1 => expr_idents_valid is_valid_ident e1
  | ELet x e1 e2 =>
      andb (is_valid_ident x)
           (andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2))
  | EFConst _ => true
  | EFAdd e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EFSub e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EFMul e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EFDiv e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EFEq e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EFLt e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EFLe e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  end.
