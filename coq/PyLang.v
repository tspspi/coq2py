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

    [pyexpr]/[pyvalue] mirror [expr]/[value] (Lang.v) constructor-for-
    constructor in this version. That is not an accident of laziness: it
    reflects that this subset of Python (int/bool/tuple/function-valued
    expressions, conditionals, local let-bindings) really is semantically
    identical to the source subset. Divergence between source and target
    shape is expected once the supported subset grows (e.g. numpy array
    operations with no direct Gallina counterpart) -- at that point
    [pyexpr] grows new constructors that [translate] (Translate.v) maps
    multiple source constructs onto.

    [peval] takes the same explicit [fuel : nat] [Lang.v]'s [eval] does,
    for the identical reason (see that file's header): once [PLam]/
    [PRec] let a closure be returned, stored, and reapplied via [PApp],
    evaluating its body is no longer a structural subterm of whatever
    [pyexpr] [peval] was originally called on, so a total Coq [Fixpoint]
    needs an explicit resource bound to stay total. *)

From Coq Require Import ZArith String List Bool.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Require Import Lang.
Open Scope Z_scope.
Open Scope string_scope.

Inductive pyexpr : Type :=
  | PConst (z : Z)
  | PBool (b : bool)
  | PVar (x : var)
  | PAdd (e1 e2 : pyexpr)
  | PSub (e1 e2 : pyexpr)
  | PMul (e1 e2 : pyexpr)
  | PEq (e1 e2 : pyexpr)
  | PLt (e1 e2 : pyexpr)
  | PLe (e1 e2 : pyexpr)
  | PAnd (e1 e2 : pyexpr)
  | POr (e1 e2 : pyexpr)
  | PNot (e : pyexpr)
  | PIf (c e1 e2 : pyexpr)
  | PPair (e1 e2 : pyexpr)
  | PFst (e : pyexpr)
  | PSnd (e : pyexpr)
  | PLet (x : var) (e1 e2 : pyexpr)
  | PFConst (f : float)
  | PFAdd (e1 e2 : pyexpr)
  | PFSub (e1 e2 : pyexpr)
  | PFMul (e1 e2 : pyexpr)
  | PFDiv (e1 e2 : pyexpr)
  | PFEq (e1 e2 : pyexpr)
  | PFLt (e1 e2 : pyexpr)
  | PFLe (e1 e2 : pyexpr)
  | PRepeat (n : nat) (x : var) (body init : pyexpr)
  | PDiv (e1 e2 : pyexpr)
  | PMod (e1 e2 : pyexpr)
  | PLam (param : var) (body : pyexpr)
  | PRec (f param : var) (body : pyexpr)
  | PRecMut (f1 param1 : var) (body1 : pyexpr) (f2 param2 : var) (body2 : pyexpr)
  | PApp (func arg : pyexpr)
  | PNil
  | PCons (hd tl : pyexpr)
  | PListMatch (scrutinee nilcase : pyexpr) (hd tl : var) (conscase : pyexpr)
  | PRecord (k1 : var) (e1 : pyexpr) (k2 : var) (e2 : pyexpr)
  | PField (name : var) (e : pyexpr)
  | PInl (e : pyexpr)
  | PInr (e : pyexpr)
  | PCase (scrutinee : pyexpr) (x1 : var) (case1 : pyexpr) (x2 : var) (case2 : pyexpr)
  | PStrConst (s : var)
  | PStrConcat (e1 e2 : pyexpr)
  | PStrEq (e1 e2 : pyexpr)
  | PRecordN (fields : list (var * pyexpr))
  | PFieldN (name : var) (e : pyexpr)
  | PRecGroup (fns : list (var * var * pyexpr)).

Inductive pyvalue : Type :=
  | PVZ (z : Z)
  | PVBool (b : bool)
  | PVPair (v1 v2 : pyvalue)
  | PVFloat (f : float)
  | PVClosure (self : option var) (param : var) (body : pyexpr) (cenv : list (var * pyvalue))
  | PVList (vs : list pyvalue)
  | PVRecord (k1 : var) (v1 : pyvalue) (k2 : var) (v2 : pyvalue)
  | PVClosureMut (f1 param1 : var) (body1 : pyexpr) (f2 param2 : var) (body2 : pyexpr)
      (cenv : list (var * pyvalue)) (which : bool)
  | PVInl (v : pyvalue)
  | PVInr (v : pyvalue)
  | PVStr (s : var)
  | PVRecordN (fields : list (var * pyvalue))
  | PVClosureGroup (fns : list (var * var * pyexpr)) (cenv : list (var * pyvalue)) (self_name : var).

Definition pyenv := list (var * pyvalue).

Fixpoint plookup (rho : pyenv) (x : var) : option pyvalue :=
  match rho with
  | [] => None
  | (y, v) :: rest => if string_dec x y then Some v else plookup rest x
  end.

Fixpoint plookup_group_fn (fns : list (var * var * pyexpr)) (name : var) : option (var * pyexpr) :=
  match fns with
  | [] => None
  | (f, p, b) :: rest => if string_dec f name then Some (p, b) else plookup_group_fn rest name
  end.

(** [piterate] mirrors [Lang.iterate] exactly, constructor for
    constructor, for the same reason given there. *)
Fixpoint piterate (n : nat) (f : pyvalue -> option pyvalue) (v : pyvalue) : option pyvalue :=
  match n with
  | O => Some v
  | S n' =>
      match f v with
      | Some v' => piterate n' f v'
      | None => None
      end
  end.

Fixpoint peval (fuel : nat) (rho : pyenv) (e : pyexpr) : option pyvalue :=
  match fuel with
  | O => None
  | S fuel' =>
  match e with
  | PConst z => Some (PVZ z)
  | PBool b => Some (PVBool b)
  | PVar x => plookup rho x
  | PAdd e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ v1), Some (PVZ v2) => Some (PVZ (v1 + v2))
      | _, _ => None
      end
  | PSub e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ v1), Some (PVZ v2) => Some (PVZ (v1 - v2))
      | _, _ => None
      end
  | PMul e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ v1), Some (PVZ v2) => Some (PVZ (v1 * v2))
      | _, _ => None
      end
  | PEq e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ v1), Some (PVZ v2) => Some (PVBool (Z.eqb v1 v2))
      | _, _ => None
      end
  | PLt e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ v1), Some (PVZ v2) => Some (PVBool (Z.ltb v1 v2))
      | _, _ => None
      end
  | PLe e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ v1), Some (PVZ v2) => Some (PVBool (Z.leb v1 v2))
      | _, _ => None
      end
  | PAnd e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVBool b1), Some (PVBool b2) => Some (PVBool (andb b1 b2))
      | _, _ => None
      end
  | POr e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVBool b1), Some (PVBool b2) => Some (PVBool (orb b1 b2))
      | _, _ => None
      end
  | PNot e1 =>
      match peval fuel' rho e1 with
      | Some (PVBool b) => Some (PVBool (negb b))
      | _ => None
      end
  | PIf c e1 e2 =>
      match peval fuel' rho c with
      | Some (PVBool true) => peval fuel' rho e1
      | Some (PVBool false) => peval fuel' rho e2
      | _ => None
      end
  | PPair e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some v1, Some v2 => Some (PVPair v1 v2)
      | _, _ => None
      end
  | PFst e1 =>
      match peval fuel' rho e1 with
      | Some (PVPair v1 _) => Some v1
      | _ => None
      end
  | PSnd e1 =>
      match peval fuel' rho e1 with
      | Some (PVPair _ v2) => Some v2
      | _ => None
      end
  | PLet x e1 e2 =>
      match peval fuel' rho e1 with
      | Some v1 => peval fuel' ((x, v1) :: rho) e2
      | None => None
      end
  | PFConst f => Some (PVFloat f)
  | PFAdd e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVFloat (f1 + f2)%float)
      | _, _ => None
      end
  | PFSub e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVFloat (f1 - f2)%float)
      | _, _ => None
      end
  | PFMul e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVFloat (f1 * f2)%float)
      | _, _ => None
      end
  | PFDiv e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVFloat (f1 / f2)%float)
      | _, _ => None
      end
  | PFEq e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVBool (f1 =? f2)%float)
      | _, _ => None
      end
  | PFLt e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVBool (f1 <? f2)%float)
      | _, _ => None
      end
  | PFLe e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVBool (f1 <=? f2)%float)
      | _, _ => None
      end
  | PRepeat n x body init =>
      match peval fuel' rho init with
      | Some v0 => piterate n (fun v => peval fuel' ((x, v) :: rho) body) v0
      | None => None
      end
  | PDiv e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ a), Some (PVZ b) => if Z.eqb b 0 then None else Some (PVZ (Z.div a b))
      | _, _ => None
      end
  | PMod e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVZ a), Some (PVZ b) => if Z.eqb b 0 then None else Some (PVZ (Z.modulo a b))
      | _, _ => None
      end
  | PLam param body => Some (PVClosure None param body rho)
  | PRec f param body => Some (PVClosure (Some f) param body rho)
  | PRecMut f1 param1 body1 f2 param2 body2 =>
      Some (PVPair (PVClosureMut f1 param1 body1 f2 param2 body2 rho false)
                   (PVClosureMut f1 param1 body1 f2 param2 body2 rho true))
  | PApp func arg =>
      match peval fuel' rho func, peval fuel' rho arg with
      | Some (PVClosure self param body cenv), Some argv =>
          let cenv' :=
            match self with
            | None => cenv
            | Some fname => (fname, PVClosure self param body cenv) :: cenv
            end in
          peval fuel' ((param, argv) :: cenv') body
      | Some (PVClosureMut f1 param1 body1 f2 param2 body2 cenv which), Some argv =>
          let cenv' :=
            (f1, PVClosureMut f1 param1 body1 f2 param2 body2 cenv false)
            :: (f2, PVClosureMut f1 param1 body1 f2 param2 body2 cenv true)
            :: cenv in
          if which
          then peval fuel' ((param2, argv) :: cenv') body2
          else peval fuel' ((param1, argv) :: cenv') body1
      | Some (PVClosureGroup fns cenv self_name), Some argv =>
          match plookup_group_fn fns self_name with
          | Some (param, body) =>
              let cenv' :=
                (fix build_bindings (gs : list (var * var * pyexpr)) : pyenv :=
                   match gs with
                   | [] => cenv
                   | (f, p, b) :: rest => (f, PVClosureGroup fns cenv f) :: build_bindings rest
                   end) fns in
              peval fuel' ((param, argv) :: cenv') body
          | None => None
          end
      | _, _ => None
      end
  | PNil => Some (PVList [])
  | PCons hd tl =>
      match peval fuel' rho hd, peval fuel' rho tl with
      | Some hv, Some (PVList tvs) => Some (PVList (hv :: tvs))
      | _, _ => None
      end
  | PListMatch scrutinee nilcase hd tl conscase =>
      match peval fuel' rho scrutinee with
      | Some (PVList []) => peval fuel' rho nilcase
      | Some (PVList (hv :: tvs)) => peval fuel' ((hd, hv) :: (tl, PVList tvs) :: rho) conscase
      | _ => None
      end
  | PRecord k1 e1 k2 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some v1, Some v2 => Some (PVRecord k1 v1 k2 v2)
      | _, _ => None
      end
  | PField name e1 =>
      match peval fuel' rho e1 with
      | Some (PVRecord k1 v1 k2 v2) =>
          if String.eqb name k1 then Some v1
          else if String.eqb name k2 then Some v2
          else None
      | _ => None
      end
  | PInl e1 =>
      match peval fuel' rho e1 with
      | Some v1 => Some (PVInl v1)
      | None => None
      end
  | PInr e1 =>
      match peval fuel' rho e1 with
      | Some v1 => Some (PVInr v1)
      | None => None
      end
  | PCase scrutinee x1 case1 x2 case2 =>
      match peval fuel' rho scrutinee with
      | Some (PVInl v1) => peval fuel' ((x1, v1) :: rho) case1
      | Some (PVInr v2) => peval fuel' ((x2, v2) :: rho) case2
      | _ => None
      end
  | PStrConst s => Some (PVStr s)
  | PStrConcat e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVStr s1), Some (PVStr s2) => Some (PVStr (s1 ++ s2))
      | _, _ => None
      end
  | PStrEq e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVStr s1), Some (PVStr s2) => Some (PVBool (String.eqb s1 s2))
      | _, _ => None
      end
  | PRecordN fields =>
      match (fix peval_fields (fs : list (var * pyexpr)) : option (list (var * pyvalue)) :=
               match fs with
               | [] => Some []
               | (k, fe) :: rest =>
                   match peval fuel' rho fe, peval_fields rest with
                   | Some v, Some vs => Some ((k, v) :: vs)
                   | _, _ => None
                   end
               end) fields
      with
      | Some vs => Some (PVRecordN vs)
      | None => None
      end
  | PFieldN name e1 =>
      match peval fuel' rho e1 with
      | Some (PVRecordN fields) =>
          (fix lookup_field (fs : list (var * pyvalue)) : option pyvalue :=
             match fs with
             | [] => None
             | (k, v) :: rest => if String.eqb k name then Some v else lookup_field rest
             end) fields
      | _ => None
      end
  | PRecGroup fns =>
      Some (PVRecordN
        ((fix build_fields (gs : list (var * var * pyexpr)) : list (var * pyvalue) :=
            match gs with
            | [] => []
            | (f, p, b) :: rest => (f, PVClosureGroup fns rho f) :: build_fields rest
            end) fns))
  end
  end.
