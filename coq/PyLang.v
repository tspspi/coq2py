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

    [PArrConst]/[PArrGet]/[PArrSet]/[PVArr] are this file's half of
    [EArrConst]/[EArrGet]/[EArrSet]/[VArray] -- see Lang.v's header for
    the rationale and the explicit, bounded scope (McCarthy-style
    functional update, not real numpy aliasing/mutation/broadcasting).
    A straight 1:1 mirror, the same way every other construct here
    already is one.

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
  | PFOpp (e1 : pyexpr)
  | PFAbs (e1 : pyexpr)
  | PFSqrt (e1 : pyexpr)
  | PFMax (e1 e2 : pyexpr)
  | PFMin (e1 e2 : pyexpr)
  | PFExp (e1 : pyexpr)
  | PFLn (e1 : pyexpr)
  | PFPow (e1 e2 : pyexpr)
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
  | PRecGroup (fns : list (var * var * pyexpr))
  | PNone
  | PSome (e : pyexpr)
  | POptionMatch (scrutinee nonecase : pyexpr) (x : var) (somecase : pyexpr)
  | PArrConst (es : list pyexpr)
  | PArrGet (arr idx : pyexpr)
  | PArrSet (arr idx val : pyexpr)
  | PArrMap2 (x y : var) (body a b : pyexpr)
  | PArrLen (arr : pyexpr)
  | PArrSlice (arr lo hi : pyexpr)
  | PArrConcat (a b : pyexpr).

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
  | PVClosureGroup (fns : list (var * var * pyexpr)) (cenv : list (var * pyvalue)) (self_name : var)
  | PVNone
  | PVSome (v : pyvalue)
  | PVArr (vs : list pyvalue).

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

(** [Lang.as_array]/[Lang.broadcast2]'s target-side twins, for
    [PArrMap2] (see Lang.v's [EArrMap2] comment). *)
Definition pas_array (v : pyvalue) : option (list pyvalue) :=
  match v with
  | PVArr vs => Some vs
  | _ => None
  end.

Definition pbroadcast2 (va vb : pyvalue) : option (list (pyvalue * pyvalue)) :=
  match pas_array va, pas_array vb with
  | Some vs, Some ws =>
      if Nat.eqb (List.length vs) (List.length ws) then Some (combine vs ws)
      else match vs, ws with
           | [v], _ => Some (map (fun w => (v, w)) ws)
           | _, [w] => Some (map (fun v => (v, w)) vs)
           | _, _ => None
           end
  | Some vs, None => Some (map (fun v => (v, vb)) vs)
  | None, Some ws => Some (map (fun w => (va, w)) ws)
  | None, None => None
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
  | PFOpp e1 =>
      match peval fuel' rho e1 with
      | Some (PVFloat f1) => Some (PVFloat (PrimFloat.opp f1))
      | _ => None
      end
  | PFAbs e1 =>
      match peval fuel' rho e1 with
      | Some (PVFloat f1) => Some (PVFloat (PrimFloat.abs f1))
      | _ => None
      end
  | PFSqrt e1 =>
      match peval fuel' rho e1 with
      | Some (PVFloat f1) => Some (PVFloat (PrimFloat.sqrt f1))
      | _ => None
      end
  | PFMax e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) =>
          Some (PVFloat (if PrimFloat.ltb f1 f2 then f2 else f1))
      | _, _ => None
      end
  | PFMin e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) =>
          Some (PVFloat (if PrimFloat.ltb f2 f1 then f2 else f1))
      | _, _ => None
      end
  | PFExp e1 =>
      match peval fuel' rho e1 with
      | Some (PVFloat f1) => Some (PVFloat (prim_exp f1))
      | _ => None
      end
  | PFLn e1 =>
      match peval fuel' rho e1 with
      | Some (PVFloat f1) => Some (PVFloat (prim_ln f1))
      | _ => None
      end
  | PFPow e1 e2 =>
      match peval fuel' rho e1, peval fuel' rho e2 with
      | Some (PVFloat f1), Some (PVFloat f2) => Some (PVFloat (prim_pow f1 f2))
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
  | PNone => Some PVNone
  | PSome e1 =>
      match peval fuel' rho e1 with
      | Some v1 => Some (PVSome v1)
      | None => None
      end
  | POptionMatch scrutinee nonecase x somecase =>
      match peval fuel' rho scrutinee with
      | Some PVNone => peval fuel' rho nonecase
      | Some (PVSome v) => peval fuel' ((x, v) :: rho) somecase
      | _ => None
      end
  | PArrConst es =>
      match (fix peval_elts (l : list pyexpr) : option (list pyvalue) :=
               match l with
               | [] => Some []
               | e1 :: rest =>
                   match peval fuel' rho e1, peval_elts rest with
                   | Some v, Some vs => Some (v :: vs)
                   | _, _ => None
                   end
               end) es
      with
      | Some vs => Some (PVArr vs)
      | None => None
      end
  | PArrGet arr idx =>
      match peval fuel' rho arr, peval fuel' rho idx with
      | Some (PVArr vs), Some (PVZ i) =>
          if Z.leb 0 i then nth_error vs (Z.to_nat i) else None
      | _, _ => None
      end
  | PArrSet arr idx val =>
      match peval fuel' rho arr, peval fuel' rho idx, peval fuel' rho val with
      | Some (PVArr vs), Some (PVZ i), Some v =>
          if Z.leb 0 i then
            if Nat.ltb (Z.to_nat i) (List.length vs) then
              Some (PVArr (firstn (Z.to_nat i) vs ++ v :: skipn (S (Z.to_nat i)) vs))
            else None
          else None
      | _, _, _ => None
      end
  | PArrMap2 x y body a b =>
      match peval fuel' rho a, peval fuel' rho b with
      | Some va, Some vb =>
          match pbroadcast2 va vb with
          | Some ps =>
              match (fix peval_map2 (l : list (pyvalue * pyvalue)) : option (list pyvalue) :=
                       match l with
                       | [] => Some []
                       | (v1, v2) :: rest =>
                           match peval fuel' ((x, v1) :: (y, v2) :: rho) body, peval_map2 rest with
                           | Some v, Some vs => Some (v :: vs)
                           | _, _ => None
                           end
                       end) ps
              with
              | Some vs => Some (PVArr vs)
              | None => None
              end
          | None => None
          end
      | _, _ => None
      end
  | PArrLen arr =>
      match peval fuel' rho arr with
      | Some (PVArr vs) => Some (PVZ (Z.of_nat (List.length vs)))
      | _ => None
      end
  | PArrSlice arr lo hi =>
      match peval fuel' rho arr, peval fuel' rho lo, peval fuel' rho hi with
      | Some (PVArr vs), Some (PVZ zlo), Some (PVZ zhi) => Some (PVArr (slice_list zlo zhi vs))
      | _, _, _ => None
      end
  | PArrConcat a b =>
      match peval fuel' rho a, peval fuel' rho b with
      | Some (PVArr vs), Some (PVArr ws) => Some (PVArr (vs ++ ws))
      | _, _ => None
      end
  end
  end.
