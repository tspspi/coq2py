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
    in their own right.

    [translate_preserves_semantics] is now stated for an explicit, shared
    [fuel] (see Lang.v's header for why [eval]/[peval] need one at all),
    with the *same* fuel on both sides -- fuel is just a recursion-depth
    governor, not a cost model, so there is no reason source and target
    would ever need a different amount of it. The proof is by induction
    on [fuel] (not on [e], as it used to be): at [fuel = 0] both sides are
    [None] regardless of [e]; at [fuel = S fuel'], the induction
    hypothesis ([IHfuel : forall e rho, ...] at [fuel']) is exactly what's
    needed for every subexpression a case recurses into, including
    [EApp]'s -- whose closure body is not a syntactic subterm of the
    current [e] at all, which is precisely why induction on [e] no longer
    works here but induction on [fuel] still does. *)

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
  | EFConst f => PFConst f
  | EFAdd e1 e2 => PFAdd (translate e1) (translate e2)
  | EFSub e1 e2 => PFSub (translate e1) (translate e2)
  | EFMul e1 e2 => PFMul (translate e1) (translate e2)
  | EFDiv e1 e2 => PFDiv (translate e1) (translate e2)
  | EFEq e1 e2 => PFEq (translate e1) (translate e2)
  | EFLt e1 e2 => PFLt (translate e1) (translate e2)
  | EFLe e1 e2 => PFLe (translate e1) (translate e2)
  | ERepeat n x body init => PRepeat n x (translate body) (translate init)
  | EDiv e1 e2 => PDiv (translate e1) (translate e2)
  | EMod e1 e2 => PMod (translate e1) (translate e2)
  | ELam param body => PLam param (translate body)
  | ERec f param body => PRec f param (translate body)
  | ERecMut f1 param1 body1 f2 param2 body2 =>
      PRecMut f1 param1 (translate body1) f2 param2 (translate body2)
  | EApp func arg => PApp (translate func) (translate arg)
  | ENil => PNil
  | ECons hd tl => PCons (translate hd) (translate tl)
  | EListMatch scrutinee nilcase hd tl conscase =>
      PListMatch (translate scrutinee) (translate nilcase) hd tl (translate conscase)
  | ERecord k1 e1 k2 e2 => PRecord k1 (translate e1) k2 (translate e2)
  | EField name e1 => PField name (translate e1)
  | EInl e1 => PInl (translate e1)
  | EInr e1 => PInr (translate e1)
  | ECase scrutinee x1 case1 x2 case2 =>
      PCase (translate scrutinee) x1 (translate case1) x2 (translate case2)
  | EStrConst s => PStrConst s
  | EStrConcat e1 e2 => PStrConcat (translate e1) (translate e2)
  | EStrEq e1 e2 => PStrEq (translate e1) (translate e2)
  | ERecordN fields => PRecordN (map (fun kf => (fst kf, translate (snd kf))) fields)
  | EFieldN name e1 => PFieldN name (translate e1)
  | ERecGroup fns => PRecGroup (map (fun fpb => (fst fpb, translate (snd fpb))) fns)
  end.

(** [VClosure] embeds a captured [env], so translating a closure needs to
    translate that whole environment pointwise -- via [map], not a
    directly-named recursive call, which is what lets Coq's guardedness
    checker accept this as a single, ordinary [Fixpoint] on [value]
    (it tracks the recursive call on [snd p] as a subterm of [cenv],
    itself a subterm of the original [v], straight through [map]). *)
Fixpoint value_to_pyvalue (v : value) : pyvalue :=
  match v with
  | VZ z => PVZ z
  | VBool b => PVBool b
  | VPair v1 v2 => PVPair (value_to_pyvalue v1) (value_to_pyvalue v2)
  | VFloat f => PVFloat f
  | VClosure self param body cenv =>
      PVClosure self param (translate body)
        (map (fun p => (fst p, value_to_pyvalue (snd p))) cenv)
  | VList vs => PVList (map value_to_pyvalue vs)
  | VRecord k1 v1 k2 v2 => PVRecord k1 (value_to_pyvalue v1) k2 (value_to_pyvalue v2)
  | VClosureMut f1 param1 body1 f2 param2 body2 cenv which =>
      PVClosureMut f1 param1 (translate body1) f2 param2 (translate body2)
        (map (fun p => (fst p, value_to_pyvalue (snd p))) cenv) which
  | VInl v1 => PVInl (value_to_pyvalue v1)
  | VInr v1 => PVInr (value_to_pyvalue v1)
  | VStr s => PVStr s
  | VRecordN fields => PVRecordN (map (fun kf => (fst kf, value_to_pyvalue (snd kf))) fields)
  | VClosureGroup fns cenv self_name =>
      PVClosureGroup (map (fun fpb => (fst fpb, translate (snd fpb))) fns)
        (map (fun p => (fst p, value_to_pyvalue (snd p))) cenv) self_name
  end.

(** The same translation, lifted pointwise to a whole environment --
    deliberately *the same* [map] expression [value_to_pyvalue]'s
    [VClosure] case already uses (a plain [Definition], not its own
    hand-rolled [Fixpoint]), so that [env_to_pyenv cenv] and that
    [VClosure] case's own translated environment are definitionally
    (not just propositionally) the same term -- no separate bridging
    lemma needed anywhere a proof unfolds through a closure's captured
    environment. *)
Definition env_to_pyenv (rho : env) : pyenv :=
  map (fun p => (fst p, value_to_pyvalue (snd p))) rho.

Lemma lookup_pyenv :
  forall rho x, plookup (env_to_pyenv rho) x = option_map value_to_pyvalue (lookup rho x).
Proof.
  induction rho as [| [y v] rho' IH]; intro x; simpl.
  - reflexivity.
  - destruct (string_dec x y); [reflexivity | apply IH].
Qed.

(** [iterate]/[piterate] (Lang.v/PyLang.v) agree under translation,
    carrying forward whatever correctness [body] already has (at *every*
    environment, since each iteration extends [rho] with a fresh binding
    for [x]) through all [n] steps, at one fixed [fuel] shared throughout
    (iteration count and fuel are independent bounds -- [ERepeat] doesn't
    spend fuel per step). This is the one piece of real proof work
    [ERepeat] needs beyond the mechanical per-constructor cases below --
    an induction on the iteration count, not a new technique. *)
Lemma iterate_translate_correct :
  forall (fuel n : nat) (x : var) (body : expr) (rho : env),
    (forall rho', peval fuel (env_to_pyenv rho') (translate body) = option_map value_to_pyvalue (eval fuel rho' body)) ->
    forall v,
      piterate n (fun pv => peval fuel ((x, pv) :: env_to_pyenv rho) (translate body)) (value_to_pyvalue v)
      = option_map value_to_pyvalue (iterate n (fun v' => eval fuel ((x, v') :: rho) body) v).
Proof.
  intros fuel n; induction n as [| n' IH]; intros x body rho Hbody v; simpl.
  - reflexivity.
  - pose proof (Hbody ((x, v) :: rho)) as Hstep.
    simpl in Hstep.
    rewrite Hstep.
    destruct (eval fuel ((x, v) :: rho) body) as [v'|].
    + simpl. apply IH, Hbody.
    + reflexivity.
Qed.

(** Two reusable helpers for [ERecordN]/[EFieldN]'s proof cases below,
    each relating the *anonymous* nested [fix] [eval]/[peval] use for
    this constructor (see Lang.v's header for why it has to be
    anonymous and nested, not a named top-level mutually-recursive
    [Fixpoint]) by plain [induction] on the field list itself -- an
    ordinary list, not an [expr], so none of [Json.v]'s
    structural-induction-on-[expr] obstacle applies here at all; this
    file's proof was never blocked by it, since it already inducts on
    *fuel*, with [IHfuel] already a blanket fact usable for any
    sub-[expr], list-buried or not. *)
Lemma eval_fields_translate_correct :
  forall fuel' rho
    (Hbody : forall e, peval fuel' (env_to_pyenv rho) (translate e) = option_map value_to_pyvalue (eval fuel' rho e))
    (fields : list (var * expr)),
    (fix peval_fields (fs : list (var * pyexpr)) : option (list (var * pyvalue)) :=
       match fs with
       | [] => Some []
       | (k, fe) :: rest =>
           match peval fuel' (env_to_pyenv rho) fe, peval_fields rest with
           | Some v, Some vs => Some ((k, v) :: vs)
           | _, _ => None
           end
       end) (map (fun kf => (fst kf, translate (snd kf))) fields)
    = option_map (fun vs => map (fun kf => (fst kf, value_to_pyvalue (snd kf))) vs)
        ((fix eval_fields (fs : list (var * expr)) : option (list (var * value)) :=
            match fs with
            | [] => Some []
            | (k, fe) :: rest =>
                match eval fuel' rho fe, eval_fields rest with
                | Some v, Some vs => Some ((k, v) :: vs)
                | _, _ => None
                end
            end) fields).
Proof.
  intros fuel' rho Hbody fields.
  induction fields as [| [k fe] fields' IHfields].
  - reflexivity.
  - simpl.
    rewrite (Hbody fe).
    destruct (eval fuel' rho fe) as [v|]; simpl; [| reflexivity].
    rewrite IHfields.
    destruct ((fix eval_fields (fs : list (var * expr)) : option (list (var * value)) :=
                 match fs with
                 | [] => Some []
                 | (k0, fe0) :: rest =>
                     match eval fuel' rho fe0, eval_fields rest with
                     | Some v0, Some vs => Some ((k0, v0) :: vs)
                     | _, _ => None
                     end
                 end) fields') as [vs|]; reflexivity.
Qed.

Lemma lookup_fieldN_translate_correct :
  forall name (fields : list (var * value)),
    (fix lookup_field (fs : list (var * pyvalue)) : option pyvalue :=
       match fs with
       | [] => None
       | (k, v) :: rest => if String.eqb k name then Some v else lookup_field rest
       end) (map (fun kf => (fst kf, value_to_pyvalue (snd kf))) fields)
    = option_map value_to_pyvalue
        ((fix lookup_field (fs : list (var * value)) : option value :=
            match fs with
            | [] => None
            | (k, v) :: rest => if String.eqb k name then Some v else lookup_field rest
            end) fields).
Proof.
  intros name fields.
  induction fields as [| [k v] fields' IH].
  - reflexivity.
  - simpl. destruct (String.eqb k name); [reflexivity | exact IH].
Qed.

(** Three reusable helpers for [ERecGroup]/[EApp]'s [VClosureGroup]
    case below, the same category as the two above: each relates one
    of the *anonymous* nested [fix]es [eval]/[peval]/[ERecGroup]'s own
    construction use (see Lang.v's header on [ERecGroup] for why) by
    plain [induction] on the group's own [fns] list. *)
Lemma lookup_group_fn_translate_correct :
  forall name (fns : list (var * var * expr)),
    plookup_group_fn (map (fun fpb => (fst fpb, translate (snd fpb))) fns) name
    = option_map (fun pb => (fst pb, translate (snd pb))) (lookup_group_fn fns name).
Proof.
  intros name fns.
  induction fns as [| [[f p] b] fns' IH].
  - reflexivity.
  - simpl. destruct (string_dec f name); [reflexivity | exact IH].
Qed.

(** Builds the group's own [VRecordN] of [VClosureGroup]s -- the
    fix [ERecGroup]'s own [eval] case uses, with an empty base case
    (no captured environment to fall back to: this *is* the whole
    group, from scratch). *)
Lemma build_fields_translate_correct :
  forall (fns : list (var * var * expr)) (rho : env) (gs : list (var * var * expr)),
    (fix build_fields_py (gs' : list (var * var * pyexpr)) : list (var * pyvalue) :=
       match gs' with
       | [] => []
       | (f, p, b) :: rest =>
           (f, PVClosureGroup (map (fun fpb => (fst fpb, translate (snd fpb))) fns)
                 (map (fun p2 => (fst p2, value_to_pyvalue (snd p2))) rho) f)
           :: build_fields_py rest
       end) (map (fun fpb => (fst fpb, translate (snd fpb))) gs)
    = map (fun kf => (fst kf, value_to_pyvalue (snd kf)))
        ((fix build_fields (gs' : list (var * var * expr)) : list (var * value) :=
            match gs' with
            | [] => []
            | (f, p, b) :: rest => (f, VClosureGroup fns rho f) :: build_fields rest
            end) gs).
Proof.
  intros fns rho gs.
  induction gs as [| [[f p] b] gs' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Rebuilds every member's binding (itself included) into the
    callee's environment -- the fix [EApp]'s own [VClosureGroup] case
    uses, with the *captured* environment [cenv] as its base case
    (unlike [build_fields_translate_correct] above): a call keeps
    whatever was already in scope when the group was created. *)
Lemma build_bindings_translate_correct :
  forall (fns : list (var * var * expr)) (cenv : env) (gs : list (var * var * expr)),
    (fix build_bindings_py (gs' : list (var * var * pyexpr)) : pyenv :=
       match gs' with
       | [] => map (fun p2 => (fst p2, value_to_pyvalue (snd p2))) cenv
       | (f, p, b) :: rest =>
           (f, PVClosureGroup (map (fun fpb => (fst fpb, translate (snd fpb))) fns)
                 (map (fun p2 => (fst p2, value_to_pyvalue (snd p2))) cenv) f)
           :: build_bindings_py rest
       end) (map (fun fpb => (fst fpb, translate (snd fpb))) gs)
    = map (fun p2 => (fst p2, value_to_pyvalue (snd p2)))
        ((fix build_bindings (gs' : list (var * var * expr)) : env :=
            match gs' with
            | [] => cenv
            | (f, p, b) :: rest => (f, VClosureGroup fns cenv f) :: build_bindings rest
            end) gs).
Proof.
  intros fns cenv gs.
  induction gs as [| [[f p] b] gs' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** The correctness theorem: for every source term, environment, and
    amount of fuel, evaluating the translated Python AST under [peval]
    (against the pointwise-translated environment, with the *same*
    fuel) gives exactly the same answer (including "gets stuck", i.e.
    [None] -- running out of fuel is one more way to get stuck,
    alongside the wrong-shape-value and unbound-variable cases that
    already existed) as evaluating the source term under [eval], up to
    translating the resulting value. No side conditions, no restriction
    to well-formed or closed terms -- it holds unconditionally over this
    subset. *)
Theorem translate_preserves_semantics :
  forall (fuel : nat) (e : expr) (rho : env),
    peval fuel (env_to_pyenv rho) (translate e) = option_map value_to_pyvalue (eval fuel rho e).
Proof.
  induction fuel as [| fuel' IHfuel].
  - intros e rho. reflexivity.
  - intros e rho.
    destruct e as
      [ z                           (* EConst *)
      | b                           (* EBool *)
      | x                           (* EVar *)
      | e1 e2                       (* EAdd *)
      | e1 e2                       (* ESub *)
      | e1 e2                       (* EMul *)
      | e1 e2                       (* EEq *)
      | e1 e2                       (* ELt *)
      | e1 e2                       (* ELe *)
      | e1 e2                       (* EAnd *)
      | e1 e2                       (* EOr *)
      | e1                          (* ENot *)
      | c e1 e2                     (* EIf *)
      | e1 e2                       (* EPair *)
      | e1                          (* EFst *)
      | e1                          (* ESnd *)
      | x e1 e2                     (* ELet *)
      | f                           (* EFConst *)
      | e1 e2                       (* EFAdd *)
      | e1 e2                       (* EFSub *)
      | e1 e2                       (* EFMul *)
      | e1 e2                       (* EFDiv *)
      | e1 e2                       (* EFEq *)
      | e1 e2                       (* EFLt *)
      | e1 e2                       (* EFLe *)
      | n x body init               (* ERepeat *)
      | e1 e2                       (* EDiv *)
      | e1 e2                       (* EMod *)
      | param body                  (* ELam *)
      | f param body                (* ERec *)
      | f1 param1 body1 f2 param2 body2 (* ERecMut *)
      | func arg                    (* EApp *)
      |                             (* ENil *)
      | hd tl                       (* ECons *)
      | scrutinee nilcase hd tl conscase (* EListMatch *)
      | k1 e1 k2 e2                 (* ERecord *)
      | name e1                     (* EField *)
      | e1                          (* EInl *)
      | e1                          (* EInr *)
      | scrutinee x1 case1 x2 case2 (* ECase *)
      | s                           (* EStrConst *)
      | e1 e2                       (* EStrConcat *)
      | e1 e2                       (* EStrEq *)
      | fields                      (* ERecordN *)
      | name e1                     (* EFieldN *)
      | fns ];                      (* ERecGroup *)
    simpl.
    + (* EConst *) reflexivity.
    + (* EBool *) reflexivity.
    + (* EVar *) apply lookup_pyenv.
    + (* EAdd *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* ESub *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EMul *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EEq *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* ELt *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* ELe *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EAnd *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EOr *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* ENot *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|]; reflexivity.
    + (* EIf *) rewrite (IHfuel c rho).
      destruct (eval fuel' rho c) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|].
      * reflexivity.
      * destruct b; [apply (IHfuel e1 rho) | apply (IHfuel e2 rho)].
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + (* EPair *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1); destruct (eval fuel' rho e2); reflexivity.
    + (* EFst *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|]; reflexivity.
    + (* ESnd *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|]; reflexivity.
    + (* ELet *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [v1|].
      * exact (IHfuel e2 ((x, v1) :: rho)).
      * reflexivity.
    + (* EFConst *) reflexivity.
    + (* EFAdd *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EFSub *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EFMul *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EFDiv *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EFEq *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EFLt *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* EFLe *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* ERepeat *) rewrite (IHfuel init rho).
      destruct (eval fuel' rho init) as [v0|].
      * apply (iterate_translate_correct fuel' n x body rho (fun rho' => IHfuel body rho') v0).
      * reflexivity.
    + (* EDiv *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|];
        try reflexivity; simpl; destruct (Z.eqb z2 0); reflexivity.
    + (* EMod *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|];
        try reflexivity; simpl; destruct (Z.eqb z2 0); reflexivity.
    + (* ELam *) reflexivity.
    + (* ERec *) reflexivity.
    + (* ERecMut *) reflexivity.
    + (* EApp *) rewrite (IHfuel func rho), (IHfuel arg rho).
      destruct (eval fuel' rho func) as [[z|b|v1 v2|f|self param body cenv|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|];
        destruct (eval fuel' rho arg) as [argv|]; try reflexivity.
      * simpl.
        destruct self as [fname|]; simpl.
        -- exact (IHfuel body ((param, argv) :: (fname, VClosure (Some fname) param body cenv) :: cenv)).
        -- exact (IHfuel body ((param, argv) :: cenv)).
      * simpl.
        destruct cw; simpl.
        -- exact (IHfuel cb2
             ((cp2, argv)
              :: (cf1, VClosureMut cf1 cp1 cb1 cf2 cp2 cb2 cce false)
              :: (cf2, VClosureMut cf1 cp1 cb1 cf2 cp2 cb2 cce true)
              :: cce)).
        -- exact (IHfuel cb1
             ((cp1, argv)
              :: (cf1, VClosureMut cf1 cp1 cb1 cf2 cp2 cb2 cce false)
              :: (cf2, VClosureMut cf1 cp1 cb1 cf2 cp2 cb2 cce true)
              :: cce)).
      * simpl.
        rewrite (lookup_group_fn_translate_correct cgc cga).
        destruct (lookup_group_fn cga cgc) as [[param body]|]; simpl; [| reflexivity].
        rewrite (build_bindings_translate_correct cga cgb cga).
        apply (IHfuel body ((param, argv) ::
          (fix build_bindings (gs : list (var * var * expr)) : env :=
             match gs with
             | [] => cgb
             | (f, p, b) :: rest => (f, VClosureGroup cga cgb f) :: build_bindings rest
             end) cga)).
    + (* ENil *) reflexivity.
    + (* ECons *) rewrite (IHfuel hd rho), (IHfuel tl rho).
      destruct (eval fuel' rho hd) as [hv|];
        destruct (eval fuel' rho tl) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|]; reflexivity.
    + (* EListMatch *) rewrite (IHfuel scrutinee rho).
      destruct (eval fuel' rho scrutinee) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|]; try reflexivity.
      destruct vs as [| hv tvs]; simpl.
      * apply (IHfuel nilcase rho).
      * exact (IHfuel conscase ((hd, hv) :: (tl, VList tvs) :: rho)).
    + (* ERecord *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1); destruct (eval fuel' rho e2); reflexivity.
    + (* EField *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|]; try reflexivity.
      simpl. destruct (String.eqb name rk1), (String.eqb name rk2); reflexivity.
    + (* EInl *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1); reflexivity.
    + (* EInr *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1); reflexivity.
    + (* ECase *) rewrite (IHfuel scrutinee rho).
      destruct (eval fuel' rho scrutinee) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|]; try reflexivity.
      * exact (IHfuel case1 ((x1, iv1) :: rho)).
      * exact (IHfuel case2 ((x2, iv2) :: rho)).
    + (* EStrConst *) reflexivity.
    + (* EStrConcat *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
        + (* EStrEq *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|rn1|cg1a cg1b cg1c]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|rn2|cg2a cg2b cg2c]|]; reflexivity.
    + (* ERecordN *) simpl.
      rewrite (eval_fields_translate_correct fuel' rho (fun e => IHfuel e rho) fields).
      destruct ((fix eval_fields (fs : list (var * expr)) : option (list (var * value)) :=
                   match fs with
                   | [] => Some []
                   | (k, fe) :: rest =>
                       match eval fuel' rho fe, eval_fields rest with
                       | Some v, Some vs => Some ((k, v) :: vs)
                       | _, _ => None
                       end
                   end) fields) as [vs|]; reflexivity.
    + (* EFieldN *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z|b|v1 v2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|rn|cga cgb cgc]|]; try reflexivity.
      simpl. apply (lookup_fieldN_translate_correct name rn).
    + (* ERecGroup *) simpl. unfold env_to_pyenv.
      rewrite (build_fields_translate_correct fns rho fns).
      reflexivity.
Qed.
