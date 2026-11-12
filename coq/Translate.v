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
  | EApp func arg => PApp (translate func) (translate arg)
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
      | func arg ];                 (* EApp *)
    simpl.
    + (* EConst *) reflexivity.
    + (* EBool *) reflexivity.
    + (* EVar *) apply lookup_pyenv.
    + (* EAdd *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* ESub *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EMul *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EEq *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* ELt *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* ELe *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EAnd *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EOr *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* ENot *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|]; reflexivity.
    + (* EIf *) rewrite (IHfuel c rho).
      destruct (eval fuel' rho c) as [[z|b|v1 v2|f|s pr bd ce]|].
      * reflexivity.
      * destruct b; [apply (IHfuel e1 rho) | apply (IHfuel e2 rho)].
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + (* EPair *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1); destruct (eval fuel' rho e2); reflexivity.
    + (* EFst *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z|b|v1 v2|f|s pr bd ce]|]; reflexivity.
    + (* ESnd *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [[z|b|v1 v2|f|s pr bd ce]|]; reflexivity.
    + (* ELet *) rewrite (IHfuel e1 rho).
      destruct (eval fuel' rho e1) as [v1|].
      * exact (IHfuel e2 ((x, v1) :: rho)).
      * reflexivity.
    + (* EFConst *) reflexivity.
    + (* EFAdd *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EFSub *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EFMul *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EFDiv *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EFEq *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EFLt *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* EFLe *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|]; reflexivity.
    + (* ERepeat *) rewrite (IHfuel init rho).
      destruct (eval fuel' rho init) as [v0|].
      * apply (iterate_translate_correct fuel' n x body rho (fun rho' => IHfuel body rho') v0).
      * reflexivity.
    + (* EDiv *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|];
        try reflexivity; simpl; destruct (Z.eqb z2 0); reflexivity.
    + (* EMod *) rewrite (IHfuel e1 rho), (IHfuel e2 rho).
      destruct (eval fuel' rho e1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1]|];
        destruct (eval fuel' rho e2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2]|];
        try reflexivity; simpl; destruct (Z.eqb z2 0); reflexivity.
    + (* ELam *) reflexivity.
    + (* ERec *) reflexivity.
    + (* EApp *) rewrite (IHfuel func rho), (IHfuel arg rho).
      destruct (eval fuel' rho func) as [[z|b|v1 v2|f|self param body cenv]|];
        destruct (eval fuel' rho arg) as [argv|]; try reflexivity.
      simpl.
      destruct self as [fname|]; simpl.
      * exact (IHfuel body ((param, argv) :: (fname, VClosure (Some fname) param body cenv) :: cenv)).
      * exact (IHfuel body ((param, argv) :: cenv)).
Qed.
