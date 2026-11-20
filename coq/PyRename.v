(** PyRename.v

    A genuine correctness bug, found by inspection and confirmed by
    actually running the generated Python (see the empirical check this
    file's commit message/roadmap entry points to): [PyPrint.v] renders
    every let/recursion/pattern-match binder with Python's walrus
    operator writing into the *one shared* enclosing function scope
    ([(x := e1), e2)[1]], etc). That is fine in isolation, but [peval]
    (PyLang.v) models closures as capturing an *immutable snapshot* of
    the environment at creation time -- standard, alias-free big-step
    semantics -- while a walrus assignment mutates a *shared* Python
    variable slot. If two sibling bindings in the same Python scope
    reuse the same name, and a closure created under the first one
    escapes (is returned, stored in a pair/record) past the point where
    the second rebinds that name, the escaped closure's free reference
    resolves -- at call time, under real Python's late-binding closure
    rule -- against whatever the *second* binding left behind, not the
    first. Concretely, the generated Python for
    [ELet "x" (EConst 1) (EPair (ELam "y" (EAdd (EVar "x") (EVar "y")))
                                (ELet "x" (EConst 2) (EConst 0)))]
    returns a closure that computes [x + y] against the *second* [x],
    not the first -- [peval]'s own formal semantics says the opposite.
    This is not "the printer is merely unpretty"; it is a place where
    text formatting silently changes what the program computes, exactly
    the class of bug docs/duality.md says this project does not accept
    silently for a Coq-to-Python transformation.

    The fix is the standard one: alpha-rename every binder in the
    [pyexpr] tree to a fresh, globally-unique name *before* printing, so
    no two distinct logical bindings anywhere in one generated function
    body ever share a Python identifier -- then no walrus assignment can
    ever be reached twice for "the same slot, two different meanings",
    because each generated name is assigned exactly once in the entire
    program text. [rename_pyexpr] is that pass; [PyPrint.v] now calls it
    before printing instead of printing original source names directly.

    One deliberate, narrow exception: a [PRecGroup] member's own name
    is *not* renamed (see that case's own comment below) -- it doubles
    as the [PVRecordN]-style dict key [EFieldN]/[PFieldN] looks a
    member up by from *outside* the group (confirmed live in
    [examples/Kinematics.v]'s [bounce3_expr], called via [EApp
    (EFieldN "fall" bounce3_expr) ...], a literal string that is never
    itself renamed), so renaming it would break that external lookup
    without fixing anything the general scheme doesn't already cover
    (a group's own members never collide with each other, and rarely
    with anything else -- found and fixed during an earlier, now-
    reverted attempt to rename them too, which broke exactly this).

    Unlike [PyPrint.v]'s character-level formatting, *this* transform
    does change the [pyexpr] term (every bound name but the
    [PRecGroup] exception above is rewritten), so in principle it
    deserves the same kind of theorem the rest of the pipeline gets:
    a [rename_pyexpr_correct] proving it does not change what [peval]
    computes. That theorem is *not yet complete* -- 44 of [pyexpr]'s
    46 constructors are proved (everything except [PRecGroup] and the
    matching [PVClosureGroup] case inside [PApp]) -- tracked as this
    file's own next step, not committed here since an incomplete
    [Admitted] theorem is a different, messier kind of trust boundary
    than this project otherwise uses. In the meantime, correctness of
    the *renaming itself* for the 44 proven shapes, plus the concrete
    before/after counterexample above and the full test suite
    (including [bounce3]'s own by-name field access), is the evidence
    this fix is actually correct. What will still *not* be proved even
    once that theorem is finished -- the same, smaller residual
    boundary [PyPrint.v]'s header describes -- is that printing the
    renamed tree as Python text, and running that text under real
    CPython, matches [peval].

    All the supporting infrastructure for the remaining two cases is
    now landed: [PRecGroup]'s own construction needs *no* new
    [env_corr] machinery at all -- building a [PVRecordN] of
    [PVClosureGroup]s from [fns]/[fns'] only needs the *ambient*
    [env_corr n env cenv cenv'] already in scope, applied once per
    member via [vcorr_recordn]/[vcorr_closuregroup], since constructing
    the value never evaluates a member's body. The real gap was
    [PApp]'s reconstruction step: applying a [PVClosureGroup] rebuilds
    *every* member's own binding (each name [f_i], deliberately
    unrenamed) into the callee's environment before evaluating the
    matched body, and relating that reconstructed environment on both
    sides needed [env_corr] to accept a "same name on both sides" push
    for each [f_i] -- exactly what an earlier, abandoned [ec_cons_same]
    attempt tried, and what [ec_cons_group] now *is*: re-examining why
    that attempt stalled ([env_corr_rho'_absent]/[env_corr_lookup] lean
    on every [rho']-side name being *of the [fresh_name] shape*, via
    [fresh_name_injective], to rule out collisions, which a pushed
    literal [f_i] isn't) showed the fix needs only a single, *local*
    side condition carried right in the new constructor -- [f_i] is
    never of the [fresh_name] shape -- not a blanket axiom, and
    critically *not* a hypothesis threaded through the whole induction:
    because [ec_cons_group]'s pushed renamed-side name always *equals*
    its own original-side key, a lookup for any *other*, already-
    in-scope name [x <> f_i] can be shown to avoid colliding with
    [f_i] using nothing but [x <> f_i] itself (if [x] resolves to
    another [ec_cons_group] entry, its renamed name is just [x] again,
    by the same identity property) or the one local side condition (if
    [x] resolves to an ordinary [fresh_name k]) -- no "two different
    groups never share a member name" assumption is needed either,
    unlike an earlier worry. [env_corr_weaken]/[env_corr_rho'_absent]/
    [env_corr_lookup] (plus a new helper, [rename_lookup_shape]) are
    updated for this one more constructor, fully proved. [recgroup_
    rebuild_corr] is the lemma connecting [PApp]'s actual reconstructed
    environment to [rename_pyexpr]'s own [PRecGroup] case's [fns]/
    [fns'] pairing -- proved with no seed/fuel bookkeeping at all,
    simpler than [rename_pyexpr_monotone]'s own [PRecGroup] case,
    since [ec_cons_group] never consumes a fresh seed, so the group's
    *entire* env-correspondence lives at one constant bound. All fully
    proved (no axioms beyond the pre-existing [PrimFloat.float]), under
    one explicit, checkable hypothesis ([group_names_ok fns]: no
    member's own name is of the [fresh_name] shape -- trivial for every
    concrete group this project runs, e.g. ["fall"]/["rise"]/
    ["report"]; a source program that deliberately named a member [v7]
    would fail it, which is the honest outcome for that case, not a
    silent wrong answer).

    What's still not done: actually *using* [recgroup_rebuild_corr]
    inside [rename_pyexpr_correct]'s own [PRecGroup]/[PVClosureGroup]
    cases to retire their [admit.]s, and deciding where [group_names_ok]
    itself becomes a hypothesis of (something built on top of)
    [rename_pyexpr_correct] -- it cannot be discharged unconditionally
    for an arbitrary [e] inside that theorem's own induction, so it has
    to enter *somewhere* explicit, most likely as a side condition on
    the top-level corollary this fix's actual callers (e.g. [PyPrint.
    rename_function]) would use, not threaded through every one of the
    44 already-proved cases' hypotheses. *)

From Coq Require Import ZArith String List Bool Lia.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Json. (* reuses z_to_string/z_of_string/z_round_trip *)
Open Scope string_scope.
Open Scope nat_scope.

(* ------------------------------------------------------------------ *)
(** * Fresh names *)

Definition nat_to_string (n : nat) : string := z_to_string (Z.of_nat n).

Lemma nat_to_string_injective : forall n1 n2,
  nat_to_string n1 = nat_to_string n2 -> n1 = n2.
Proof.
  intros n1 n2 H. unfold nat_to_string in H.
  assert (Hz : z_of_string (z_to_string (Z.of_nat n1)) = z_of_string (z_to_string (Z.of_nat n2)))
    by (rewrite H; reflexivity).
  rewrite !z_round_trip in Hz.
  injection Hz as Hz.
  apply Nat2Z.inj. exact Hz.
Qed.

(** Every fresh name starts with ["v"], a character no digit is, so two
    fresh names collide only if their [nat] seeds do. *)
Definition fresh_name (n : nat) : var := "v" ++ nat_to_string n.

Lemma fresh_name_injective : forall n1 n2, fresh_name n1 = fresh_name n2 -> n1 = n2.
Proof.
  intros n1 n2 H. unfold fresh_name in H.
  apply nat_to_string_injective.
  injection H as H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(** * The renaming environment *)

Fixpoint rename_lookup (env : list (var * var)) (x : var) : var :=
  match env with
  | [] => x
  | (k, v) :: rest => if string_dec x k then v else rename_lookup rest x
  end.

(* ------------------------------------------------------------------ *)
(** * The renaming pass itself

    [rename_pyexpr env n e] returns the alpha-renamed term together with
    the next unused fresh-name seed. Every binder -- including [PLam]'s
    own parameter, which is perfectly safe as real Python function-call
    scoping -- is renamed uniformly, with no "safe vs risky" special
    case: this is both simpler to state and simpler to get right than
    trying to prove exactly which binders are safe to leave alone. *)

(** [PRecordN]'s fields and [PRecGroup]'s members are each walked by an
    *inlined, anonymous* [fix] inside [rename_pyexpr]'s own case below,
    not a named top-level sibling: Coq's structural guard checker cannot
    verify a named, separately-defined list helper that calls back into
    [rename_pyexpr] (even passed in as a plain higher-order parameter --
    tried, and rejected, since the checker cannot see, from inside
    [rename_pyexpr]'s own body, that a value the helper will *later*
    apply it to is still a subterm of the original argument). Inlining
    the [fix] directly inside the branch keeps [fields]/[fns] -- already
    known, at that point, to be subterms of [e] -- visibly in scope for
    the checker, the same fix [Lang.v]'s own [ERecordN]/[ERecGroup]
    [eval] cases already use. The main correctness proof below handles
    these two cases with a plain list [induction] over [fields]/[fns]
    directly, not a named lemma about this [fix] -- induction is on
    [fuel], not on [pyexpr]'s structure, so [IHfuel'] already applies to
    every field/member's own (arbitrarily nested) body regardless of it
    sitting inside a [list], without needing the strong/size-based
    induction [Json.v] needs for its (structurally-induction-only)
    parser roundtrip. *)

Fixpoint rename_pyexpr (env : list (var * var)) (n : nat) (e : pyexpr) {struct e} : pyexpr * nat :=
  match e with
  | PConst z => (PConst z, n)
  | PBool b => (PBool b, n)
  | PVar x => (PVar (rename_lookup env x), n)
  | PAdd e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PAdd e1' e2', n2)
  | PSub e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PSub e1' e2', n2)
  | PMul e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PMul e1' e2', n2)
  | PEq e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PEq e1' e2', n2)
  | PLt e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PLt e1' e2', n2)
  | PLe e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PLe e1' e2', n2)
  | PAnd e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PAnd e1' e2', n2)
  | POr e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (POr e1' e2', n2)
  | PNot e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      (PNot e1', n1)
  | PIf c e1 e2 =>
      let '(c', n0) := rename_pyexpr env n c in
      let '(e1', n1) := rename_pyexpr env n0 e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PIf c' e1' e2', n2)
  | PPair e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PPair e1' e2', n2)
  | PFst e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in (PFst e1', n1)
  | PSnd e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in (PSnd e1', n1)
  | PLet x e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let y := fresh_name n1 in
      let '(e2', n2) := rename_pyexpr ((x, y) :: env) (S n1) e2 in
      (PLet y e1' e2', n2)
  | PFConst f => (PFConst f, n)
  | PFAdd e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFAdd e1' e2', n2)
  | PFSub e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFSub e1' e2', n2)
  | PFMul e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFMul e1' e2', n2)
  | PFDiv e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFDiv e1' e2', n2)
  | PFEq e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFEq e1' e2', n2)
  | PFLt e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFLt e1' e2', n2)
  | PFLe e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFLe e1' e2', n2)
  | PRepeat k x body init =>
      let '(init', n1) := rename_pyexpr env n init in
      let y := fresh_name n1 in
      let '(body', n2) := rename_pyexpr ((x, y) :: env) (S n1) body in
      (PRepeat k y body' init', n2)
  | PDiv e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PDiv e1' e2', n2)
  | PMod e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PMod e1' e2', n2)
  | PLam param body =>
      let yparam := fresh_name n in
      let '(body', n1) := rename_pyexpr ((param, yparam) :: env) (S n) body in
      (PLam yparam body', n1)
  | PRec f param body =>
      let yf := fresh_name n in
      let yparam := fresh_name (S n) in
      let '(body', n1) := rename_pyexpr ((param, yparam) :: (f, yf) :: env) (S (S n)) body in
      (PRec yf yparam body', n1)
  | PRecMut f1 param1 body1 f2 param2 body2 =>
      let yf2 := fresh_name n in
      let yf1 := fresh_name (S n) in
      let yparam1 := fresh_name (S (S n)) in
      let yparam2 := fresh_name (S (S (S n))) in
      let envfs := (f1, yf1) :: (f2, yf2) :: env in
      let '(body1', n1) := rename_pyexpr ((param1, yparam1) :: envfs) (S (S (S (S n)))) body1 in
      let '(body2', n2) := rename_pyexpr ((param2, yparam2) :: envfs) n1 body2 in
      (PRecMut yf1 yparam1 body1' yf2 yparam2 body2', n2)
  | PApp func arg =>
      let '(func', n1) := rename_pyexpr env n func in
      let '(arg', n2) := rename_pyexpr env n1 arg in
      (PApp func' arg', n2)
  | PNil => (PNil, n)
  | PCons hd tl =>
      let '(hd', n1) := rename_pyexpr env n hd in
      let '(tl', n2) := rename_pyexpr env n1 tl in
      (PCons hd' tl', n2)
  | PListMatch scrutinee nilcase hd tl conscase =>
      let '(scrutinee', n0) := rename_pyexpr env n scrutinee in
      let '(nilcase', n1) := rename_pyexpr env n0 nilcase in
      let ytl := fresh_name n1 in
      let yhd := fresh_name (S n1) in
      let '(conscase', n2) := rename_pyexpr ((hd, yhd) :: (tl, ytl) :: env) (S (S n1)) conscase in
      (PListMatch scrutinee' nilcase' yhd ytl conscase', n2)
  | PRecord k1 e1 k2 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PRecord k1 e1' k2 e2', n2)
  | PField name e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in (PField name e1', n1)
  | PInl e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in (PInl e1', n1)
  | PInr e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in (PInr e1', n1)
  | PCase scrutinee x1 case1 x2 case2 =>
      let '(scrutinee', n0) := rename_pyexpr env n scrutinee in
      let y1 := fresh_name n0 in
      let '(case1', n1) := rename_pyexpr ((x1, y1) :: env) (S n0) case1 in
      let y2 := fresh_name n1 in
      let '(case2', n2) := rename_pyexpr ((x2, y2) :: env) (S n1) case2 in
      (PCase scrutinee' y1 case1' y2 case2', n2)
  | PStrConst s => (PStrConst s, n)
  | PStrConcat e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PStrConcat e1' e2', n2)
  | PStrEq e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PStrEq e1' e2', n2)
  | PRecordN fields =>
      let '(fields', n1) :=
        (fix go (fs : list (var * pyexpr)) (n : nat) : list (var * pyexpr) * nat :=
           match fs with
           | [] => ([], n)
           | (k, fe) :: rest =>
               let '(fe', n0) := rename_pyexpr env n fe in
               let '(rest', n2) := go rest n0 in
               ((k, fe') :: rest', n2)
           end) fields n
      in
      (PRecordN fields', n1)
  | PFieldN name e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in (PFieldN name e1', n1)
  | PRecGroup fns =>
      (** Deliberately *not* renamed: a group member's own name doubles as
          the [PVRecordN]-style dict key [EFieldN]/[PFieldN] looks a member
          up by (confirmed live in [examples/Kinematics.v]'s [bounce3_expr],
          called via [EApp (EFieldN "fall" bounce3_expr) ...] -- a *literal*
          string, never itself renamed, the same way an ordinary record's
          own field names never are) *and* the Python walrus variable
          [PyPrint.v] binds it to, so renaming it would have to change both
          consistently -- but the dict key specifically must stay exactly
          what external [EFieldN] lookups already expect, so it cannot
          change at all. Every *other* binder a member introduces (its own
          parameter, and anything inside its body) is still renamed
          normally; this is a narrowly-scoped, explicitly accepted
          exception, not a gap in the fix -- see [PyRename.v]'s header. *)
      let envfs := map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns in
      let env' := List.app envfs env in
      let '(fns', n2) :=
        (fix go (fs : list (var * var * pyexpr)) (n : nat) : list (var * var * pyexpr) * nat :=
           match fs with
           | [] => ([], n)
           | (f, p, b) :: rest =>
               let yp := fresh_name n in
               let '(b', n0) := rename_pyexpr ((p, yp) :: env') (S n) b in
               let '(rest', n2) := go rest n0 in
               ((f, yp, b') :: rest', n2)
           end) fns n
      in
      (PRecGroup fns', n2)
  end.

(* ------------------------------------------------------------------ *)
(** * The renaming counter never goes backwards

    Needed below to show every fresh name [rename_pyexpr] ever hands
    out is actually fresh: each binder consumes the *current* counter
    and passes a strictly larger one to everything printed after it,
    so two different binders anywhere in one call are never assigned
    the same seed.

    Proved by *strong induction on [pyexpr_size e]*
    ([well_founded_induction lt_wf]), mirroring [Json.v]'s own
    [parse_print_roundtrip] proof technique (see that file's header):
    plain structural [induction e] cannot reach a sub-[pyexpr] buried
    inside [PRecordN]/[PRecGroup]'s own [list] field. [PRecGroup] needs
    the strong form specifically (not the anonymous-[fix]-plus-
    [induction on the list] shortcut [rename_pyexpr] itself uses above):
    its body-renaming pass threads a *shared* [envfs]/[env'], computed
    once for the whole member list, through every member -- a plain
    [induction fns] would instead hand back an induction hypothesis
    that *recomputes* [envfs] fresh for just the tail, which is not the
    fact being used. A strong, size-indexed hypothesis lets the
    [Hbodies] helper below carry [envfs]/[env'] as ordinary, externally
    fixed parameters instead, with no such mismatch. *)

Fixpoint pyexpr_size (e : pyexpr) : nat :=
  match e with
  | PConst _ | PBool _ | PVar _ | PNil | PFConst _ | PStrConst _ => 1
  | PNot e1 | PFst e1 | PSnd e1 | PField _ e1 | PInl e1 | PInr e1 | PFieldN _ e1 =>
      S (pyexpr_size e1)
  | PAdd e1 e2 | PSub e1 e2 | PMul e1 e2 | PEq e1 e2 | PLt e1 e2 | PLe e1 e2
  | PAnd e1 e2 | POr e1 e2 | PPair e1 e2 | PFAdd e1 e2 | PFSub e1 e2 | PFMul e1 e2
  | PFDiv e1 e2 | PFEq e1 e2 | PFLt e1 e2 | PFLe e1 e2 | PDiv e1 e2 | PMod e1 e2
  | PApp e1 e2 | PCons e1 e2 | PStrConcat e1 e2 | PStrEq e1 e2
  | PLet _ e1 e2 | PRecord _ e1 _ e2 =>
      S (pyexpr_size e1 + pyexpr_size e2)
  | PIf c e1 e2 => S (pyexpr_size c + pyexpr_size e1 + pyexpr_size e2)
  | PRepeat _ _ body init => S (pyexpr_size body + pyexpr_size init)
  | PLam _ body => S (pyexpr_size body)
  | PRec _ _ body => S (pyexpr_size body)
  | PRecMut _ _ body1 _ _ body2 => S (pyexpr_size body1 + pyexpr_size body2)
  | PListMatch sc nc _ _ cc => S (pyexpr_size sc + pyexpr_size nc + pyexpr_size cc)
  | PCase sc _ c1 _ c2 => S (pyexpr_size sc + pyexpr_size c1 + pyexpr_size c2)
  | PRecordN fields => S (fold_right (fun kv acc => pyexpr_size (snd kv) + acc) 0 fields)
  | PRecGroup fns => S (fold_right (fun fpb acc => pyexpr_size (snd fpb) + acc) 0 fns)
  end.

Lemma pyexpr_size_in_fields :
  forall k fe fields, In (k, fe) fields -> pyexpr_size fe < pyexpr_size (PRecordN fields).
Proof.
  intros k fe fields Hin.
  induction fields as [| [k0 fe0] rest IH]; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + injection Heq as -> ->. simpl. lia.
    + specialize (IH Hin). simpl in IH |- *. lia.
Qed.

Lemma pyexpr_size_in_fns :
  forall f p b fns, In (f, p, b) fns -> pyexpr_size b < pyexpr_size (PRecGroup fns).
Proof.
  intros f p b fns Hin.
  induction fns as [| [[f0 p0] b0] rest IH]; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + injection Heq as -> -> ->. simpl. lia.
    + specialize (IH Hin). simpl in IH |- *. lia.
Qed.

Lemma rename_pyexpr_monotone : forall e env n, n <= snd (rename_pyexpr env n e).
Proof.
  assert (Hstrong : forall sz e, pyexpr_size e <= sz -> forall env n, n <= snd (rename_pyexpr env n e)).
  { induction sz as [sz IHsz] using (well_founded_induction lt_wf).
    intros e Hsz env n.
    destruct e as
      [ z | b | x | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1
      | c e1 e2 | e1 e2 | e1 | e1 | x e1 e2 | fl | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2
      | e1 e2 | e1 e2 | k x body init | e1 e2 | e1 e2 | param body | f param body
      | f1 param1 body1 f2 param2 body2 | func arg | | hd tl
      | scrutinee nilcase hd tl conscase | k1 e1 k2 e2 | name e1 | e1 | e1
      | scrutinee x1 case1 x2 case2 | s | e1 e2 | e1 e2 | fields | name e1 | fns ];
      simpl in Hsz; simpl;
      try (
        repeat match goal with
        | |- context [ rename_pyexpr ?env0 ?n0 ?xx ] =>
            let Hlt := fresh "Hlt" in
            let H := fresh "H" in
            assert (Hlt : pyexpr_size xx < sz) by lia;
            pose proof (IHsz (pyexpr_size xx) Hlt xx (le_n _) env0 n0) as H;
            destruct (rename_pyexpr env0 n0 xx) as [? ?] eqn:?;
            simpl in H; simpl
        end;
        lia).
    - (* PRecordN fields *)
      revert Hsz n.
      induction fields as [| [k fe] fields' IHfields]; intros Hsz n; simpl in Hsz; simpl.
      + lia.
      + assert (Hfe_lt : pyexpr_size fe < sz) by lia.
        assert (Htail : pyexpr_size (PRecordN fields') <= sz) by (simpl; lia).
        pose proof (IHsz (pyexpr_size fe) Hfe_lt fe (le_n _) env n) as Hfe.
        destruct (rename_pyexpr env n fe) as [fe' n0] eqn:Efe. simpl in Hfe.
        specialize (IHfields Htail n0).
        destruct ((fix go (fs : list (var * pyexpr)) (n1 : nat) : list (var * pyexpr) * nat :=
                     match fs with
                     | [] => ([], n1)
                     | (k0, fe0) :: rest =>
                         let '(fe'0, n2) := rename_pyexpr env n1 fe0 in
                         let '(rest', n3) := go rest n2 in
                         ((k0, fe'0) :: rest', n3)
                     end) fields' n0) as [fields'' n1] eqn:Efields'.
        simpl in IHfields. simpl. lia.
    - (* PRecGroup fns *)
      assert (Hbodies : forall env' fs,
                (forall f p b, In (f, p, b) fs -> In (f, p, b) fns) ->
                forall n0,
                n0 <= snd ((fix go (fs0 : list (var * var * pyexpr)) (n1 : nat)
                                : list (var * var * pyexpr) * nat :=
                              match fs0 with
                              | [] => ([], n1)
                              | (f0, p0, b0) :: rest =>
                                  let yp0 := fresh_name n1 in
                                  let '(b'0, n2) := rename_pyexpr ((p0, yp0) :: env') (S n1) b0 in
                                  let '(rest', n3) := go rest n2 in
                                  ((f0, yp0, b'0) :: rest', n3)
                              end) fs n0)).
      { intros env' fs.
        induction fs as [| [[f p] b] fs' IHfs]; intros Hsub n0; simpl.
        - lia.
        - assert (Hb_in : In (f, p, b) fns) by (apply Hsub; left; reflexivity).
          assert (Hb_lt : pyexpr_size b < sz) by
            (pose proof (pyexpr_size_in_fns f p b fns Hb_in) as Hlt0; simpl in Hlt0; lia).
          pose proof (IHsz (pyexpr_size b) Hb_lt b (le_n _) ((p, fresh_name n0) :: env') (S n0)) as Hb.
          destruct (rename_pyexpr ((p, fresh_name n0) :: env') (S n0) b) as [b' n1] eqn:Eb.
          simpl in Hb.
          assert (Hsub' : forall f0 p0 b0, In (f0, p0, b0) fs' -> In (f0, p0, b0) fns)
            by (intros f0 p0 b0 Hin0; apply Hsub; right; exact Hin0).
          specialize (IHfs Hsub' n1).
          destruct ((fix go (fs0 : list (var * var * pyexpr)) (n2 : nat)
                         : list (var * var * pyexpr) * nat :=
                       match fs0 with
                       | [] => ([], n2)
                       | (f0, p0, b0) :: rest =>
                           let yp0 := fresh_name n2 in
                           let '(b'0, n3) := rename_pyexpr ((p0, yp0) :: env') (S n2) b0 in
                           let '(rest', n4) := go rest n3 in
                           ((f0, yp0, b'0) :: rest', n4)
                       end) fs' n1) as [fs'' n2] eqn:Efs'.
          simpl in IHfs. simpl. lia. }
      pose proof (Hbodies (List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env) fns
                    (fun f p b Hin => Hin) n) as Hb.
      destruct ((fix go (fs0 : list (var * var * pyexpr)) (n2 : nat)
                     : list (var * var * pyexpr) * nat :=
                   match fs0 with
                   | [] => ([], n2)
                   | (f0, p0, b0) :: rest =>
                       let yp0 := fresh_name n2 in
                       let '(b'0, n3) :=
                         rename_pyexpr ((p0, yp0) :: (List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env))
                           (S n2) b0 in
                       let '(rest', n4) := go rest n3 in
                       ((f0, yp0, b'0) :: rest', n4)
                   end) fns n) as [fns'' n2] eqn:Efns.
      simpl in Hb. simpl. lia.
  }
  intros e env n. apply (Hstrong (pyexpr_size e) e (le_n _) env n).
Qed.

(* ------------------------------------------------------------------ *)
(** * Correctness: renaming does not change what [peval] computes

    [value_corr v v'] / [env_corr n env rho rho'] are a joint logical
    relation: [env_corr] ties [env] (the renaming map), [rho] (the
    original environment) and [rho'] (the renamed one) together
    *structurally*, one entry at a time, in exactly the order
    [rename_pyexpr]'s own binders push them -- the [m < n] chain
    descends strictly with depth, so (via [fresh_name_injective]) no
    two entries anywhere in one [env_corr] derivation ever share a
    renamed name. [value_corr]'s closure cases carry their own
    captured [env]/[n] existentially, since different closures in one
    program are renamed under different (but each individually
    well-formed) accumulated bindings.

    [pyval_opt_corr] is intentionally *one-sided*: it only constrains
    the renamed side when the original [peval] actually succeeds, the
    same forward-simulation shape [translate_preserves_semantics] would
    have if stated for a possibly-stuck evaluator cast to this form.
    This sidesteps a genuine (if narrow) edge case for the *other*
    direction with no loss to what this theorem is for: nothing here
    needs "if the original gets stuck, so does the renamed one" (a
    stuck original already produced nothing to preserve), and proving
    it would require knowing no real source identifier ever collides,
    character for character, with a generated [fresh_name] -- a fact
    about the rest of the pipeline's naming conventions, not about
    [rename_pyexpr] itself. *)

Inductive value_corr : pyvalue -> pyvalue -> Prop :=
  | vcorr_z : forall z, value_corr (PVZ z) (PVZ z)
  | vcorr_bool : forall bb, value_corr (PVBool bb) (PVBool bb)
  | vcorr_float : forall ff, value_corr (PVFloat ff) (PVFloat ff)
  | vcorr_str : forall ss, value_corr (PVStr ss) (PVStr ss)
  | vcorr_pair : forall v1 v2 v1' v2',
      value_corr v1 v1' -> value_corr v2 v2' -> value_corr (PVPair v1 v2) (PVPair v1' v2')
  | vcorr_list : forall vs vs',
      Forall2 value_corr vs vs' -> value_corr (PVList vs) (PVList vs')
  | vcorr_inl : forall v v', value_corr v v' -> value_corr (PVInl v) (PVInl v')
  | vcorr_inr : forall v v', value_corr v v' -> value_corr (PVInr v) (PVInr v')
  | vcorr_record : forall k1 v1 k2 v2 v1' v2',
      value_corr v1 v1' -> value_corr v2 v2' ->
      value_corr (PVRecord k1 v1 k2 v2) (PVRecord k1 v1' k2 v2')
  | vcorr_recordn : forall fs fs',
      Forall2 (fun kv kv' => fst kv = fst kv' /\ value_corr (snd kv) (snd kv')) fs fs' ->
      value_corr (PVRecordN fs) (PVRecordN fs')
  | vcorr_closure_lam : forall param body cenv env n yparam body' cenv',
      env_corr n env cenv cenv' ->
      rename_pyexpr env n (PLam param body) = (PLam yparam body', snd (rename_pyexpr env n (PLam param body))) ->
      value_corr (PVClosure None param body cenv) (PVClosure None yparam body' cenv')
  | vcorr_closure_rec : forall f param body cenv env n yf yparam body' cenv',
      env_corr n env cenv cenv' ->
      rename_pyexpr env n (PRec f param body)
        = (PRec yf yparam body', snd (rename_pyexpr env n (PRec f param body))) ->
      value_corr (PVClosure (Some f) param body cenv) (PVClosure (Some yf) yparam body' cenv')
  | vcorr_closuremut : forall f1 param1 body1 f2 param2 body2 cenv which
                               env n yf1 yparam1 body1' yf2 yparam2 body2' cenv',
      env_corr n env cenv cenv' ->
      rename_pyexpr env n (PRecMut f1 param1 body1 f2 param2 body2)
        = (PRecMut yf1 yparam1 body1' yf2 yparam2 body2',
           snd (rename_pyexpr env n (PRecMut f1 param1 body1 f2 param2 body2))) ->
      value_corr (PVClosureMut f1 param1 body1 f2 param2 body2 cenv which)
                 (PVClosureMut yf1 yparam1 body1' yf2 yparam2 body2' cenv' which)
  | vcorr_closuregroup : forall fns cenv self_name env n fns' cenv',
      env_corr n env cenv cenv' ->
      rename_pyexpr env n (PRecGroup fns)
        = (PRecGroup fns', snd (rename_pyexpr env n (PRecGroup fns))) ->
      value_corr (PVClosureGroup fns cenv self_name) (PVClosureGroup fns' cenv' self_name)

with env_corr : nat -> list (var * var) -> pyenv -> pyenv -> Prop :=
  | ec_nil : forall n, env_corr n [] [] []
  | ec_cons : forall n m x v v' env rho rho',
      m < n -> value_corr v v' -> env_corr m env rho rho' ->
      env_corr n ((x, fresh_name m) :: env) ((x, v) :: rho) ((fresh_name m, v') :: rho')
  (** The [PRecGroup] exception's env-side counterpart: a binder that
      keeps its *original* name on both sides instead of getting a
      fresh one -- needed for [PApp]'s reconstruction of a
      [PVClosureGroup]'s member bindings (see this section's header for
      why [PRecGroup]'s own construction needs no such thing). Guarded
      by an explicit, checkable side condition ([f] is never of the
      [fresh_name] shape) carried right in the constructor rather than
      threaded through every other case's hypotheses: every concrete
      group this project actually runs discharges it trivially
      ([discriminate] against [fresh_name]'s ["v" ++ digits] shape);
      only a source program that deliberately names a group member like
      [v7] could fail it, and failing an explicit precondition is the
      honest outcome for that case, not a silently wrong one. *)
  | ec_cons_group : forall n f v v' env rho rho',
      (forall k, f <> fresh_name k) -> value_corr v v' -> env_corr n env rho rho' ->
      env_corr n ((f, f) :: env) ((f, v) :: rho) ((f, v') :: rho').

(** [env_corr]'s bound only ever needs to grow: nothing about the
    relation depends on using the *tightest* bound. *)
Lemma env_corr_weaken : forall n env rho rho',
  env_corr n env rho rho' -> forall n', n <= n' -> env_corr n' env rho rho'.
Proof.
  intros n env rho rho' H.
  induction H as [n0 | n0 m x v v' env0 rho0 rho0' Hm Hv Hcorr _
                  | n0 f v v' env0 rho0 rho0' Hf Hv Hcorr IH]; intros n' Hle.
  - constructor.
  - apply ec_cons; [lia | exact Hv | exact Hcorr].
  - apply ec_cons_group; [exact Hf | exact Hv | exact (IH n' Hle)].
Qed.

(** No entry [env_corr] ever builds into [rho'] uses a seed [>=] the
    bound in force when it was built -- the structural reason two
    different bindings can never collide, spelled out for [rho']
    directly (the form the lookup lemma below actually needs). *)
Lemma env_corr_rho'_absent : forall n env rho rho' m,
  env_corr n env rho rho' -> n <= m -> plookup rho' (fresh_name m) = None.
Proof.
  intros n env rho rho' m H. revert m.
  induction H as [n0 | n0 m0 x v v' env0 rho0 rho0' Hm0 Hv Hcorr IH
                  | n0 f v v' env0 rho0 rho0' Hf Hv Hcorr IH]; intros m Hle.
  - reflexivity.
  - cbn [plookup]. destruct (string_dec (fresh_name m) (fresh_name m0)) as [Heq|Hneq].
    + apply fresh_name_injective in Heq. lia.
    + apply IH. lia.
  - cbn [plookup]. destruct (string_dec (fresh_name m) f) as [Heq|Hneq].
    + exfalso. apply (Hf m). symmetry. exact Heq.
    + apply IH. exact Hle.
Qed.

(** Every name [rename_lookup] can ever hand back, given a well-formed
    [env_corr], is either the looked-up name itself unchanged (an
    [ec_cons_group] binder) or a genuine [fresh_name] (an [ec_cons]
    binder) -- the fact [env_corr_lookup]'s own new [ec_cons_group]
    case below needs to rule out an accidental collision with the one
    it just pushed. *)
Lemma rename_lookup_shape : forall n env rho rho' x,
  env_corr n env rho rho' ->
  rename_lookup env x = x \/ exists k, rename_lookup env x = fresh_name k.
Proof.
  intros n env rho rho' x H.
  induction H as [n0 | n0 m x0 v v' env0 rho0 rho0' Hm Hv Hcorr IH
                  | n0 f v v' env0 rho0 rho0' Hf Hv Hcorr IH].
  - cbn [rename_lookup]. left. reflexivity.
  - cbn [rename_lookup]. destruct (string_dec x x0) as [->|Hne].
    + right. exists m. reflexivity.
    + exact IH.
  - cbn [rename_lookup]. destruct (string_dec x f) as [->|Hne].
    + left. reflexivity.
    + exact IH.
Qed.

(** The heart of the correctness proof: looking a variable up on the
    original side and on the renamed side (via [rename_lookup]) agree
    whenever the original lookup actually succeeds -- the one-sided
    form [pyval_opt_corr] needs; see this section's header for why the
    other direction is intentionally not claimed. *)
Lemma env_corr_lookup : forall n env rho rho' x,
  env_corr n env rho rho' ->
  match plookup rho x with
  | None => True
  | Some v => exists v', plookup rho' (rename_lookup env x) = Some v' /\ value_corr v v'
  end.
Proof.
  intros n env rho rho' x H.
  induction H as [n | n m x0 v0 v0' env0 rho0 rho0' Hm Hv Hcorr IH
                  | n f0 v0 v0' env0 rho0 rho0' Hf0 Hv Hcorr IH].
  - cbn [plookup]. exact I.
  - cbn [plookup rename_lookup]. destruct (string_dec x x0) as [->|Hne].
    + destruct (string_dec (fresh_name m) (fresh_name m)) as [_|Hc];
        [| exfalso; apply Hc; reflexivity].
      exists v0'. split; [reflexivity | exact Hv].
    + cbn [plookup] in IH. destruct (plookup rho0 x) as [v|] eqn:Hlook; [| exact I].
      destruct IH as [v' [Hv' Hcv]].
      assert (Habsent : rename_lookup env0 x <> fresh_name m).
      { intro Heq.
        pose proof (env_corr_rho'_absent m env0 rho0 rho0' m Hcorr (le_n _)) as Habs.
        rewrite Heq in Hv'. rewrite Hv' in Habs. discriminate. }
      destruct (string_dec (rename_lookup env0 x) (fresh_name m)) as [Heq|_].
      * contradiction.
      * exists v'. split; [exact Hv' | exact Hcv].
  - cbn [plookup rename_lookup]. destruct (string_dec x f0) as [->|Hne].
    + destruct (string_dec f0 f0) as [_|Hc]; [| exfalso; apply Hc; reflexivity].
      exists v0'. split; [reflexivity | exact Hv].
    + cbn [plookup] in IH. destruct (plookup rho0 x) as [v|] eqn:Hlook; [| exact I].
      destruct IH as [v' [Hv' Hcv]].
      assert (Habsent : rename_lookup env0 x <> f0).
      { pose proof (rename_lookup_shape n env0 rho0 rho0' x Hcorr) as [Heqx | [k Heqk]].
        - rewrite Heqx. exact Hne.
        - rewrite Heqk. intro Heq. apply (Hf0 k). symmetry. exact Heq. }
      destruct (string_dec (rename_lookup env0 x) f0) as [Heq|_].
      * contradiction.
      * exists v'. split; [exact Hv' | exact Hcv].
Qed.

(** The environment [PApp]'s [PVClosureGroup] case actually rebuilds
    (PyLang.v's own [build_bindings], copied here as a standalone,
    parameterized [Fixpoint] so it can be reasoned about outside that
    [match]): every member of [gs] bound to a [PVClosureGroup] tagged
    with its own name, the *whole* group [fns]/ambient [cenv] carried
    through unchanged regardless of how far [gs] has been walked down. *)
Fixpoint recgroup_build_bindings
    (gs fns : list (var * var * pyexpr)) (cenv : pyenv) : pyenv :=
  match gs with
  | [] => cenv
  | (f, p, b) :: rest => (f, PVClosureGroup fns cenv f) :: recgroup_build_bindings rest fns cenv
  end.

(** The explicit, checkable side condition [ec_cons_group] needs,
    specialized to an actual [fns]: no member's own name is of the
    [fresh_name] shape. Trivial to discharge for every concrete group
    this project runs. *)
Definition group_names_ok (fns : list (var * var * pyexpr)) : Prop :=
  forall f p b, In (f, p, b) fns -> forall k, f <> fresh_name k.

(** [rename_pyexpr]'s [PRecGroup] case renames every member's own
    [param]/[body] but never its name (see this file's header) -- so
    the *list of names* a group ends up with is exactly the list it
    started with, just confirmed structurally rather than only
    asserted in prose. Proved for the bare anonymous [fix] first (no
    seed/fuel subtlety at all: a member's own renamed param/body are
    irrelevant to this fact, only *that* [go] keeps its first
    component unchanged, regardless of what it computes for the
    second and third), then lifted to [rename_pyexpr] itself. *)
Lemma recgroup_go_names : forall env' fs n,
  map (fun fpb => fst (fst fpb))
    (fst ((fix go (gs : list (var * var * pyexpr)) (m : nat)
               : list (var * var * pyexpr) * nat :=
             match gs with
             | [] => ([], m)
             | (f, p, b) :: rest =>
                 let yp := fresh_name m in
                 let '(b', m0) := rename_pyexpr ((p, yp) :: env') (S m) b in
                 let '(rest', m2) := go rest m0 in
                 ((f, yp, b') :: rest', m2)
             end) fs n))
  = map (fun fpb => fst (fst fpb)) fs.
Proof.
  intros env' fs. induction fs as [| [[f p] b] fs' IH]; intros n; simpl.
  - reflexivity.
  - destruct (rename_pyexpr ((p, fresh_name n) :: env') (S n) b) as [b' m0] eqn:Eb.
    destruct ((fix go (gs : list (var * var * pyexpr)) (m : nat)
                   : list (var * var * pyexpr) * nat :=
                 match gs with
                 | [] => ([], m)
                 | (f0, p0, b0) :: rest =>
                     let yp := fresh_name m in
                     let '(b'0, m0) := rename_pyexpr ((p0, yp) :: env') (S m) b0 in
                     let '(rest', m2) := go rest m0 in
                     ((f0, yp, b'0) :: rest', m2)
                 end) fs' m0) as [rest' m2] eqn:Ego.
    simpl. f_equal.
    specialize (IH m0). rewrite Ego in IH. simpl in IH. exact IH.
Qed.

Lemma rename_pyexpr_recgroup_names : forall env n fns fns' n',
  rename_pyexpr env n (PRecGroup fns) = (PRecGroup fns', n') ->
  map (fun fpb => fst (fst fpb)) fns' = map (fun fpb => fst (fst fpb)) fns.
Proof.
  intros env n fns fns' n' Hr.
  cbn [rename_pyexpr] in Hr.
  set (envfs := map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) in Hr.
  set (env' := List.app envfs env) in Hr.
  destruct ((fix go (gs : list (var * var * pyexpr)) (m : nat)
                 : list (var * var * pyexpr) * nat :=
               match gs with
               | [] => ([], m)
               | (f, p, b) :: rest =>
                   let yp := fresh_name m in
                   let '(b', m0) := rename_pyexpr ((p, yp) :: env') (S m) b in
                   let '(rest', m2) := go rest m0 in
                   ((f, yp, b') :: rest', m2)
               end) fns n) as [fnsX nX] eqn:Ego.
  injection Hr as Hr1 Hr2. subst fns'.
  rewrite <- (recgroup_go_names env' fns n). rewrite Ego. reflexivity.
Qed.

(** [recgroup_build_bindings] only ever looks at its first argument's
    own *names* (never its params/bodies, and never the length-
    shrinking recursion's own identity beyond that) -- so two lists
    with the same name sequence build the same environment, whatever
    their params/bodies actually are. *)
Lemma recgroup_build_bindings_ext : forall gs gs' fns cenv,
  map (fun fpb => fst (fst fpb)) gs = map (fun fpb => fst (fst fpb)) gs' ->
  recgroup_build_bindings gs fns cenv = recgroup_build_bindings gs' fns cenv.
Proof.
  induction gs as [| [[f p] b] gs_t IH]; intros gs' fns cenv Heq.
  - destruct gs' as [| [[f' p'] b'] gs_t']; simpl in Heq; [reflexivity | discriminate].
  - destruct gs' as [| [[f' p'] b'] gs_t']; simpl in Heq; [discriminate |].
    injection Heq as Hf Ht. subst f'. simpl. f_equal. apply IH, Ht.
Qed.

(** Connects [rename_pyexpr]'s own [PRecGroup] case to [PApp]'s
    reconstruction: the environment [PApp] rebuilds from [fns]/[cenv]
    on the original side and [fns']/[cenv'] on the renamed side
    correspond via [env_corr], keyed by the group's own (unrenamed)
    member names -- the fact [PRecGroup]/[PVClosureGroup]'s own
    [rename_pyexpr_correct] cases need. Unlike [rename_pyexpr_monotone]'s
    own [PRecGroup] case, no seed/fuel bookkeeping is needed here at
    all: [ec_cons_group] never consumes a fresh seed, so the *same*
    bound [n0] -- the ambient [env_corr]'s own -- works at every
    position in the group, and the induction (over an arbitrary
    sub-list [fs] of [fns], [fns]/[fns']/[cenv]/[cenv'] held fixed)
    only needs [recgroup_go_names]/[recgroup_build_bindings_ext] at the
    very end to reconcile the renamed-side tag ([fns] inside the
    induction, [fns'] in the goal -- the same names either way). *)
Lemma recgroup_rebuild_corr :
  forall env0 n0 cenv cenv', env_corr n0 env0 cenv cenv' ->
  forall fns fns' n',
  rename_pyexpr env0 n0 (PRecGroup fns) = (PRecGroup fns', n') ->
  group_names_ok fns ->
  env_corr n0 (List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env0)
              (recgroup_build_bindings fns fns cenv)
              (recgroup_build_bindings fns' fns' cenv').
Proof.
  intros env0 n0 cenv cenv' Hcorr0 fns fns' n' Hren Hok.
  assert (Hren2 : rename_pyexpr env0 n0 (PRecGroup fns)
                  = (PRecGroup fns', snd (rename_pyexpr env0 n0 (PRecGroup fns))))
    by (rewrite Hren; reflexivity).
  assert (Hnames : map (fun fpb => fst (fst fpb)) fns' = map (fun fpb => fst (fst fpb)) fns)
    by (apply (rename_pyexpr_recgroup_names env0 n0 fns fns' n' Hren)).
  assert (Hbodies : forall fs,
            (forall f p b, In (f, p, b) fs -> In (f, p, b) fns) ->
            env_corr n0 (List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fs) env0)
              (recgroup_build_bindings fs fns cenv)
              (recgroup_build_bindings fs fns' cenv')).
  { induction fs as [| [[f p] b] fs' IHfs]; intros Hsub; simpl.
    - exact Hcorr0.
    - assert (Hin : In (f, p, b) fns) by (apply Hsub; left; reflexivity).
      assert (Hsub' : forall f0 p0 b0, In (f0, p0, b0) fs' -> In (f0, p0, b0) fns)
        by (intros f0 p0 b0 Hin0; apply Hsub; right; exact Hin0).
      apply ec_cons_group.
      + exact (Hok f p b Hin).
      + apply (vcorr_closuregroup fns cenv f env0 n0 fns').
        * exact Hcorr0.
        * exact Hren2.
      + apply (IHfs Hsub'). }
  pose proof (Hbodies fns (fun f p b Hin => Hin)) as Hb.
  rewrite (recgroup_build_bindings_ext fns fns' fns' cenv' (eq_sym Hnames)) in Hb.
  exact Hb.
Qed.

(** The one-sided result relation [rename_pyexpr_correct] (below) is
    stated in terms of -- see this section's header for why one-sided. *)
Definition pyval_opt_corr (ov ov' : option pyvalue) : Prop :=
  match ov with
  | None => True
  | Some v => exists v', ov' = Some v' /\ value_corr v v'
  end.

(** The same one-sided shape as [pyval_opt_corr], but for the
    [option (list (var * pyvalue))] an N-field record's fields
    evaluate to as a group, before being wrapped in [PVRecordN] --
    needed because [PRecordN]'s own per-field reasoning is itself a
    list fold, one level "inside" the [pyvalue] [pyval_opt_corr]
    describes. *)
Definition pyval_optlist_corr (ov ov' : option (list (var * pyvalue))) : Prop :=
  match ov with
  | None => True
  | Some vs => exists vs', ov' = Some vs' /\
      Forall2 (fun kv kv' => fst kv = fst kv' /\ value_corr (snd kv) (snd kv')) vs vs'
  end.

Lemma pyval_opt_corr_lookup : forall n env rho rho' x,
  env_corr n env rho rho' -> pyval_opt_corr (plookup rho x) (plookup rho' (rename_lookup env x)).
Proof.
  intros n env rho rho' x H.
  pose proof (env_corr_lookup n env rho rho' x H) as Hl.
  unfold pyval_opt_corr. destruct (plookup rho x) as [v|]; [exact Hl | exact I].
Qed.

(** [PFieldN]'s by-name field lookup, and [PRecordN]/[PRecGroup]'s own
    field/member lists, all reduce to this one shape: given
    corresponding (same keys, [value_corr]-related values) field
    lists, looking the same name up in both agrees -- the one-sided
    form, again, since a miss on the original side needs nothing said
    about the renamed side. *)
Lemma pvrecordn_field_corr : forall fields fields' name,
  Forall2 (fun kv kv' => fst kv = fst kv' /\ value_corr (snd kv) (snd kv')) fields fields' ->
  pyval_opt_corr
    ((fix lookup_field (fs : list (var * pyvalue)) : option pyvalue :=
        match fs with
        | [] => None
        | (k, v) :: rest => if String.eqb k name then Some v else lookup_field rest
        end) fields)
    ((fix lookup_field (fs : list (var * pyvalue)) : option pyvalue :=
        match fs with
        | [] => None
        | (k, v) :: rest => if String.eqb k name then Some v else lookup_field rest
        end) fields').
Proof.
  intros fields fields' name H.
  induction H as [| kv kv' fields2 fields2' [Hk Hv] Hrest IH].
  - simpl. exact I.
  - destruct kv as [k v]. destruct kv' as [k' v'].
    simpl in Hk. subst k'. simpl.
    destruct (String.eqb k name); [eexists; split; [reflexivity | exact Hv] | exact IH].
Qed.

(** [PRepeat]'s own correctness need: [piterate] run on two
    [value_corr]-related seeds, with a step function that preserves
    [value_corr] (the one-sided way) for every related pair, itself
    preserves it after any number of steps -- mirrors [Translate.v]'s
    own [iterate_translate_correct], proved once by induction on the
    step count, the same way. *)
Lemma piterate_corr : forall k f f' v v',
  value_corr v v' ->
  (forall u u', value_corr u u' -> pyval_opt_corr (f u) (f' u')) ->
  pyval_opt_corr (piterate k f v) (piterate k f' v').
Proof.
  induction k as [| k' IH]; intros f f' v v' Hv Hf.
  - simpl. eexists; split; [reflexivity | exact Hv].
  - simpl.
    pose proof (Hf v v' Hv) as Hfv.
    unfold pyval_opt_corr in Hfv.
    destruct (f v) as [u|] eqn:Ef; [| exact I].
    destruct Hfv as [u' [Ef' Hu]].
    rewrite Ef'.
    apply IH; [exact Hu | exact Hf].
Qed.
