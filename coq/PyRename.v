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
    computes. **That theorem is now complete** -- all 46 of [pyexpr]'s
    constructors are proved, [Qed]'d, no [Admitted]/[admit] anywhere.
    [Print Assumptions] on it shows only [PrimFloat]'s own existing
    primitives, the same set every other theorem in this pipeline
    already carries -- nothing new.

    Getting the last two cases ([PRecGroup] and the matching
    [PVClosureGroup] case inside [PApp]) actually closed needed two
    real pieces of new machinery, not just more casework, both now
    landed:

    - [env_corr] gained a new constructor, [ec_cons_group]: a binder
      that keeps its *original* name on both sides instead of getting
      a fresh one (needed because [PApp] reconstructs every member's
      own binding, by its never-renamed name, into the callee's
      environment before evaluating the matched body). Guarded by one
      explicit, local, checkable side condition carried right in the
      constructor -- the pushed name is never of the [fresh_name]
      shape -- rather than a blanket axiom or a hypothesis threaded
      through the whole induction: because the pushed renamed-side name
      always *equals* its own original-side key, ruling out a collision
      with any other already-in-scope name needs nothing beyond that
      one local fact (no "two different groups never share a member
      name" assumption either, despite an earlier worry to the
      contrary). [env_corr_weaken]/[env_corr_rho'_absent]/
      [env_corr_lookup] (plus a new helper, [rename_lookup_shape]) were
      extended for this one more constructor.
    - A syntactic well-formedness predicate, [pyexpr_recgroup_ok] (an
      explicit, checkable hypothesis now threaded through
      [rename_pyexpr_correct]'s own statement: every [PRecGroup]
      anywhere inside the expression has member names avoiding the
      [fresh_name] shape -- [group_names_ok]'s own per-group condition,
      generalized to the whole term, trivial to discharge for every
      concrete group this project runs, e.g. ["fall"]/["rise"]/
      ["report"]; a source program that deliberately named a member
      [v7] would fail it, which is the honest outcome, not a silent
      wrong answer). A syntactic fact about the *current* expression
      alone isn't quite enough on its own, though: [PApp]'s closure-
      application cases need it for the closure's own *captured
      body*, which is reached through a *value* already sitting in
      [rho], not through a subterm of [PApp func arg] itself. So
      [value_corr]'s four closure constructors
      ([vcorr_closure_lam]/[vcorr_closure_rec]/[vcorr_closuremut]/
      [vcorr_closuregroup]) now also carry a [pyexpr_recgroup_ok]
      premise for their own captured body/bodies/group -- established
      once at construction time (every [PLam]/[PRec]/[PRecMut]/
      [PRecGroup] case supplies it, trivially, from its own current
      [pyexpr_recgroup_ok] hypothesis), consumed later at application
      time (via [inversion] on the [value_corr] witness, the same way
      its [env_corr] premise already was).

    Three more lemmas connect [rename_pyexpr]'s own [PRecGroup] case to
    [PApp]'s actual runtime reconstruction: [recgroup_rebuild_corr]
    (the rebuilt environment corresponds via [env_corr], keyed by the
    group's own names -- needs no seed/fuel bookkeeping at all, since
    [ec_cons_group] never consumes a fresh seed), [plookup_group_fn_corr]
    (the by-name dispatch [PApp] uses to pick which member is being
    called finds corresponding members on both sides, with the
    renamed side's parameter/body exactly what [rename_pyexpr] itself
    produced for that member), and two small bridging facts
    ([recgroup_build_fields_eq]/[recgroup_build_bindings_eq],
    [plookup_group_fn_in]) identifying [PyLang.v]'s own anonymous
    [fix]es with named, reusable versions of the same functions.

    What this theorem does *not* claim, unchanged from before: the
    same, smaller residual boundary [PyPrint.v]'s header describes --
    that printing the renamed tree as Python text, and running that
    text under real CPython, matches [peval]. That remains the
    project's documented, explicit trust boundary (`docs/duality.md`),
    not a gap specific to this file. *)

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
  | PFOpp e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      (PFOpp e1', n1)
  | PFAbs e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      (PFAbs e1', n1)
  | PFSqrt e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      (PFSqrt e1', n1)
  | PFMax e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFMax e1' e2', n2)
  | PFMin e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFMin e1' e2', n2)
  | PFExp e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      (PFExp e1', n1)
  | PFLn e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      (PFLn e1', n1)
  | PFPow e1 e2 =>
      let '(e1', n1) := rename_pyexpr env n e1 in
      let '(e2', n2) := rename_pyexpr env n1 e2 in
      (PFPow e1' e2', n2)
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
  | PNone => (PNone, n)
  | PSome e1 =>
      let '(e1', n1) := rename_pyexpr env n e1 in (PSome e1', n1)
  | POptionMatch scrutinee nonecase x somecase =>
      let '(scrutinee', n0) := rename_pyexpr env n scrutinee in
      let '(nonecase', n1) := rename_pyexpr env n0 nonecase in
      let y := fresh_name n1 in
      let '(somecase', n2) := rename_pyexpr ((x, y) :: env) (S n1) somecase in
      (POptionMatch scrutinee' nonecase' y somecase', n2)
  | PArrConst es =>
      let '(es', n1) :=
        (fix go (xs : list pyexpr) (n : nat) : list pyexpr * nat :=
           match xs with
           | [] => ([], n)
           | e1 :: rest =>
               let '(e1', n0) := rename_pyexpr env n e1 in
               let '(rest', n2) := go rest n0 in
               (e1' :: rest', n2)
           end) es n
      in
      (PArrConst es', n1)
  | PArrGet arr idx =>
      let '(arr', n1) := rename_pyexpr env n arr in
      let '(idx', n2) := rename_pyexpr env n1 idx in
      (PArrGet arr' idx', n2)
  | PArrSet arr idx val =>
      let '(arr', n1) := rename_pyexpr env n arr in
      let '(idx', n2) := rename_pyexpr env n1 idx in
      let '(val', n3) := rename_pyexpr env n2 val in
      (PArrSet arr' idx' val', n3)
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
  | PNot e1 | PFst e1 | PSnd e1 | PField _ e1 | PInl e1 | PInr e1 | PFieldN _ e1 | PFOpp e1 | PFAbs e1 | PFSqrt e1 | PFExp e1 | PFLn e1 =>
      S (pyexpr_size e1)
  | PAdd e1 e2 | PSub e1 e2 | PMul e1 e2 | PEq e1 e2 | PLt e1 e2 | PLe e1 e2
  | PAnd e1 e2 | POr e1 e2 | PPair e1 e2 | PFAdd e1 e2 | PFSub e1 e2 | PFMul e1 e2
  | PFDiv e1 e2 | PFEq e1 e2 | PFLt e1 e2 | PFLe e1 e2 | PFMax e1 e2 | PFMin e1 e2 | PFPow e1 e2 | PDiv e1 e2 | PMod e1 e2
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
  | PNone => 1
  | PSome e1 => S (pyexpr_size e1)
  | POptionMatch sc nc _ sm => S (pyexpr_size sc + pyexpr_size nc + pyexpr_size sm)
  | PArrConst es => S (fold_right (fun e1 acc => pyexpr_size e1 + acc) 0 es)
  | PArrGet arr idx => S (pyexpr_size arr + pyexpr_size idx)
  | PArrSet arr idx val => S (pyexpr_size arr + pyexpr_size idx + pyexpr_size val)
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

Lemma pyexpr_size_in_elts :
  forall e1 es, In e1 es -> pyexpr_size e1 < pyexpr_size (PArrConst es).
Proof.
  intros e1 es Hin.
  induction es as [| e0 rest IH]; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst. simpl. lia.
    + specialize (IH Hin). simpl in IH |- *. lia.
Qed.

(** The explicit, checkable side condition a [PRecGroup]'s own
    env-correspondence needs ([ec_cons_group], later below): no
    member's own name is of the [fresh_name] shape. Trivial to
    discharge for every concrete group this project runs. *)
Definition group_names_ok (fns : list (var * var * pyexpr)) : Prop :=
  forall f p b, In (f, p, b) fns -> forall k, f <> fresh_name k.

(** A well-formedness predicate on [pyexpr] itself, recursing the same
    way [pyexpr_size] does: every [PRecGroup] anywhere inside [e] (at
    any depth) has member names avoiding the [fresh_name] shape. This
    is the explicit, checkable hypothesis [rename_pyexpr_correct]
    (below) needs for its own [PRecGroup]/[PVClosureGroup] cases --
    *not* a hypothesis that can be discharged unconditionally for an
    arbitrary [e], since it is genuinely false for an adversarial one
    (a group member named literally [v7] really can collide with an
    unrelated [fresh_name 7] elsewhere in the same renamed tree, which
    really would make two distinct bindings share one generated Python
    identifier -- the exact bug class this whole file exists to rule
    out). Every concrete group this project runs discharges it
    trivially by [reflexivity]/[discriminate] against [fresh_name]'s
    ["v" ++ digits] shape. *)
Fixpoint pyexpr_recgroup_ok (e : pyexpr) : Prop :=
  match e with
  | PConst _ | PBool _ | PVar _ | PNil | PFConst _ | PStrConst _ | PNone => True
  | PNot e1 | PFst e1 | PSnd e1 | PField _ e1 | PInl e1 | PInr e1 | PFieldN _ e1 | PFOpp e1 | PFAbs e1 | PFSqrt e1 | PFExp e1 | PFLn e1 | PSome e1 =>
      pyexpr_recgroup_ok e1
  | PAdd e1 e2 | PSub e1 e2 | PMul e1 e2 | PEq e1 e2 | PLt e1 e2 | PLe e1 e2
  | PAnd e1 e2 | POr e1 e2 | PPair e1 e2 | PFAdd e1 e2 | PFSub e1 e2 | PFMul e1 e2
  | PFDiv e1 e2 | PFEq e1 e2 | PFLt e1 e2 | PFLe e1 e2 | PFMax e1 e2 | PFMin e1 e2 | PFPow e1 e2 | PDiv e1 e2 | PMod e1 e2
  | PApp e1 e2 | PCons e1 e2 | PStrConcat e1 e2 | PStrEq e1 e2
  | PLet _ e1 e2 | PRecord _ e1 _ e2 =>
      pyexpr_recgroup_ok e1 /\ pyexpr_recgroup_ok e2
  | PIf c e1 e2 => pyexpr_recgroup_ok c /\ pyexpr_recgroup_ok e1 /\ pyexpr_recgroup_ok e2
  | PRepeat _ _ body init => pyexpr_recgroup_ok body /\ pyexpr_recgroup_ok init
  | PLam _ body => pyexpr_recgroup_ok body
  | PRec _ _ body => pyexpr_recgroup_ok body
  | PRecMut _ _ body1 _ _ body2 => pyexpr_recgroup_ok body1 /\ pyexpr_recgroup_ok body2
  | PListMatch sc nc _ _ cc => pyexpr_recgroup_ok sc /\ pyexpr_recgroup_ok nc /\ pyexpr_recgroup_ok cc
  | PCase sc _ c1 _ c2 => pyexpr_recgroup_ok sc /\ pyexpr_recgroup_ok c1 /\ pyexpr_recgroup_ok c2
  | PRecordN fields =>
      (fix go (fs : list (var * pyexpr)) : Prop :=
         match fs with [] => True | (_, fe) :: rest => pyexpr_recgroup_ok fe /\ go rest end) fields
  | PRecGroup fns =>
      group_names_ok fns /\
      (fix go (fs : list (var * var * pyexpr)) : Prop :=
         match fs with [] => True | (_, _, b) :: rest => pyexpr_recgroup_ok b /\ go rest end) fns
  | POptionMatch sc nc _ sm => pyexpr_recgroup_ok sc /\ pyexpr_recgroup_ok nc /\ pyexpr_recgroup_ok sm
  | PArrConst es =>
      (fix go (xs : list pyexpr) : Prop :=
         match xs with [] => True | e1 :: rest => pyexpr_recgroup_ok e1 /\ go rest end) es
  | PArrGet arr idx => pyexpr_recgroup_ok arr /\ pyexpr_recgroup_ok idx
  | PArrSet arr idx val => pyexpr_recgroup_ok arr /\ pyexpr_recgroup_ok idx /\ pyexpr_recgroup_ok val
  end.

Lemma rename_pyexpr_monotone : forall e env n, n <= snd (rename_pyexpr env n e).
Proof.
  assert (Hstrong : forall sz e, pyexpr_size e <= sz -> forall env n, n <= snd (rename_pyexpr env n e)).
  { induction sz as [sz IHsz] using (well_founded_induction lt_wf).
    intros e Hsz env n.
    destruct e as
      [ z | b | x | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1
      | c e1 e2 | e1 e2 | e1 | e1 | x e1 e2 | fl | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2
      | e1 e2 | e1 e2 | e1 | e1 | e1 | e1 e2 | e1 e2 | e1 | e1 | e1 e2 | k x body init | e1 e2 | e1 e2 | param body | f param body
      | f1 param1 body1 f2 param2 body2 | func arg | | hd tl
      | scrutinee nilcase hd tl conscase | k1 e1 k2 e2 | name e1 | e1 | e1
      | scrutinee x1 case1 x2 case2 | s | e1 e2 | e1 e2 | fields | name e1 | fns
      | | e1 | scrutinee nonecase x somecase
      | es | arr idx | arr idx val ];
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
    - (* PArrConst es *)
      revert Hsz n.
      induction es as [| e0 es' IHes]; intros Hsz n; simpl in Hsz; simpl.
      + lia.
      + assert (He0_lt : pyexpr_size e0 < sz) by lia.
        assert (Htail : pyexpr_size (PArrConst es') <= sz) by (simpl; lia).
        pose proof (IHsz (pyexpr_size e0) He0_lt e0 (le_n _) env n) as He0.
        destruct (rename_pyexpr env n e0) as [e0' n0] eqn:Ee0. simpl in He0.
        specialize (IHes Htail n0).
        destruct ((fix go (xs : list pyexpr) (n1 : nat) : list pyexpr * nat :=
                     match xs with
                     | [] => ([], n1)
                     | e1 :: rest =>
                         let '(e1', n2) := rename_pyexpr env n1 e1 in
                         let '(rest', n3) := go rest n2 in
                         (e1' :: rest', n3)
                     end) es' n0) as [es'' n1] eqn:Ees'.
        simpl in IHes. simpl. lia.
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
  | vcorr_array : forall vs vs',
      Forall2 value_corr vs vs' -> value_corr (PVArr vs) (PVArr vs')
  | vcorr_none : value_corr PVNone PVNone
  | vcorr_some : forall v v', value_corr v v' -> value_corr (PVSome v) (PVSome v')
  | vcorr_closure_lam : forall param body cenv env n yparam body' cenv',
      env_corr n env cenv cenv' ->
      pyexpr_recgroup_ok body ->
      rename_pyexpr env n (PLam param body) = (PLam yparam body', snd (rename_pyexpr env n (PLam param body))) ->
      value_corr (PVClosure None param body cenv) (PVClosure None yparam body' cenv')
  | vcorr_closure_rec : forall f param body cenv env n yf yparam body' cenv',
      env_corr n env cenv cenv' ->
      pyexpr_recgroup_ok body ->
      rename_pyexpr env n (PRec f param body)
        = (PRec yf yparam body', snd (rename_pyexpr env n (PRec f param body))) ->
      value_corr (PVClosure (Some f) param body cenv) (PVClosure (Some yf) yparam body' cenv')
  | vcorr_closuremut : forall f1 param1 body1 f2 param2 body2 cenv which
                               env n yf1 yparam1 body1' yf2 yparam2 body2' cenv',
      env_corr n env cenv cenv' ->
      pyexpr_recgroup_ok body1 -> pyexpr_recgroup_ok body2 ->
      rename_pyexpr env n (PRecMut f1 param1 body1 f2 param2 body2)
        = (PRecMut yf1 yparam1 body1' yf2 yparam2 body2',
           snd (rename_pyexpr env n (PRecMut f1 param1 body1 f2 param2 body2))) ->
      value_corr (PVClosureMut f1 param1 body1 f2 param2 body2 cenv which)
                 (PVClosureMut yf1 yparam1 body1' yf2 yparam2 body2' cenv' which)
  | vcorr_closuregroup : forall fns cenv self_name env n fns' cenv',
      env_corr n env cenv cenv' ->
      pyexpr_recgroup_ok (PRecGroup fns) ->
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
Lemma env_corr_weaken : forall n n' env rho rho',
  n <= n' -> env_corr n env rho rho' -> env_corr n' env rho rho'.
Proof.
  intros n n' env rho rho' Hle H. revert n' Hle.
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

(** [PRecGroup]'s own [peval] case (PyLang.v) builds a [PVRecordN], not
    an environment -- a different anonymous [fix], ending in [[]] (no
    ambient environment appended) rather than [cenv]. Copied here the
    same way, standalone, for the same reason. *)
Fixpoint recgroup_build_fields
    (gs fns : list (var * var * pyexpr)) (cenv : pyenv) : list (var * pyvalue) :=
  match gs with
  | [] => []
  | (f, p, b) :: rest => (f, PVClosureGroup fns cenv f) :: recgroup_build_fields rest fns cenv
  end.

(** Identifies [recgroup_build_fields] with [PyLang.v]'s own anonymous
    [build_fields] (its [PRecGroup] [peval] case), so a goal exposing
    the latter (via [simpl]/[cbn [peval]]) can be rewritten into the
    former -- the named, reusable form every other lemma above
    actually works with. *)
Lemma recgroup_build_fields_eq : forall gs fns cenv,
  (fix build_fields (gs0 : list (var * var * pyexpr)) : list (var * pyvalue) :=
     match gs0 with
     | [] => []
     | (f, p, b) :: rest => (f, PVClosureGroup fns cenv f) :: build_fields rest
     end) gs
  = recgroup_build_fields gs fns cenv.
Proof.
  induction gs as [| [[f p] b] rest IH]; intros fns cenv; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

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
  pyexpr_recgroup_ok (PRecGroup fns) ->
  env_corr n0 (List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env0)
              (recgroup_build_bindings fns fns cenv)
              (recgroup_build_bindings fns' fns' cenv').
Proof.
  intros env0 n0 cenv cenv' Hcorr0 fns fns' n' Hren Hwf.
  assert (Hok : group_names_ok fns) by (destruct Hwf as [Hok _]; exact Hok).
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
        * exact Hwf.
        * exact Hren2.
      + apply (IHfs Hsub'). }
  pose proof (Hbodies fns (fun f p b Hin => Hin)) as Hb.
  rewrite (recgroup_build_bindings_ext fns fns' fns' cenv' (eq_sym Hnames)) in Hb.
  exact Hb.
Qed.

Lemma recgroup_build_bindings_eq : forall gs fns cenv,
  (fix build_bindings (gs0 : list (var * var * pyexpr)) : pyenv :=
     match gs0 with
     | [] => cenv
     | (f, p, b) :: rest => (f, PVClosureGroup fns cenv f) :: build_bindings rest
     end) gs
  = recgroup_build_bindings gs fns cenv.
Proof.
  induction gs as [| [[f p] b] rest IH]; intros fns cenv; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma plookup_group_fn_in : forall fns self_name param body,
  plookup_group_fn fns self_name = Some (param, body) ->
  In (self_name, param, body) fns.
Proof.
  induction fns as [| [[f p] b] rest IH]; intros self_name param body Hlook.
  - simpl in Hlook. discriminate.
  - simpl in Hlook. destruct (string_dec f self_name) as [->|Hneq].
    + injection Hlook as -> ->. left. reflexivity.
    + right. apply (IH self_name param body Hlook).
Qed.

(** Connects [plookup_group_fn]'s by-name lookup (how [PApp] finds
    which member of a [PVClosureGroup] is actually being called) across
    [rename_pyexpr]'s [PRecGroup] case: if the original side finds a
    member (by its own, never-renamed name) with a given [param]/
    [body], the renamed side finds the *same* member (same name) with
    a corresponding [fresh_name]'d parameter and the correspondingly
    renamed body -- proved the same way [recgroup_rebuild_corr] is
    (generalizing over an arbitrary sub-list, no change to the outer
    [fns]/[fns']/[env']), but now tracking the *specific* seed each
    member's own parameter was assigned, not just environment
    correspondence. *)

Lemma plookup_group_fn_corr :
  forall env0 n0 fns fns' n0',
  rename_pyexpr env0 n0 (PRecGroup fns) = (PRecGroup fns', n0') ->
  forall self_name param body,
  plookup_group_fn fns self_name = Some (param, body) ->
  exists body' sd,
    n0 <= sd /\
    plookup_group_fn fns' self_name = Some (fresh_name sd, body') /\
    rename_pyexpr
      ((param, fresh_name sd) :: List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env0)
      (S sd) body
    = (body', snd (rename_pyexpr
         ((param, fresh_name sd) :: List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env0)
         (S sd) body)).
Proof.
  intros env0 n0 fns fns' n0' Hren.
  cbn [rename_pyexpr] in Hren.
  set (envfs := map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) in Hren.
  set (env' := List.app envfs env0) in Hren.
  assert (Hbodies : forall fs,
            forall seed,
            forall self_name param body,
            plookup_group_fn fs self_name = Some (param, body) ->
            exists body' sd,
              seed <= sd /\
              plookup_group_fn
                (fst ((fix go (gs : list (var * var * pyexpr)) (m : nat)
                           : list (var * var * pyexpr) * nat :=
                         match gs with
                         | [] => ([], m)
                         | (f, p, b) :: rest =>
                             let yp := fresh_name m in
                             let '(b', m0) := rename_pyexpr ((p, yp) :: env') (S m) b in
                             let '(rest', m2) := go rest m0 in
                             ((f, yp, b') :: rest', m2)
                         end) fs seed)) self_name = Some (fresh_name sd, body') /\
              rename_pyexpr ((param, fresh_name sd) :: env') (S sd) body
                = (body', snd (rename_pyexpr ((param, fresh_name sd) :: env') (S sd) body))).
  { induction fs as [| [[f p] b] rest IH]; intros seed self_name0 param0 body0 Hlook.
    - simpl in Hlook. discriminate.
    - simpl in Hlook. simpl.
      destruct (rename_pyexpr ((p, fresh_name seed) :: env') (S seed) b) as [b' m0] eqn:Eb.
      destruct ((fix go (gs : list (var * var * pyexpr)) (m : nat)
                     : list (var * var * pyexpr) * nat :=
                   match gs with
                   | [] => ([], m)
                   | (f0, p0, b0) :: rest0 =>
                       let yp := fresh_name m in
                       let '(b'0, m1) := rename_pyexpr ((p0, yp) :: env') (S m) b0 in
                       let '(rest0', m2) := go rest0 m1 in
                       ((f0, yp, b'0) :: rest0', m2)
                   end) rest m0) as [rest' m2] eqn:Ego.
      simpl.
      destruct (string_dec f self_name0) as [Heq | Hneq].
      + injection Hlook as Hp Hb. subst p b self_name0.
        exists b', seed.
        split; [lia |].
        split; [destruct (string_dec f f) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity] |].
        rewrite Eb. reflexivity.
      + pose proof (IH m0 self_name0 param0 body0 Hlook) as [body' [sd [Hsd [Hplook Hbeq]]]].
        exists body', sd.
        split; [pose proof (rename_pyexpr_monotone b ((p, fresh_name seed) :: env') (S seed)) as Hm;
                rewrite Eb in Hm; simpl in Hm; lia |].
        split; [destruct (string_dec f self_name0) as [Hc|_]; [contradiction | rewrite Ego in Hplook; simpl in Hplook; exact Hplook] |].
        exact Hbeq. }
  destruct ((fix go (gs : list (var * var * pyexpr)) (m : nat)
                 : list (var * var * pyexpr) * nat :=
               match gs with
               | [] => ([], m)
               | (f, p, b) :: rest =>
                   let yp := fresh_name m in
                   let '(b', m0) := rename_pyexpr ((p, yp) :: env') (S m) b in
                   let '(rest', m2) := go rest m0 in
                   ((f, yp, b') :: rest', m2)
               end) fns n0) as [fnsX n0X] eqn:Ego0.
  injection Hren as Hren1 Hren2. subst fnsX.
  intros self_name param body Hlook.
  pose proof (Hbodies fns n0 self_name param body Hlook) as [body' [sd [Hsd [Hplook Hbeq]]]].
  rewrite Ego0 in Hplook. simpl in Hplook.
  exists body', sd. split; [exact Hsd | split; [exact Hplook | exact Hbeq]].
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

(** [pyval_optlist_corr]'s own un-keyed sibling, for [PArrConst]'s
    [option (list pyvalue)] element list -- the [var]-keyed half of
    that template dropped since an array's elements carry no name,
    the same adaptation this project's array work has already made
    for [elts_fuel]/[print_parse_eltsN_roundtrip] in [Json.v]. *)
Definition pyval_optarr_corr (ov ov' : option (list pyvalue)) : Prop :=
  match ov with
  | None => True
  | Some vs => exists vs', ov' = Some vs' /\ Forall2 value_corr vs vs'
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

(** [PArrGet]/[PArrSet]'s own small helpers -- [Forall2 value_corr]
    preserved under [nth_error]/[firstn]/[skipn]/[++], the relational
    (one-sided, [value_corr]-indexed) counterpart of [Translate.v]'s
    own [option_map_nth_error]/[map_firstn_skipn_ins] facts, which are
    stated in terms of exact equality under [map] rather than a
    relation, since that file's own [EArrGet]/[EArrSet] proof doesn't
    need to track a renaming. *)
Lemma Forall2_value_corr_nth_error : forall vs vs' (i : nat),
  Forall2 value_corr vs vs' -> pyval_opt_corr (nth_error vs i) (nth_error vs' i).
Proof.
  intros vs vs' i H. revert i.
  induction H as [| v v' vs2 vs2' Hv Hrest IH]; intros i.
  - destruct i; simpl; exact I.
  - destruct i as [| i']; simpl.
    + eexists; split; [reflexivity | exact Hv].
    + exact (IH i').
Qed.

Lemma Forall2_value_corr_firstn : forall vs vs' (i : nat),
  Forall2 value_corr vs vs' -> Forall2 value_corr (firstn i vs) (firstn i vs').
Proof.
  intros vs vs' i H. revert i.
  induction H as [| v v' vs2 vs2' Hv Hrest IH]; intros i.
  - destruct i; simpl; constructor.
  - destruct i as [| i']; simpl; [constructor |].
    constructor; [exact Hv | exact (IH i')].
Qed.

Lemma Forall2_value_corr_skipn : forall vs vs' (i : nat),
  Forall2 value_corr vs vs' -> Forall2 value_corr (skipn i vs) (skipn i vs').
Proof.
  intros vs vs' i H. revert i.
  induction H as [| v v' vs2 vs2' Hv Hrest IH]; intros i.
  - destruct i; simpl; constructor.
  - destruct i as [| i']; simpl; [constructor; [exact Hv | exact Hrest] |].
    exact (IH i').
Qed.

Lemma Forall2_value_corr_app : forall vs1 vs1' vs2 vs2',
  Forall2 value_corr vs1 vs1' -> Forall2 value_corr vs2 vs2' ->
  Forall2 value_corr (vs1 ++ vs2) (vs1' ++ vs2').
Proof.
  intros vs1 vs1' vs2 vs2' H1 H2.
  induction H1 as [| v v' rest rest' Hv Hrest IH]; simpl; [exact H2 | constructor; [exact Hv | exact IH]].
Qed.

Lemma Forall2_value_corr_length : forall vs vs',
  Forall2 value_corr vs vs' -> List.length vs = List.length vs'.
Proof.
  intros vs vs' H. induction H as [| v v' rest rest' Hv Hrest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** The exact same [simpl] one-step-unfolds [skipn (S n) l] gotcha
    this project's own [coq_rewrite_anonymous_fix_mismatch] session
    memory documents (and [Translate.v]'s own [skipn_S_unfold] already
    fixes for that file) -- a local copy, since [PyRename.v] does not
    import [Translate.v]. *)
Lemma skipn_S_unfold : forall (A : Type) (n : nat) (l : list A),
  match l with [] => [] | _ :: l' => skipn n l' end = skipn (S n) l.
Proof. intros. destruct l; reflexivity. Qed.

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

Theorem rename_pyexpr_correct :
  forall fuel e env n rho rho',
    pyexpr_recgroup_ok e ->
    env_corr n env rho rho' ->
    pyval_opt_corr (peval fuel rho e) (peval fuel rho' (fst (rename_pyexpr env n e))).
Proof.
  induction fuel as [| fuel' IHfuel']; intros e env n rho rho' Hok Henv.
  - simpl. exact I.
  - destruct e as
      [ z | b | x | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1
      | c e1 e2 | e1 e2 | e1 | e1 | x e1 e2 | fl | e1 e2 | e1 e2 | e1 e2 | e1 e2 | e1 e2
      | e1 e2 | e1 e2 | e1 | e1 | e1 | e1 e2 | e1 e2 | e1 | e1 | e1 e2 | k x body init | e1 e2 | e1 e2 | param body | f param body
      | f1 param1 body1 f2 param2 body2 | func arg | | hd tl
      | scrutinee nilcase hd tl conscase | k1 e1 k2 e2 | name e1 | e1 | e1
      | scrutinee x1 case1 x2 case2 | s | e1 e2 | e1 e2 | fields | name e1 | fns
      | | e1 | scrutinee nonecase x somecase
      | es | arr idx | arr idx val ].
    all: simpl in Hok.
    + (* PConst *) simpl. eexists; split; [reflexivity | constructor].
    + (* PBool *) simpl. eexists; split; [reflexivity | constructor].
    + (* PVar *) simpl. apply (pyval_opt_corr_lookup n env rho rho' x). exact Henv.
    + (* PAdd *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PSub *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PMul *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PEq *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PLt *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PLe *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PAnd *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* POr *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PNot *) rename Hok into Hok1. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PIf *) destruct Hok as [HokC [Hok1 Hok2]]. simpl.
      destruct (rename_pyexpr env n c) as [c' n0] eqn:R0.
      destruct (rename_pyexpr env n0 e1) as [e1' n1] eqn:R1.
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho c) as [vc|] eqn:Ec; [| exact I].
      pose proof (IHfuel' c env n rho rho' HokC Henv) as Hc.
      rewrite Ec, R0 in Hc; simpl in Hc; destruct Hc as [vc' [Ec' Hvc]].
      rewrite Ec'.
      destruct vc; simpl in Hvc |- *; try exact I.
      inversion Hvc; subst.
      assert (Hn0 : n <= n0) by (pose proof (rename_pyexpr_monotone c env n) as Hm; rewrite R0 in Hm; exact Hm).
      assert (Hn1 : n0 <= n1) by (pose proof (rename_pyexpr_monotone e1 env n0) as Hm; rewrite R1 in Hm; exact Hm).
      destruct b.
      * pose proof (IHfuel' e1 env n0 rho rho' Hok1 (env_corr_weaken n n0 env rho rho' Hn0 Henv)) as H1.
        rewrite R1 in H1. simpl in H1. exact H1.
      * assert (Hn0n1 : n <= n1) by lia.
        pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn0n1 Henv)) as H2.
        rewrite R2 in H2. simpl in H2. exact H2.
    + (* PPair *) destruct Hok as [Hok1 Hok2]. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I].
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm).
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2.
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]].
      rewrite E2'.
      simpl. eexists; split; [reflexivity | constructor; [exact Hv1 | exact Hv2]].
    + (* PFst *) rename Hok into Hok1. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      destruct v1; simpl in Hv1 |- *; try exact I.
      inversion Hv1; subst.
      simpl; eexists; split; [reflexivity | eassumption].
    + (* PSnd *) rename Hok into Hok1. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      destruct v1; simpl in Hv1 |- *; try exact I.
      inversion Hv1; subst.
      simpl; eexists; split; [reflexivity | eassumption].
    + (* PLet *) destruct Hok as [Hok1 Hok2]. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      destruct (rename_pyexpr ((x, fresh_name n1) :: env) (S n1) e2) as [e2' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm).
      assert (Hext : env_corr (S n1) ((x, fresh_name n1) :: env) ((x, v1) :: rho) ((fresh_name n1, v1') :: rho'))
        by (apply ec_cons; [lia | exact Hv1 | apply (env_corr_weaken n n1 env rho rho' Hn1 Henv)]).
      pose proof (IHfuel' e2 ((x, fresh_name n1) :: env) (S n1) ((x, v1) :: rho) ((fresh_name n1, v1') :: rho') Hok2 Hext) as H2.
      rewrite R2 in H2. simpl in H2. exact H2.
    + (* PFConst *) simpl. eexists; split; [reflexivity | constructor].
    + (* PFAdd *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFSub *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFMul *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFDiv *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFEq *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFLt *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFLe *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFOpp *) rename Hok into Hok1. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFAbs *) rename Hok into Hok1. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFSqrt *) rename Hok into Hok1. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFMax *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFMin *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFExp *) rename Hok into Hok1. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFLn *) rename Hok into Hok1. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PFPow *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PRepeat *) destruct Hok as [HokBody HokInit]. simpl.
      destruct (rename_pyexpr env n init) as [init' n1] eqn:R1.
      destruct (rename_pyexpr ((x, fresh_name n1) :: env) (S n1) body) as [body' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho init) as [v0|] eqn:E0; [| exact I].
      pose proof (IHfuel' init env n rho rho' HokInit Henv) as H0.
      rewrite E0, R1 in H0; simpl in H0; destruct H0 as [v0' [E0' Hv0]].
      rewrite E0'.
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone init env n) as Hm; rewrite R1 in Hm; exact Hm).
      apply piterate_corr.
      * exact Hv0.
      * intros u u' Hu.
        assert (Hext : env_corr (S n1) ((x, fresh_name n1) :: env) ((x, u) :: rho) ((fresh_name n1, u') :: rho'))
          by (apply ec_cons; [lia | exact Hu | apply (env_corr_weaken n n1 env rho rho' Hn1 Henv)]).
        pose proof (IHfuel' body ((x, fresh_name n1) :: env) (S n1) ((x, u) :: rho) ((fresh_name n1, u') :: rho') HokBody Hext) as H2.
        rewrite R2 in H2. simpl in H2. exact H2.
    + (* PDiv *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; destruct (Z.eqb _ 0); [exact I | eexists; split; [reflexivity | constructor]].
    + (* PMod *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; destruct (Z.eqb _ 0); [exact I | eexists; split; [reflexivity | constructor]].
    + (* PLam *) simpl.
      destruct (rename_pyexpr ((param, fresh_name n) :: env) (S n) body) as [body' n1] eqn:Rb.
      simpl. eexists; split; [reflexivity |].
      apply (vcorr_closure_lam param body rho env n (fresh_name n) body' rho');
        [exact Henv | exact Hok | simpl; rewrite Rb; reflexivity].
    + (* PRec *) simpl.
      destruct (rename_pyexpr ((param, fresh_name (S n)) :: (f, fresh_name n) :: env) (S (S n)) body)
        as [body' n1] eqn:Rb.
      simpl. eexists; split; [reflexivity |].
      apply (vcorr_closure_rec f param body rho env n (fresh_name n) (fresh_name (S n)) body' rho');
        [exact Henv | exact Hok | simpl; rewrite Rb; reflexivity].
    + (* PRecMut *) destruct Hok as [Hok1 Hok2]. simpl.
      destruct (rename_pyexpr
                  ((param1, fresh_name (S (S n))) :: (f1, fresh_name (S n)) :: (f2, fresh_name n) :: env)
                  (S (S (S (S n)))) body1) as [body1' n1] eqn:R1.
      destruct (rename_pyexpr
                  ((param2, fresh_name (S (S (S n)))) :: (f1, fresh_name (S n)) :: (f2, fresh_name n) :: env)
                  n1 body2) as [body2' n2] eqn:R2.
      simpl.
      eexists; split; [reflexivity |].
      constructor.
      * apply (vcorr_closuremut f1 param1 body1 f2 param2 body2 rho false env n
                 (fresh_name (S n)) (fresh_name (S (S n))) body1'
                 (fresh_name n) (fresh_name (S (S (S n)))) body2' rho');
          [exact Henv | exact Hok1 | exact Hok2 | simpl; rewrite R1, R2; reflexivity].
      * apply (vcorr_closuremut f1 param1 body1 f2 param2 body2 rho true env n
                 (fresh_name (S n)) (fresh_name (S (S n))) body1'
                 (fresh_name n) (fresh_name (S (S (S n)))) body2' rho');
          [exact Henv | exact Hok1 | exact Hok2 | simpl; rewrite R1, R2; reflexivity].
    + (* PApp *) destruct Hok as [HokFunc HokArg]. simpl.
      destruct (rename_pyexpr env n func) as [func' n1] eqn:R1.
      destruct (rename_pyexpr env n1 arg) as [arg' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho func) as [vf|] eqn:Ef; [| exact I].
      pose proof (IHfuel' func env n rho rho' HokFunc Henv) as H1.
      rewrite Ef, R1 in H1; simpl in H1; destruct H1 as [vf' [Ef' Hvf]].
      rewrite Ef'.
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone func env n) as Hm; rewrite R1 in Hm; exact Hm).
      assert (Harg : pyval_opt_corr (peval fuel' rho arg) (peval fuel' rho' arg'))
        by (pose proof (IHfuel' arg env n1 rho rho' HokArg (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
            rewrite R2 in H2; simpl in H2; exact H2).
      destruct vf; simpl in Hvf |- *; try exact I.
      * (* PVClosure *)
        destruct self as [f|].
        -- inversion Hvf; subst.
           simpl in H6.
           destruct (rename_pyexpr ((param, fresh_name (S n0)) :: (f, fresh_name n0) :: env0) (S (S n0)) body)
             as [bb nn] eqn:Rb.
           simpl in H6.
           injection H6 as Hyf Hyparam Hbb.
           subst yf yparam body'.
           destruct (peval fuel' rho arg) as [va|] eqn:Ea; [| exact I].
           destruct Harg as [va' [Ea' Hva]].
           rewrite Ea'.
           assert (Hext : env_corr (S (S n0)) ((param, fresh_name (S n0)) :: (f, fresh_name n0) :: env0)
                             ((param, va) :: (f, PVClosure (Some f) param body cenv) :: cenv)
                             ((fresh_name (S n0), va') :: (fresh_name n0, PVClosure (Some (fresh_name n0)) (fresh_name (S n0)) bb cenv') :: cenv')).
           { apply ec_cons; [lia | exact Hva |].
             apply ec_cons; [lia | | exact H4].
             apply (vcorr_closure_rec f param body cenv env0 n0 (fresh_name n0) (fresh_name (S n0)) bb cenv').
             - exact H4.
             - exact H5.
             - simpl. rewrite Rb. reflexivity. }
           pose proof (IHfuel' body ((param, fresh_name (S n0)) :: (f, fresh_name n0) :: env0) (S (S n0))
                         ((param, va) :: (f, PVClosure (Some f) param body cenv) :: cenv)
                         ((fresh_name (S n0), va') :: (fresh_name n0, PVClosure (Some (fresh_name n0)) (fresh_name (S n0)) bb cenv') :: cenv') H5 Hext) as Hb.
           rewrite Rb in Hb. simpl in Hb. exact Hb.
        -- inversion Hvf; subst.
           simpl in H5.
           destruct (rename_pyexpr ((param, fresh_name n0) :: env0) (S n0) body) as [bb nn] eqn:Rb.
           simpl in H5.
           injection H5 as Hyparam Hbb.
           subst yparam body'.
           destruct (peval fuel' rho arg) as [va|] eqn:Ea; [| exact I].
           destruct Harg as [va' [Ea' Hva]].
           rewrite Ea'.
           assert (Hext : env_corr (S n0) ((param, fresh_name n0) :: env0) ((param, va) :: cenv)
                             ((fresh_name n0, va') :: cenv'))
             by (apply ec_cons; [lia | exact Hva | exact H2]).
           pose proof (IHfuel' body ((param, fresh_name n0) :: env0) (S n0) ((param, va) :: cenv)
                         ((fresh_name n0, va') :: cenv') H4 Hext) as Hb.
           rewrite Rb in Hb. simpl in Hb. exact Hb.
      * (* PVClosureMut *)
        inversion Hvf; subst.
        simpl in H11.
        destruct (rename_pyexpr
                    ((param1, fresh_name (S (S n0))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                    (S (S (S (S n0)))) body1) as [bb1 nn1] eqn:Rb1.
        destruct (rename_pyexpr
                    ((param2, fresh_name (S (S (S n0)))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                    nn1 body2) as [bb2 nn2] eqn:Rb2.
        simpl in H11.
        injection H11 as Hyf1 Hyparam1 Hbb1 Hyf2 Hyparam2 Hbb2.
        subst yf1 yparam1 body1' yf2 yparam2 body2'.
        destruct (peval fuel' rho arg) as [va|] eqn:Ea; [| exact I].
        destruct Harg as [va' [Ea' Hva]].
        rewrite Ea'.
        destruct which.
        -- assert (Hext : env_corr (S (S (S (S n0))))
                     ((param2, fresh_name (S (S (S n0)))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                     ((param2, va) :: (f1, PVClosureMut f1 param1 body1 f2 param2 body2 cenv false)
                        :: (f2, PVClosureMut f1 param1 body1 f2 param2 body2 cenv true) :: cenv)
                     ((fresh_name (S (S (S n0))), va')
                        :: (fresh_name (S n0),
                             PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                               (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' false)
                        :: (fresh_name n0,
                             PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                               (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' true) :: cenv')).
           { apply ec_cons; [lia | exact Hva |].
             apply ec_cons; [lia | | apply ec_cons; [lia | | exact H8]].
             - apply (vcorr_closuremut f1 param1 body1 f2 param2 body2 cenv false env0 n0
                        (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                        (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv');
                 [exact H8 | exact H9 | exact H10 | simpl; rewrite Rb1, Rb2; reflexivity].
             - apply (vcorr_closuremut f1 param1 body1 f2 param2 body2 cenv true env0 n0
                        (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                        (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv');
                 [exact H8 | exact H9 | exact H10 | simpl; rewrite Rb1, Rb2; reflexivity]. }
           assert (Hnn1 : S (S (S (S n0))) <= nn1)
             by (pose proof (rename_pyexpr_monotone body1
                   ((param1, fresh_name (S (S n0))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                   (S (S (S (S n0))))) as Hm;
                 rewrite Rb1 in Hm; exact Hm).
           pose proof (IHfuel' body2
                         ((param2, fresh_name (S (S (S n0)))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                         nn1
                         ((param2, va) :: (f1, PVClosureMut f1 param1 body1 f2 param2 body2 cenv false)
                            :: (f2, PVClosureMut f1 param1 body1 f2 param2 body2 cenv true) :: cenv)
                         ((fresh_name (S (S (S n0))), va')
                            :: (fresh_name (S n0),
                                 PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                                   (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' false)
                            :: (fresh_name n0,
                                 PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                                   (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' true) :: cenv')
                         H10
                         (env_corr_weaken (S (S (S (S n0)))) nn1
                            ((param2, fresh_name (S (S (S n0)))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                            ((param2, va) :: (f1, PVClosureMut f1 param1 body1 f2 param2 body2 cenv false)
                               :: (f2, PVClosureMut f1 param1 body1 f2 param2 body2 cenv true) :: cenv)
                            ((fresh_name (S (S (S n0))), va')
                               :: (fresh_name (S n0),
                                    PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                                      (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' false)
                               :: (fresh_name n0,
                                    PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                                      (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' true) :: cenv')
                            Hnn1 Hext)) as Hb.
           rewrite Rb2 in Hb. simpl in Hb. exact Hb.
        -- assert (Hext : env_corr (S (S (S (S n0))))
                     ((param1, fresh_name (S (S n0))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                     ((param1, va) :: (f1, PVClosureMut f1 param1 body1 f2 param2 body2 cenv false)
                        :: (f2, PVClosureMut f1 param1 body1 f2 param2 body2 cenv true) :: cenv)
                     ((fresh_name (S (S n0)), va')
                        :: (fresh_name (S n0),
                             PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                               (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' false)
                        :: (fresh_name n0,
                             PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                               (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' true) :: cenv')).
           { apply ec_cons; [lia | exact Hva |].
             apply ec_cons; [lia | | apply ec_cons; [lia | | exact H8]].
             - apply (vcorr_closuremut f1 param1 body1 f2 param2 body2 cenv false env0 n0
                        (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                        (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv');
                 [exact H8 | exact H9 | exact H10 | simpl; rewrite Rb1, Rb2; reflexivity].
             - apply (vcorr_closuremut f1 param1 body1 f2 param2 body2 cenv true env0 n0
                        (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                        (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv');
                 [exact H8 | exact H9 | exact H10 | simpl; rewrite Rb1, Rb2; reflexivity]. }
           pose proof (IHfuel' body1
                         ((param1, fresh_name (S (S n0))) :: (f1, fresh_name (S n0)) :: (f2, fresh_name n0) :: env0)
                         (S (S (S (S n0))))
                         ((param1, va) :: (f1, PVClosureMut f1 param1 body1 f2 param2 body2 cenv false)
                            :: (f2, PVClosureMut f1 param1 body1 f2 param2 body2 cenv true) :: cenv)
                         ((fresh_name (S (S n0)), va')
                            :: (fresh_name (S n0),
                                 PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                                   (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' false)
                            :: (fresh_name n0,
                                 PVClosureMut (fresh_name (S n0)) (fresh_name (S (S n0))) bb1
                                   (fresh_name n0) (fresh_name (S (S (S n0)))) bb2 cenv' true) :: cenv') H9 Hext) as Hb.
           rewrite Rb1 in Hb. simpl in Hb. exact Hb.
      * (* PVClosureGroup *)
        inversion Hvf; subst.
        destruct (peval fuel' rho arg) as [va|] eqn:Ea; [| exact I].
        destruct Harg as [va' [Ea' Hva]].
        rewrite Ea'.
        destruct (plookup_group_fn fns self_name) as [[param body]|] eqn:Elook; [| exact I].
        pose proof (plookup_group_fn_corr env0 n0 fns fns' (snd (rename_pyexpr env0 n0 (PRecGroup fns)))
                      H5 self_name param body Elook) as [body' [sd [Hsd [Hplook Hbeq]]]].
        rewrite Hplook.
        assert (HokBody : pyexpr_recgroup_ok body).
        { destruct H4 as [_ Hbodies].
          pose proof (plookup_group_fn_in fns self_name param body Elook) as Hin.
          clear - Hbodies Hin.
          induction fns as [| [[f0 p0] b0] rest IH]; simpl in Hin, Hbodies.
          - contradiction.
          - destruct Hbodies as [Hok0 Hoks].
            destruct Hin as [Heq | Hin].
            + injection Heq as -> -> ->. exact Hok0.
            + apply (IH Hoks Hin). }
        assert (Hrb : env_corr n0
                  (List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env0)
                  (recgroup_build_bindings fns fns cenv)
                  (recgroup_build_bindings fns' fns' cenv'))
          by (apply (recgroup_rebuild_corr env0 n0 cenv cenv' H2 fns fns'
                       (snd (rename_pyexpr env0 n0 (PRecGroup fns))) H5 H4)).
        rewrite !recgroup_build_bindings_eq.
        assert (Hext : env_corr (S sd)
                  ((param, fresh_name sd) :: List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env0)
                  ((param, va) :: recgroup_build_bindings fns fns cenv)
                  ((fresh_name sd, va') :: recgroup_build_bindings fns' fns' cenv'))
          by (apply ec_cons; [lia | exact Hva | apply (env_corr_weaken n0 sd _ _ _ Hsd Hrb)]).
        pose proof (IHfuel' body
                      ((param, fresh_name sd) :: List.app (map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) env0)
                      (S sd)
                      ((param, va) :: recgroup_build_bindings fns fns cenv)
                      ((fresh_name sd, va') :: recgroup_build_bindings fns' fns' cenv')
                      HokBody Hext) as Hb.
        rewrite Hbeq in Hb. simpl in Hb. exact Hb.
    + (* PNil *) simpl. eexists; split; [reflexivity | constructor; constructor].
    + (* PCons *) destruct Hok as [Hok1 Hok2]. simpl.
      destruct (rename_pyexpr env n hd) as [hd' n1] eqn:R1.
      destruct (rename_pyexpr env n1 tl) as [tl' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho hd) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' hd env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      destruct (peval fuel' rho tl) as [v2|] eqn:E2; [| exact I].
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone hd env n) as Hm; rewrite R1 in Hm; exact Hm).
      pose proof (IHfuel' tl env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2.
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]].
      rewrite E2'.
      destruct v2; simpl in Hv2 |- *; try exact I.
      inversion Hv2; subst.
      simpl. eexists; split; [reflexivity | constructor; constructor; [exact Hv1 | eassumption]].
    + (* PListMatch *) destruct Hok as [HokS [HokNc HokCc]]. simpl.
      destruct (rename_pyexpr env n scrutinee) as [scrutinee' n0] eqn:R0.
      destruct (rename_pyexpr env n0 nilcase) as [nilcase' n1] eqn:R1.
      destruct (rename_pyexpr ((hd, fresh_name (S n1)) :: (tl, fresh_name n1) :: env) (S (S n1)) conscase)
        as [conscase' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho scrutinee) as [vs|] eqn:Es; [| exact I].
      pose proof (IHfuel' scrutinee env n rho rho' HokS Henv) as Hs.
      rewrite Es, R0 in Hs; simpl in Hs; destruct Hs as [vs' [Es' Hvs]].
      rewrite Es'.
      assert (Hn0 : n <= n0) by (pose proof (rename_pyexpr_monotone scrutinee env n) as Hm; rewrite R0 in Hm; exact Hm).
      assert (Hn1 : n0 <= n1) by (pose proof (rename_pyexpr_monotone nilcase env n0) as Hm; rewrite R1 in Hm; exact Hm).
      destruct vs; simpl in Hvs |- *; try exact I.
      inversion Hvs; subst.
      match goal with
      | H : Forall2 value_corr ?l ?l' |- _ => destruct H as [| hv hv' tvs tvs' Hhv Htl]
      end; simpl.
      * pose proof (IHfuel' nilcase env n0 rho rho' HokNc (env_corr_weaken n n0 env rho rho' Hn0 Henv)) as Hnc.
        rewrite R1 in Hnc. simpl in Hnc. exact Hnc.
      * assert (Hn0n1 : n <= n1) by lia.
        assert (Hext : env_corr (S (S n1)) ((hd, fresh_name (S n1)) :: (tl, fresh_name n1) :: env)
                          ((hd, hv) :: (tl, PVList tvs) :: rho)
                          ((fresh_name (S n1), hv') :: (fresh_name n1, PVList tvs') :: rho')).
        { apply ec_cons; [lia | exact Hhv |].
          apply ec_cons; [lia | constructor; exact Htl | apply (env_corr_weaken n n1 env rho rho' Hn0n1 Henv)]. }
        pose proof (IHfuel' conscase ((hd, fresh_name (S n1)) :: (tl, fresh_name n1) :: env) (S (S n1))
                      ((hd, hv) :: (tl, PVList tvs) :: rho)
                      ((fresh_name (S n1), hv') :: (fresh_name n1, PVList tvs') :: rho') HokCc Hext) as Hcc.
        rewrite R2 in Hcc. simpl in Hcc. exact Hcc.
    + (* PRecord *) destruct Hok as [Hok1 Hok2]. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I].
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm).
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2.
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]].
      rewrite E2'.
      simpl. eexists; split; [reflexivity | constructor; [exact Hv1 | exact Hv2]].
    + (* PField *) rename Hok into Hok1. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      destruct v1; simpl in Hv1 |- *; try exact I.
      inversion Hv1; subst.
      simpl.
      destruct (String.eqb name k1); [eexists; split; [reflexivity | eassumption] |].
      destruct (String.eqb name k2); [eexists; split; [reflexivity | eassumption] | exact I].
    + (* PInl *) rename Hok into Hok1. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'. simpl. eexists; split; [reflexivity | constructor; exact Hv1].
    + (* PInr *) rename Hok into Hok1. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'. simpl. eexists; split; [reflexivity | constructor; exact Hv1].
    + (* PCase *) destruct Hok as [HokS [Hok1 Hok2]]. simpl.
      destruct (rename_pyexpr env n scrutinee) as [scrutinee' n0] eqn:R0.
      destruct (rename_pyexpr ((x1, fresh_name n0) :: env) (S n0) case1) as [case1' n1] eqn:R1.
      destruct (rename_pyexpr ((x2, fresh_name n1) :: env) (S n1) case2) as [case2' n2] eqn:R2.
      simpl.
      destruct (peval fuel' rho scrutinee) as [vs|] eqn:Es; [| exact I].
      pose proof (IHfuel' scrutinee env n rho rho' HokS Henv) as Hs.
      rewrite Es, R0 in Hs; simpl in Hs; destruct Hs as [vs' [Es' Hvs]].
      rewrite Es'.
      assert (Hn0 : n <= n0) by (pose proof (rename_pyexpr_monotone scrutinee env n) as Hm; rewrite R0 in Hm; exact Hm).
      assert (Hn1 : n0 <= n1) by (pose proof (rename_pyexpr_monotone case1 ((x1, fresh_name n0) :: env) (S n0)) as Hm; rewrite R1 in Hm; simpl in Hm; lia).
      destruct vs; simpl in Hvs |- *; try exact I.
      * inversion Hvs; subst.
        assert (Hext : env_corr (S n0) ((x1, fresh_name n0) :: env) ((x1, vs) :: rho) ((fresh_name n0, v') :: rho'))
          by (apply ec_cons; [lia | eassumption | apply (env_corr_weaken n n0 env rho rho' Hn0 Henv)]).
        pose proof (IHfuel' case1 ((x1, fresh_name n0) :: env) (S n0) ((x1, vs) :: rho) ((fresh_name n0, v') :: rho') Hok1 Hext) as H1.
        rewrite R1 in H1. simpl in H1. exact H1.
      * inversion Hvs; subst.
        assert (Hn0n1 : n <= n1) by lia.
        assert (Hext : env_corr (S n1) ((x2, fresh_name n1) :: env) ((x2, vs) :: rho) ((fresh_name n1, v') :: rho'))
          by (apply ec_cons; [lia | eassumption | apply (env_corr_weaken n n1 env rho rho' Hn0n1 Henv)]).
        pose proof (IHfuel' case2 ((x2, fresh_name n1) :: env) (S n1) ((x2, vs) :: rho) ((fresh_name n1, v') :: rho') Hok2 Hext) as H2.
        rewrite R2 in H2. simpl in H2. exact H2.
    + (* PStrConst *) simpl. eexists; split; [reflexivity | constructor].
    + (* PStrConcat *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PStrEq *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      destruct (rename_pyexpr env n1 e2) as [e2' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho e2) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone e1 env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' e2 env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      simpl; eexists; split; [reflexivity | constructor].
    + (* PRecordN *) simpl.
      assert (Haux : forall flds,
        (fix fok (fs : list (var * pyexpr)) : Prop :=
           match fs with [] => True | (_, fe) :: rest => pyexpr_recgroup_ok fe /\ fok rest end) flds ->
        forall n0, env_corr n0 env rho rho' ->
        pyval_optlist_corr
          ((fix peval_fields (fs : list (var * pyexpr)) : option (list (var * pyvalue)) :=
              match fs with
              | [] => Some []
              | (k0, fe0) :: rest =>
                  match peval fuel' rho fe0, peval_fields rest with
                  | Some v0, Some vs => Some ((k0, v0) :: vs)
                  | _, _ => None
                  end
              end) flds)
          ((fix peval_fields (fs : list (var * pyexpr)) : option (list (var * pyvalue)) :=
              match fs with
              | [] => Some []
              | (k0, fe0) :: rest =>
                  match peval fuel' rho' fe0, peval_fields rest with
                  | Some v0, Some vs => Some ((k0, v0) :: vs)
                  | _, _ => None
                  end
              end)
             (fst ((fix go (fs : list (var * pyexpr)) (n1 : nat) : list (var * pyexpr) * nat :=
                      match fs with
                      | [] => ([], n1)
                      | (k0, fe0) :: rest =>
                          let '(fe'0, n2) := rename_pyexpr env n1 fe0 in
                          let '(rest', n3) := go rest n2 in
                          ((k0, fe'0) :: rest', n3)
                      end) flds n0)))).
      { induction flds as [| [k0 fe0] rest IHr]; intros Hokf n0 Henv0.
        - simpl. eexists; split; [reflexivity | constructor].
        - destruct Hokf as [HokFe0 HokRest].
          destruct (rename_pyexpr env n0 fe0) as [fe0' n1] eqn:R0.
          destruct ((fix go (fs : list (var * pyexpr)) (n1 : nat) : list (var * pyexpr) * nat :=
                       match fs with
                       | [] => ([], n1)
                       | (k1, fe1) :: rest' =>
                           let '(fe1', n2) := rename_pyexpr env n1 fe1 in
                           let '(rest'', n3) := go rest' n2 in
                           ((k1, fe1') :: rest'', n3)
                       end) rest n1) as [rest'' n3] eqn:Rgo.
          simpl.
          destruct (peval fuel' rho fe0) as [v0|] eqn:E0; [| exact I].
          pose proof (IHfuel' fe0 env n0 rho rho' HokFe0 Henv0) as H0.
          rewrite E0, R0 in H0; simpl in H0; destruct H0 as [v0' [E0' Hv0]].
          rewrite E0'.
          assert (Hn1 : n0 <= n1) by (pose proof (rename_pyexpr_monotone fe0 env n0) as Hm; rewrite R0 in Hm; exact Hm).
          pose proof (IHr HokRest n1 (env_corr_weaken n0 n1 env rho rho' Hn1 Henv0)) as IH.
          rewrite Rgo in IH. simpl in IH.
          destruct ((fix peval_fields (fs : list (var * pyexpr)) : option (list (var * pyvalue)) :=
                       match fs with
                       | [] => Some []
                       | (k1, fe1) :: rest' =>
                           match peval fuel' rho fe1, peval_fields rest' with
                           | Some v1, Some vs => Some ((k1, v1) :: vs)
                           | _, _ => None
                           end
                       end) rest) as [vs|] eqn:Erest; [| exact I].
          destruct IH as [vs' [Erest' Hvs]].
          rewrite Erest'.
          simpl. eexists; split; [reflexivity | constructor; [split; [reflexivity | exact Hv0] | exact Hvs]]. }
      destruct ((fix go (fs : list (var * pyexpr)) (n1 : nat) : list (var * pyexpr) * nat :=
                   match fs with
                   | [] => ([], n1)
                   | (k0, fe0) :: rest =>
                       let '(fe0', n2) := rename_pyexpr env n1 fe0 in
                       let '(rest', n3) := go rest n2 in
                       ((k0, fe0') :: rest', n3)
                   end) fields n) as [fields'' n1] eqn:Rgo.
      simpl.
      destruct ((fix peval_fields (fs : list (var * pyexpr)) : option (list (var * pyvalue)) :=
                   match fs with
                   | [] => Some []
                   | (k0, fe0) :: rest =>
                       match peval fuel' rho fe0, peval_fields rest with
                       | Some v0, Some vs => Some ((k0, v0) :: vs)
                       | _, _ => None
                       end
                   end) fields) as [vs|] eqn:Efields; [| exact I].
      pose proof (Haux fields Hok n Henv) as HA.
      rewrite Efields, Rgo in HA. simpl in HA.
      destruct HA as [vs' [Efields' Hvs]].
      rewrite Efields'.
      simpl. eexists; split; [reflexivity | constructor; exact Hvs].
    + (* PFieldN *) rename Hok into Hok1. simpl.
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1.
      simpl.
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I].
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1.
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]].
      rewrite E1'.
      destruct v1; simpl in Hv1 |- *; try exact I.
      inversion Hv1; subst.
      simpl. apply pvrecordn_field_corr. eassumption.
    + (* PRecGroup *)
      destruct (rename_pyexpr env n (PRecGroup fns)) as [erg n'] eqn:Rg0.
      assert (Hren : rename_pyexpr env n (PRecGroup fns) = (erg, n')) by exact Rg0.
      cbn [rename_pyexpr] in Rg0.
      set (envfs := map (fun fpb => (fst (fst fpb), fst (fst fpb))) fns) in Rg0.
      set (env' := List.app envfs env) in Rg0.
      destruct ((fix go (fs : list (var * var * pyexpr)) (n0 : nat) : list (var * var * pyexpr) * nat :=
                   match fs with
                   | [] => ([], n0)
                   | (f, p, b) :: rest =>
                       let yp := fresh_name n0 in
                       let '(b', n1) := rename_pyexpr ((p, yp) :: env') (S n0) b in
                       let '(rest', n2) := go rest n1 in
                       ((f, yp, b') :: rest', n2)
                   end) fns n) as [fns' n''] eqn:Ego.
      injection Rg0 as Hrg1 Hrg2. subst erg n'.
      assert (Hren2 : rename_pyexpr env n (PRecGroup fns)
                      = (PRecGroup fns', snd (rename_pyexpr env n (PRecGroup fns))))
        by (rewrite Hren; reflexivity).
      simpl.
      rewrite !recgroup_build_fields_eq.
      assert (Hbf : forall fs,
                (forall f p b, In (f, p, b) fs -> In (f, p, b) fns) ->
                forall n1,
                Forall2 (fun kv kv' => fst kv = fst kv' /\ value_corr (snd kv) (snd kv'))
                  (recgroup_build_fields fs fns rho)
                  (recgroup_build_fields
                     (fst ((fix go (gs1 : list (var * var * pyexpr)) (m : nat)
                                : list (var * var * pyexpr) * nat :=
                              match gs1 with
                              | [] => ([], m)
                              | (f, p, b) :: rest =>
                                  let yp := fresh_name m in
                                  let '(b', m0) := rename_pyexpr ((p, yp) :: env') (S m) b in
                                  let '(rest', m2) := go rest m0 in
                                  ((f, yp, b') :: rest', m2)
                              end) fs n1))
                     fns' rho')).
      { induction fs as [| [[f p] b] fs' IHfs]; intros Hsub n1; simpl.
        - constructor.
        - assert (Hin : In (f, p, b) fns) by (apply Hsub; left; reflexivity).
          assert (Hsub' : forall f0 p0 b0, In (f0, p0, b0) fs' -> In (f0, p0, b0) fns)
            by (intros f0 p0 b0 Hin0; apply Hsub; right; exact Hin0).
          destruct (rename_pyexpr ((p, fresh_name n1) :: env') (S n1) b) as [b' m0] eqn:Eb.
          destruct ((fix go (gs1 : list (var * var * pyexpr)) (m : nat)
                         : list (var * var * pyexpr) * nat :=
                       match gs1 with
                       | [] => ([], m)
                       | (f0, p0, b0) :: rest =>
                           let yp := fresh_name m in
                           let '(b'0, m1) := rename_pyexpr ((p0, yp) :: env') (S m) b0 in
                           let '(rest', m2) := go rest m1 in
                           ((f0, yp, b'0) :: rest', m2)
                       end) fs' m0) as [fs'' m2] eqn:Ego2.
          cbn [recgroup_build_fields fst snd].
          constructor.
          + split; [reflexivity |].
            apply (vcorr_closuregroup fns rho f env n fns').
            * exact Henv.
            * exact Hok.
            * exact Hren2.
          + pose proof (IHfs Hsub' m0) as IH2. rewrite Ego2 in IH2. simpl in IH2. exact IH2. }
      pose proof (Hbf fns (fun f p b H => H) n) as Hb.
      rewrite Ego in Hb. simpl in Hb.
      eexists; split; [reflexivity | constructor; exact Hb].
    + (* PNone *) simpl; eexists; split; [reflexivity | constructor].
    + (* PSome *) rename Hok into Hok1. simpl;
      destruct (rename_pyexpr env n e1) as [e1' n1] eqn:R1;
      simpl;
      destruct (peval fuel' rho e1) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' e1 env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      eexists; split; [reflexivity | constructor; exact Hv1].
    + (* POptionMatch *) destruct Hok as [HokS [HokN Hok1]]. simpl.
      destruct (rename_pyexpr env n scrutinee) as [scrutinee' n0] eqn:R0.
      destruct (rename_pyexpr env n0 nonecase) as [nonecase' n0'] eqn:R0'.
      destruct (rename_pyexpr ((x, fresh_name n0') :: env) (S n0') somecase) as [somecase' n1] eqn:R1.
      simpl.
      destruct (peval fuel' rho scrutinee) as [vs|] eqn:Es; [| exact I].
      pose proof (IHfuel' scrutinee env n rho rho' HokS Henv) as Hs.
      rewrite Es, R0 in Hs; simpl in Hs; destruct Hs as [vs' [Es' Hvs]].
      rewrite Es'.
      assert (Hn0 : n <= n0) by (pose proof (rename_pyexpr_monotone scrutinee env n) as Hm; rewrite R0 in Hm; exact Hm).
      assert (Hn0' : n0 <= n0') by (pose proof (rename_pyexpr_monotone nonecase env n0) as Hm; rewrite R0' in Hm; exact Hm).
      destruct vs; simpl in Hvs |- *; try exact I.
      * inversion Hvs; subst.
        pose proof (IHfuel' nonecase env n0 rho rho' HokN (env_corr_weaken n n0 env rho rho' Hn0 Henv)) as Hn.
        rewrite R0' in Hn. simpl in Hn. exact Hn.
      * inversion Hvs; subst.
        assert (Hn0n0' : n <= n0') by lia.
        assert (Hext : env_corr (S n0') ((x, fresh_name n0') :: env) ((x, vs) :: rho) ((fresh_name n0', v') :: rho'))
          by (apply ec_cons; [lia | eassumption | apply (env_corr_weaken n n0' env rho rho' Hn0n0' Henv)]).
        pose proof (IHfuel' somecase ((x, fresh_name n0') :: env) (S n0') ((x, vs) :: rho) ((fresh_name n0', v') :: rho') Hok1 Hext) as H1.
        rewrite R1 in H1. simpl in H1. exact H1.
    + (* PArrConst *) simpl.
      assert (Haux : forall xs,
        (fix fok (xs0 : list pyexpr) : Prop :=
           match xs0 with [] => True | e1 :: rest => pyexpr_recgroup_ok e1 /\ fok rest end) xs ->
        forall n0, env_corr n0 env rho rho' ->
        pyval_optarr_corr
          ((fix peval_elts (xs0 : list pyexpr) : option (list pyvalue) :=
              match xs0 with
              | [] => Some []
              | e1 :: rest =>
                  match peval fuel' rho e1, peval_elts rest with
                  | Some v, Some vs => Some (v :: vs)
                  | _, _ => None
                  end
              end) xs)
          ((fix peval_elts (xs0 : list pyexpr) : option (list pyvalue) :=
              match xs0 with
              | [] => Some []
              | e1 :: rest =>
                  match peval fuel' rho' e1, peval_elts rest with
                  | Some v, Some vs => Some (v :: vs)
                  | _, _ => None
                  end
              end)
             (fst ((fix go (xs0 : list pyexpr) (n1 : nat) : list pyexpr * nat :=
                      match xs0 with
                      | [] => ([], n1)
                      | e1 :: rest =>
                          let '(e1', n2) := rename_pyexpr env n1 e1 in
                          let '(rest', n3) := go rest n2 in
                          (e1' :: rest', n3)
                      end) xs n0)))).
      { induction xs as [| e0 rest IHr]; intros Hokx n0 Henv0.
        - simpl. eexists; split; [reflexivity | constructor].
        - destruct Hokx as [HokE0 HokRest].
          destruct (rename_pyexpr env n0 e0) as [e0' n1] eqn:R0.
          destruct ((fix go (xs0 : list pyexpr) (n1 : nat) : list pyexpr * nat :=
                       match xs0 with
                       | [] => ([], n1)
                       | e1 :: rest' =>
                           let '(e1', n2) := rename_pyexpr env n1 e1 in
                           let '(rest'', n3) := go rest' n2 in
                           (e1' :: rest'', n3)
                       end) rest n1) as [rest'' n3] eqn:Rgo.
          simpl.
          destruct (peval fuel' rho e0) as [v0|] eqn:E0; [| exact I].
          pose proof (IHfuel' e0 env n0 rho rho' HokE0 Henv0) as H0.
          rewrite E0, R0 in H0; simpl in H0; destruct H0 as [v0' [E0' Hv0]].
          rewrite E0'.
          assert (Hn1 : n0 <= n1) by (pose proof (rename_pyexpr_monotone e0 env n0) as Hm; rewrite R0 in Hm; exact Hm).
          pose proof (IHr HokRest n1 (env_corr_weaken n0 n1 env rho rho' Hn1 Henv0)) as IH.
          rewrite Rgo in IH. simpl in IH.
          destruct ((fix peval_elts (xs0 : list pyexpr) : option (list pyvalue) :=
                       match xs0 with
                       | [] => Some []
                       | e1 :: rest' =>
                           match peval fuel' rho e1, peval_elts rest' with
                           | Some v1, Some vs => Some (v1 :: vs)
                           | _, _ => None
                           end
                       end) rest) as [vs|] eqn:Erest; [| exact I].
          destruct IH as [vs' [Erest' Hvs]].
          rewrite Erest'.
          simpl. eexists; split; [reflexivity | constructor; [exact Hv0 | exact Hvs]]. }
      destruct ((fix go (xs0 : list pyexpr) (n1 : nat) : list pyexpr * nat :=
                   match xs0 with
                   | [] => ([], n1)
                   | e1 :: rest =>
                       let '(e1', n2) := rename_pyexpr env n1 e1 in
                       let '(rest', n3) := go rest n2 in
                       (e1' :: rest', n3)
                   end) es n) as [es'' n1] eqn:Rgo.
      simpl.
      destruct ((fix peval_elts (xs0 : list pyexpr) : option (list pyvalue) :=
                   match xs0 with
                   | [] => Some []
                   | e1 :: rest =>
                       match peval fuel' rho e1, peval_elts rest with
                       | Some v1, Some vs => Some (v1 :: vs)
                       | _, _ => None
                       end
                   end) es) as [vs|] eqn:Ees; [| exact I].
      pose proof (Haux es Hok n Henv) as HA.
      rewrite Ees, Rgo in HA. simpl in HA.
      destruct HA as [vs' [Ees' Hvs]].
      rewrite Ees'.
      simpl. eexists; split; [reflexivity | constructor; exact Hvs].
    + (* PArrGet *) destruct Hok as [Hok1 Hok2]. simpl;
      destruct (rename_pyexpr env n arr) as [arr' n1] eqn:R1;
      destruct (rename_pyexpr env n1 idx) as [idx' n2] eqn:R2;
      simpl;
      destruct (peval fuel' rho arr) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' arr env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho idx) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone arr env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' idx env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst.
      simpl. destruct (Z.leb 0 _); [| exact I].
      apply Forall2_value_corr_nth_error. eassumption.
    + (* PArrSet *) destruct Hok as [Hok1 [Hok2 Hok3]]. simpl;
      destruct (rename_pyexpr env n arr) as [arr' n1] eqn:R1;
      destruct (rename_pyexpr env n1 idx) as [idx' n2] eqn:R2;
      destruct (rename_pyexpr env n2 val) as [val' n3] eqn:R3;
      simpl;
      destruct (peval fuel' rho arr) as [v1|] eqn:E1; [| exact I];
      pose proof (IHfuel' arr env n rho rho' Hok1 Henv) as H1;
      rewrite E1, R1 in H1; simpl in H1; destruct H1 as [v1' [E1' Hv1]];
      rewrite E1';
      destruct v1; simpl in Hv1 |- *; try exact I; inversion Hv1; subst;
      destruct (peval fuel' rho idx) as [v2|] eqn:E2; [| exact I];
      assert (Hn1 : n <= n1) by (pose proof (rename_pyexpr_monotone arr env n) as Hm; rewrite R1 in Hm; exact Hm);
      pose proof (IHfuel' idx env n1 rho rho' Hok2 (env_corr_weaken n n1 env rho rho' Hn1 Henv)) as H2;
      rewrite E2, R2 in H2; simpl in H2; destruct H2 as [v2' [E2' Hv2]];
      rewrite E2';
      destruct v2; simpl in Hv2 |- *; try exact I; inversion Hv2; subst;
      destruct (peval fuel' rho val) as [v3|] eqn:E3; [| exact I];
      assert (Hn2 : n1 <= n2) by (pose proof (rename_pyexpr_monotone idx env n1) as Hm; rewrite R2 in Hm; exact Hm);
      assert (Hn02 : n <= n2) by lia;
      pose proof (IHfuel' val env n2 rho rho' Hok3 (env_corr_weaken n n2 env rho rho' Hn02 Henv)) as H3;
      rewrite E3, R3 in H3; simpl in H3; destruct H3 as [v3' [E3' Hv3]];
      rewrite E3'.
      simpl. rewrite <- (Forall2_value_corr_length _ _ ltac:(eassumption)).
      destruct (Z.leb 0 _); [| exact I].
      destruct (Nat.ltb _ _); [| exact I].
      rewrite !skipn_S_unfold.
      eexists; split; [reflexivity | apply vcorr_array;
        apply Forall2_value_corr_app;
        [apply Forall2_value_corr_firstn; eassumption |
         apply Forall2_cons; [exact Hv3 | apply Forall2_value_corr_skipn; eassumption]]].
Qed.
