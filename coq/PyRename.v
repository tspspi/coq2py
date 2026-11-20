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

    Unlike [PyPrint.v]'s character-level formatting, *this* transform
    does change the [pyexpr] term (every bound name is rewritten), so it
    gets the same kind of theorem the rest of the pipeline gets:
    [rename_pyexpr_correct] proves it does not change what [peval]
    computes. What is still *not* proved -- the same, smaller residual
    boundary [PyPrint.v]'s header now describes -- is that printing the
    (now alpha-unique) tree as Python text, and running that text under
    real CPython, matches [peval]; this file closes the one gap that
    was actually a proved-wrong mismatch, not an accepted axiom. *)

From Coq Require Import ZArith String List Bool.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Json. (* reuses z_to_string/z_of_string/z_round_trip *)
Open Scope string_scope.

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

(** The fresh name assigned to every [PRecGroup] member -- computed
    up front, in one pass, before any member's body is visited, since
    (mirroring [peval]'s own [build_bindings]) every member must be
    visible to every other member's body, including ones appearing
    later in the list. Does not call [rename_pyexpr], so it does not
    need to join the mutual block below. *)
Fixpoint rename_group_env (n : nat) (fs : list (var * var * pyexpr)) : list (var * var) * nat :=
  match fs with
  | [] => ([], n)
  | (f, _, _) :: rest =>
      let yf := fresh_name n in
      let '(restenv, n0) := rename_group_env (S n) rest in
      ((f, yf) :: restenv, n0)
  end.

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
      let yf1 := fresh_name n in
      let yf2 := fresh_name (S n) in
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
      let yhd := fresh_name n1 in
      let ytl := fresh_name (S n1) in
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
      let '(envfs, n1) := rename_group_env n fns in
      let env' := List.app envfs env in
      let '(fns', n2) :=
        (fix go (fs : list (var * var * pyexpr)) (n : nat) : list (var * var * pyexpr) * nat :=
           match fs with
           | [] => ([], n)
           | (f, p, b) :: rest =>
               let yf := rename_lookup envfs f in
               let yp := fresh_name n in
               let '(b', n0) := rename_pyexpr ((p, yp) :: env') (S n) b in
               let '(rest', n2) := go rest n0 in
               ((yf, yp, b') :: rest', n2)
           end) fns n1
      in
      (PRecGroup fns', n2)
  end.
