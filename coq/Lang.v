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
    gets stuck, same as any other wrong-shape value).

    [ERepeat n x body init] is bounded iteration: evaluate [init] to a
    starting value, then apply [body] (with [x] bound to the current
    value) exactly [n] times, [n] a literal [nat] fixed at "compile
    time" -- not a runtime-computed count. Its own recursion is plain
    structural recursion on [n], needing no fuel on its own -- but seeing
    why that doesn't extend to real functions is exactly the motivation
    for the fuel parameter described next.

    [EDiv]/[EMod] are integer floor-division/modulo, matching Python's
    [//]/[%] exactly (including for negative operands -- Coq's [Z.div]/
    [Z.modulo] already use the same floor convention Python does, unlike
    OCaml's native [/]/[mod], which truncates toward zero; this is
    exactly why [ExtrOcamlZInt] declines to give them a native-[int]
    realizer, extracting their real recursive definition instead --
    slower, but correct, the same accepted tradeoff as [Z] not being
    arbitrary-precision). Division by zero is *undefined* here: [eval]
    gets stuck ([None]) on a zero divisor rather than reaching for
    [Z.div]'s own (silently total, defaults-to-0) convention, so that
    [eval]'s domain matches Python's own -- [//]/[%] raise
    [ZeroDivisionError] on a zero divisor too. See [eval_div_correct] for
    the precondition this buys: given [b <> 0], [EDiv]/[EMod] compute
    exactly [Z.div]/[Z.modulo], no more, no less.

    * Functions, closures, and why [eval] now needs fuel

    [ELam param body] builds a closure value ([VClosure]) capturing the
    *current* environment -- standard lexical scoping. [EApp func arg]
    applies one. [ERec f param body] is the recursive variant: inside
    [body], [EVar f] resolves to the closure itself (rebuilt and rebound
    on every call), which is what lets a function call itself -- there is
    deliberately no other way to write recursion in this language, so
    every recursive [expr] is visibly, syntactically recursive via
    [ERec], not accidentally so via some other combination.

    This is also why [eval] takes an explicit [fuel : nat] first
    argument, decremented by one on *every* call (the same fuel-as-
    recursion-governor pattern [Json.v]'s [parse_expr] already uses, for
    the same underlying reason). It is not an optional optimization: once
    a closure can be returned, stored, and re-applied, [EApp]'s case
    needs to evaluate a [body] that is *not* a structural subterm of the
    [expr] [eval] was originally called on (it is a subterm of wherever
    the closure was first built, possibly a value flowing through
    several other applications first) -- Coq's guardedness checker
    rejects exactly this shape of recursive call outright, as it must:
    this language can now express genuine, unbounded recursion (an
    [ERec] applied without a decreasing argument diverges, the same as in
    Python), so no *total* evaluator for it can exist without an explicit
    resource bound. Running out of fuel ([eval 0 _ _ = None], or fuel
    reaching [0] partway through) is "stuck" the same way an unbound
    variable or a wrong-shape value already is -- indistinguishable from
    any other [None], and *not* claimed to correspond to anything on the
    Python side (an infinite Python loop just doesn't return; there is no
    "ran out of fuel" exception to match against, so this is one place
    the source and target semantics only agree on *terminating* runs,
    stated as a hypothesis rather than silently assumed -- see
    [Translate.v]'s correctness theorem).

    [ENil]/[ECons]/[EListMatch] add lists -- a genuine new *inductive*
    value shape, not another scalar operator, and (together with
    [ERec]) this subset's first real "recurse over the structure of a
    value" pattern: [EListMatch scrutinee nilcase hd tl conscase]
    evaluates [scrutinee] and either runs [nilcase] (empty list) or
    binds [hd]/[tl] to the head and tail and runs [conscase] (non-empty)
    -- the same two-case shape [Coq.Lists.List.list]'s own [match] has.
    A list of the wrong shape (or a scrutinee that isn't a list at all)
    gets stuck, same as everywhere else.

    [ERecord k1 e1 k2 e2]/[EField name e] add named-field records --
    Gallina's record types, in miniature: deliberately capped at exactly
    two fields, the same way [EPair]/[VPair] are capped at two
    components rather than supporting arbitrary-arity tuples. A general
    N-field record would need [expr] to embed a *list* of fields, and
    while [eval] can process such a list just fine computationally (the
    same way it already processes a closure's captured environment or a
    list value), [Json.v]'s round-trip proof inducts directly on [expr]
    rather than on fuel, and Coq's auto-generated induction principle
    for [expr] does not hand back a usable inductive hypothesis for
    sub-expressions buried inside a list field -- fixing the arity at
    two sidesteps that entirely, with no loss of expressiveness (nest,
    the same way three-or-more-tuples already nest pairs: [ERecord "a"
    e1 "rest" (ERecord "b" e2 "c" e3)] is a genuine 3-field record).

    [ERecMut f1 param1 body1 f2 param2 body2] is [ERec]'s mutual-
    recursion cousin -- two functions that may each call *both* of
    themselves, returned together as [VPair clo1 clo2] (so the usual
    [EFst]/[EApp] or [ESnd]/[EApp] picks out and calls either one). As
    with records, this is deliberately capped at exactly two functions
    rather than an arbitrary mutually-recursive group, for the same
    underlying reason: a general group needs [expr] to embed a *list*
    of (name, param, body) triples, which [Json.v]'s structural
    induction on [expr] can't hand back a usable hypothesis for. Unlike
    [ERecord], the cap here isn't just a proof-engineering convenience
    -- it reflects a real representation choice: [VClosureMut] bundles
    *both* bodies into a single value (tagged with a [which : bool]
    saying which of the two it currently stands for), rather than two
    separate [VClosure]s each somehow pointing at the other -- Coq
    values have no cycles, so "two closures that capture each other" is
    only representable by each one carrying *all* the information
    needed to reconstruct either side, which is exactly what bundling
    both bodies together does. [EApp] reconstructs *both* siblings'
    bindings into the callee's environment on every call, the same way
    it already reconstructs [ERec]'s single self-binding.

    [EInl e]/[EInr e]/[ECase scrutinee x1 case1 x2 case2] round out the
    basic algebraic-data-type trio this subset now has: [EPair]/
    [ERecord] are *products* (a value of each component, always both),
    [EInl]/[EInr] are the dual *sum* (a value tagged as one of exactly
    two alternatives, [VInl]/[VInr] -- the same shape as Coq's own
    [sum]/[inl]/[inr]), and [ERec]/[ERecMut] give structural recursion
    over either. [ECase] is the eliminator: it evaluates [scrutinee]
    and runs [case1] with [x1] bound to the payload if it was [VInl],
    or [case2] with [x2] bound if it was [VInr] -- the same two-case
    shape [EListMatch] already has for [Nil]/[Cons], just for a sum
    type general enough to tag *any* value, not only lists. Like
    [EPair], there is deliberately no fixed arity limit to work around
    here: a sum of more than two alternatives already nests, the same
    way a 3-tuple nests two [EPair]s ([EInr (EInl e)] is "the third of
    three cases").

    [EStrConst s]/[EStrConcat e1 e2]/[EStrEq e1 e2] add a fifth scalar
    value shape, [VStr], alongside [VZ]/[VBool]/[VFloat] -- genuine
    first-class strings, not just the identifiers [var] was already
    used for everywhere else in this file. The honest restriction: a
    string *value* here is deliberately still exactly as restricted as
    an identifier ([EStrConst]'s payload has type [var], checked by
    [is_valid_ident] in [expr_idents_valid] the same way [EVar]'s is),
    not an arbitrary Unicode string -- reusing [Json.v]'s already-proven
    [quote_string]/[parse_qstring] identifier codec as-is, rather than
    building a second, general-purpose JSON string-escaping codec
    (quotes, backslashes, control characters) as a separate effort. *)

From Coq Require Import ZArith String List Bool.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition var := string.

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
  | EFLe (e1 e2 : expr)
  | ERepeat (n : nat) (x : var) (body init : expr)
  | EDiv (e1 e2 : expr)
  | EMod (e1 e2 : expr)
  | ELam (param : var) (body : expr)
  | ERec (f param : var) (body : expr)
  | ERecMut (f1 param1 : var) (body1 : expr) (f2 param2 : var) (body2 : expr)
  | EApp (func arg : expr)
  | ENil
  | ECons (hd tl : expr)
  | EListMatch (scrutinee nilcase : expr) (hd tl : var) (conscase : expr)
  | ERecord (k1 : var) (e1 : expr) (k2 : var) (e2 : expr)
  | EField (name : var) (e : expr)
  | EInl (e : expr)
  | EInr (e : expr)
  | ECase (scrutinee : expr) (x1 : var) (case1 : expr) (x2 : var) (case2 : expr)
  | EStrConst (s : var)
  | EStrConcat (e1 e2 : expr)
  | EStrEq (e1 e2 : expr).

(** A value is now possibly a function: [VClosure self param body cenv]
    is [fun param => body] (or, if [self = Some f], the same but with
    [f] bound to the closure itself inside [body]), closed over the
    environment [cenv] it was created in. [value] can refer to [expr]
    directly (for [body]) and to itself (for [cenv], via [list (var *
    value)]) because both are already fully defined above/structurally
    nested -- no forward reference or mutual-inductive declaration
    needed. *)
Inductive value : Type :=
  | VZ (z : Z)
  | VBool (b : bool)
  | VPair (v1 v2 : value)
  | VFloat (f : float)
  | VClosure (self : option var) (param : var) (body : expr) (cenv : list (var * value))
  | VList (vs : list value)
  | VRecord (k1 : var) (v1 : value) (k2 : var) (v2 : value)
  | VClosureMut (f1 param1 : var) (body1 : expr) (f2 param2 : var) (body2 : expr)
      (cenv : list (var * value)) (which : bool)
  | VInl (v : value)
  | VInr (v : value)
  | VStr (s : var).

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

(** Apply [f] to [v], then to that result, [n] times in total, stopping
    early (returning [None]) the first time [f] gets stuck. Parametrized
    over an arbitrary [f] rather than folded directly into [eval]'s
    [ERepeat] case so that this is a plain structural recursion on [n]
    with no dependency on [expr]/[eval] at all -- [eval] below just
    supplies [f] as a closure over one fixed [body]/[rho]/[fuel]. *)
Fixpoint iterate (n : nat) (f : value -> option value) (v : value) : option value :=
  match n with
  | O => Some v
  | S n' =>
      match f v with
      | Some v' => iterate n' f v'
      | None => None
      end
  end.

(** [fuel] bounds recursion depth through function application (see this
    file's header for why that's unavoidable once closures exist); every
    other case just passes [fuel'] through unchanged to its immediate
    sub-evaluations, the same uniform style [Json.v]'s [parse_expr]
    already uses its own fuel parameter with. *)
Fixpoint eval (fuel : nat) (rho : env) (e : expr) : option value :=
  match fuel with
  | O => None
  | S fuel' =>
  match e with
  | EConst z => Some (VZ z)
  | EBool b => Some (VBool b)
  | EVar x => lookup rho x
  | EAdd e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VZ (v1 + v2))
      | _, _ => None
      end
  | ESub e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VZ (v1 - v2))
      | _, _ => None
      end
  | EMul e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VZ (v1 * v2))
      | _, _ => None
      end
  | EEq e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VBool (Z.eqb v1 v2))
      | _, _ => None
      end
  | ELt e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VBool (Z.ltb v1 v2))
      | _, _ => None
      end
  | ELe e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ v1), Some (VZ v2) => Some (VBool (Z.leb v1 v2))
      | _, _ => None
      end
  | EAnd e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2))
      | _, _ => None
      end
  | EOr e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VBool b1), Some (VBool b2) => Some (VBool (orb b1 b2))
      | _, _ => None
      end
  | ENot e1 =>
      match eval fuel' rho e1 with
      | Some (VBool b) => Some (VBool (negb b))
      | _ => None
      end
  | EIf c e1 e2 =>
      match eval fuel' rho c with
      | Some (VBool true) => eval fuel' rho e1
      | Some (VBool false) => eval fuel' rho e2
      | _ => None
      end
  | EPair e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some v1, Some v2 => Some (VPair v1 v2)
      | _, _ => None
      end
  | EFst e1 =>
      match eval fuel' rho e1 with
      | Some (VPair v1 _) => Some v1
      | _ => None
      end
  | ESnd e1 =>
      match eval fuel' rho e1 with
      | Some (VPair _ v2) => Some v2
      | _ => None
      end
  | ELet x e1 e2 =>
      match eval fuel' rho e1 with
      | Some v1 => eval fuel' ((x, v1) :: rho) e2
      | None => None
      end
  | EFConst f => Some (VFloat f)
  | EFAdd e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 + f2)%float)
      | _, _ => None
      end
  | EFSub e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 - f2)%float)
      | _, _ => None
      end
  | EFMul e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 * f2)%float)
      | _, _ => None
      end
  | EFDiv e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VFloat (f1 / f2)%float)
      | _, _ => None
      end
  | EFEq e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VBool (f1 =? f2)%float)
      | _, _ => None
      end
  | EFLt e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VBool (f1 <? f2)%float)
      | _, _ => None
      end
  | EFLe e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VFloat f1), Some (VFloat f2) => Some (VBool (f1 <=? f2)%float)
      | _, _ => None
      end
  | ERepeat n x body init =>
      match eval fuel' rho init with
      | Some v0 => iterate n (fun v => eval fuel' ((x, v) :: rho) body) v0
      | None => None
      end
  | EDiv e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ a), Some (VZ b) => if Z.eqb b 0 then None else Some (VZ (Z.div a b))
      | _, _ => None
      end
  | EMod e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VZ a), Some (VZ b) => if Z.eqb b 0 then None else Some (VZ (Z.modulo a b))
      | _, _ => None
      end
  | ELam param body => Some (VClosure None param body rho)
  | ERec f param body => Some (VClosure (Some f) param body rho)
  | ERecMut f1 param1 body1 f2 param2 body2 =>
      Some (VPair (VClosureMut f1 param1 body1 f2 param2 body2 rho false)
                  (VClosureMut f1 param1 body1 f2 param2 body2 rho true))
  | EApp func arg =>
      match eval fuel' rho func, eval fuel' rho arg with
      | Some (VClosure self param body cenv), Some argv =>
          let cenv' :=
            match self with
            | None => cenv
            | Some fname => (fname, VClosure self param body cenv) :: cenv
            end in
          eval fuel' ((param, argv) :: cenv') body
      | Some (VClosureMut f1 param1 body1 f2 param2 body2 cenv which), Some argv =>
          let cenv' :=
            (f1, VClosureMut f1 param1 body1 f2 param2 body2 cenv false)
            :: (f2, VClosureMut f1 param1 body1 f2 param2 body2 cenv true)
            :: cenv in
          if which
          then eval fuel' ((param2, argv) :: cenv') body2
          else eval fuel' ((param1, argv) :: cenv') body1
      | _, _ => None
      end
  | ENil => Some (VList [])
  | ECons hd tl =>
      match eval fuel' rho hd, eval fuel' rho tl with
      | Some hv, Some (VList tvs) => Some (VList (hv :: tvs))
      | _, _ => None
      end
  | EListMatch scrutinee nilcase hd tl conscase =>
      match eval fuel' rho scrutinee with
      | Some (VList []) => eval fuel' rho nilcase
      | Some (VList (hv :: tvs)) => eval fuel' ((hd, hv) :: (tl, VList tvs) :: rho) conscase
      | _ => None
      end
  | ERecord k1 e1 k2 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some v1, Some v2 => Some (VRecord k1 v1 k2 v2)
      | _, _ => None
      end
  | EField name e1 =>
      match eval fuel' rho e1 with
      | Some (VRecord k1 v1 k2 v2) =>
          if String.eqb name k1 then Some v1
          else if String.eqb name k2 then Some v2
          else None
      | _ => None
      end
  | EInl e1 =>
      match eval fuel' rho e1 with
      | Some v1 => Some (VInl v1)
      | None => None
      end
  | EInr e1 =>
      match eval fuel' rho e1 with
      | Some v1 => Some (VInr v1)
      | None => None
      end
  | ECase scrutinee x1 case1 x2 case2 =>
      match eval fuel' rho scrutinee with
      | Some (VInl v1) => eval fuel' ((x1, v1) :: rho) case1
      | Some (VInr v2) => eval fuel' ((x2, v2) :: rho) case2
      | _ => None
      end
  | EStrConst s => Some (VStr s)
  | EStrConcat e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VStr s1), Some (VStr s2) => Some (VStr (s1 ++ s2))
      | _, _ => None
      end
  | EStrEq e1 e2 =>
      match eval fuel' rho e1, eval fuel' rho e2 with
      | Some (VStr s1), Some (VStr s2) => Some (VBool (String.eqb s1 s2))
      | _, _ => None
      end
  end
  end.

(** The precondition, made explicit: whenever the divisor is known
    non-zero, [EDiv]/[EMod] compute exactly [Z.div]/[Z.modulo] -- no
    hidden rounding or truncation-vs-floor surprise, matching the
    comment above. This is the Coq-side half of "extract an assumption
    into a runtime check": the *assumption* ([b <> 0]) is what this
    theorem needs to say anything at all; the *check* is [eval]'s own
    [Z.eqb b 0] test above, and (separately, assumed not proved per
    docs/duality.md) Python's own [ZeroDivisionError] on [//]/[%]. The
    hypotheses are at fuel level [fuel] (how much fuel evaluating [e1]/
    [e2] actually used) and the conclusion at [S fuel] (one more, for
    [EDiv]/[EMod]'s own step) -- matching exactly how [eval] unfolds
    once before recursing. *)
Lemma eval_div_correct :
  forall fuel rho e1 e2 a b,
    eval fuel rho e1 = Some (VZ a) -> eval fuel rho e2 = Some (VZ b) -> b <> 0 ->
    eval (S fuel) rho (EDiv e1 e2) = Some (VZ (Z.div a b)).
Proof.
  intros fuel rho e1 e2 a b He1 He2 Hb.
  simpl. rewrite He1, He2.
  apply Z.eqb_neq in Hb. rewrite Hb. reflexivity.
Qed.

Lemma eval_mod_correct :
  forall fuel rho e1 e2 a b,
    eval fuel rho e1 = Some (VZ a) -> eval fuel rho e2 = Some (VZ b) -> b <> 0 ->
    eval (S fuel) rho (EMod e1 e2) = Some (VZ (Z.modulo a b)).
Proof.
  intros fuel rho e1 e2 a b He1 He2 Hb.
  simpl. rewrite He1, He2.
  apply Z.eqb_neq in Hb. rewrite Hb. reflexivity.
Qed.

(** Identifier validity: the restricted grammar in Json.v only round-trips
    names made of ASCII letters/digits/underscore. This predicate marks
    exactly the [expr] terms whose variable names satisfy that. It is not a
    restriction on the semantics above -- [eval] is total (modulo the
    "wrong shape of value" / unbound-variable / out-of-fuel getting-stuck
    cases already described) over all [expr] values regardless of
    identifier shape. *)
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
  | ERepeat _ x body init =>
      andb (is_valid_ident x)
           (andb (expr_idents_valid is_valid_ident body) (expr_idents_valid is_valid_ident init))
  | EDiv e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EMod e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | ELam param body => andb (is_valid_ident param) (expr_idents_valid is_valid_ident body)
  | ERec f param body =>
      andb (is_valid_ident f) (andb (is_valid_ident param) (expr_idents_valid is_valid_ident body))
  | ERecMut f1 param1 body1 f2 param2 body2 =>
      andb (is_valid_ident f1)
        (andb (is_valid_ident param1)
          (andb (expr_idents_valid is_valid_ident body1)
            (andb (is_valid_ident f2)
              (andb (is_valid_ident param2) (expr_idents_valid is_valid_ident body2)))))
  | EApp func arg => andb (expr_idents_valid is_valid_ident func) (expr_idents_valid is_valid_ident arg)
  | ENil => true
  | ECons hd tl => andb (expr_idents_valid is_valid_ident hd) (expr_idents_valid is_valid_ident tl)
  | EListMatch scrutinee nilcase hd tl conscase =>
      andb (expr_idents_valid is_valid_ident scrutinee)
        (andb (expr_idents_valid is_valid_ident nilcase)
          (andb (is_valid_ident hd)
            (andb (is_valid_ident tl) (expr_idents_valid is_valid_ident conscase))))
  | ERecord k1 e1 k2 e2 =>
      andb (is_valid_ident k1)
        (andb (expr_idents_valid is_valid_ident e1)
          (andb (is_valid_ident k2) (expr_idents_valid is_valid_ident e2)))
  | EField name e1 => andb (is_valid_ident name) (expr_idents_valid is_valid_ident e1)
  | EInl e1 => expr_idents_valid is_valid_ident e1
  | EInr e1 => expr_idents_valid is_valid_ident e1
  | ECase scrutinee x1 case1 x2 case2 =>
      andb (expr_idents_valid is_valid_ident scrutinee)
        (andb (is_valid_ident x1)
          (andb (expr_idents_valid is_valid_ident case1)
            (andb (is_valid_ident x2) (expr_idents_valid is_valid_ident case2))))
  | EStrConst s => is_valid_ident s
  | EStrConcat e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  | EStrEq e1 e2 => andb (expr_idents_valid is_valid_ident e1) (expr_idents_valid is_valid_ident e2)
  end.
