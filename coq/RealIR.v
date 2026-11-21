(** RealIR.v

    A first step toward GOAL.md's still-open "reconciling Json.v's
    grammar against Coq's actual [Extraction Language JSON] output"
    question: a formal model of a *recognized fragment* of that real
    IR, together with a proof that translating it into our existing
    [expr] subset (Lang.v) preserves meaning -- anchored not against a
    reimplementation of Coq's arithmetic, but against Coq's own [Z]/
    [bool] operations directly, the same trust level as the kernel
    itself.

    [Extraction Language JSON] (Coq's own, stock, already-shipped
    extraction backend) really does exist in this project's Coq
    8.18.0 -- confirmed by direct experiment, not assumed: running
    [coqc] on a file with [Require Extraction. Extraction Language
    JSON.] and a genuine, human-written

      Definition clamp_nonneg (a b : Z) : Z := if Z.ltb a 0 then b else a.

    emits a generic MiniML-shaped JSON tree ([decl:term]/[expr:lambda]/
    [expr:case]/[expr:apply]/[expr:global]/[expr:rel]/[expr:constructor]
    nodes), *not* anything resembling [Json.v]'s bespoke
    [{"tag":...}] grammar. Two complications this file's design works
    around, both found by direct experiment:

    - With this project's own OCaml-native-int/float realizers
      ([ExtrOcamlZInt] etc, needed so [Z]/[float] extract to OCaml's
      native types rather than Peano-style unary/binary trees) loaded,
      the JSON output leaks raw OCaml source snippets as constructor
      names (a constructor literally named ["(fun p->1+2*p)"]) and
      pulls in unrelated transitive standard-library declarations.
      [real_expr] below is designed against the *realizer-free*
      extraction output instead, which is clean MiniML (if verbose:
      every [Z]/[positive] operation extracts its own full recursive
      definition over Coq's binary encoding, which this file's
      translation deliberately ignores in favor of recognizing
      well-known *names* -- ["add"]/["ltb"]/["andb"]/etc, exactly as
      they appear unqualified in the real JSON -- as intrinsics, the
      same way a real compiler treats built-ins rather than
      interpreting their extracted bodies).
    - A numeral literal extracts as nested [Z0]/[Zpos]/[Zneg]/
      [positive] constructor applications, not a flat JSON number --
      but since [real_expr]'s own literal case, [RZLit], stores a
      genuine Coq [Z] (the same type [EConst] already carries),
      *reconstructing* that [Z] from the nested constructors is
      squarely a job for the future JSON-text parser (not yet written
      -- see docs/roadmap.md), not for this file, which works at the
      Gallina level: it takes [real_expr] terms as already-built
      values, the same way examples/Kinematics.v already builds [expr]
      terms directly without first round-tripping them through
      [Json.v]'s parser.

    [real_expr] is deliberately a tiny, *recognized* fragment --
    variables, integer/boolean literals, unary/binary calls to a
    fixed, named set of intrinsics, and a 2-case boolean [if] -- not a
    general MiniML interpreter for arbitrary extracted Coq. Anything
    outside it is simply not representable here, the same honest way
    partiality already works throughout this project:
    [real_to_expr] returns [None] rather than guessing. *)

(** [RPair]/[RProj1]/[RProj2] cover both tuples *and* 2-field
    [Record]s, confirmed directly: a real two-field [Record point :=
    mkpoint { px : Z; py : Z }.] extracts its constructor exactly like
    [pair] (an [expr:constructor] with 2 args -- [RPair] already
    recognizes any 2-arg constructor, whatever it's named), but field
    *access* ([py p]) does not extract as a named function call the
    way [fst]/[snd] do -- it extracts as a 1-case [expr:case] match on
    that same constructor, binding one field to a real name and the
    other to ["_"], returning the named one bare. Since a Coq [Record]
    is genuinely just sugar for a single-constructor inductive --
    isomorphic to a plain product at the value level, with the field
    *names* living only in the generated projection functions, not in
    the runtime representation -- [RProj1]/[RProj2] model exactly that
    1-case match shape and translate into the same [EFst]/[ESnd]
    tuples already use, rather than inventing a separate representation
    keyed by field name for what is, underneath, the same value shape
    [RPair] already covers. *)

(** [RCase scrutinee x1 case1 x2 case2]: a real, human-written 2-case
    sum ([Datatypes.sum], Coq's own [inl]/[inr], not [option] -- see
    below). Confirmed directly against a real extracted [Definition
    classify (s : Z + Z) : Z := match s with inl a => a | inr b => 0 -
    b end.]: a 2-case [expr:case] on the scrutinee, each
    [pat:constructor] ([Inl]/[Inr]) carrying exactly one payload
    argument -- the *same* shape [RListMatch]'s own [Nil]/[Cons]
    match already has, and lines up exactly with [Lang.v]'s own
    [EInl]/[EInr]/[ECase] (both payload-carrying), needing no encoding
    trick the way [RProj1]/[RProj2] needed one for [Record] field
    access. [option]'s [None]/[Some] is *not* covered the same way:
    [None] carries *no* payload, so it doesn't fit [EInl]/[EInr]'s
    both-sides-have-a-payload shape without a second, separate
    encoding -- [RNone]/[RSome]/[ROptionMatch] below are that second
    encoding. *)

(** [RNone]/[RSome e]/[ROptionMatch scrutinee nonecase x somecase]:
    Coq's own [option], confirmed directly against a real extracted
    [Definition default_zero (x : option Z) : Z := match x with None
    => 0 | Some v => v end.] and [Definition wrap_positive (x : Z) :
    option Z := if Z.ltb x 0 then None else Some x.]: [None]/[Some v]
    extract as 0-/1-argument [expr:constructor]s, the same shape
    [True]/[False] or [Nil]/[Cons] already have, and a match on them is
    a 2-case [expr:case] -- confirmed to appear in *either* order
    ([Some] first in one probe, matching [option]'s own declaration
    order in Coq's stdlib, [Some] before [None] -- not the order the
    source [match] was even written in), so [real_case_of_json]'s own
    dispatch below checks both. Lines up with [Lang.v]'s own
    [ENone]/[ESome]/[EOptionMatch] (a dedicated pair of constructors,
    not [EInl]/[EInr] with a dummy payload for [None] -- see [Lang.v]'s
    header for why). *)
(** [RSelf arg]: a self-recursive call, inside the body of a real,
    human-written [Fixpoint]. Confirmed directly against a real
    extracted [Fixpoint any_true (l : list bool) : bool := match l
    with nil => false | b :: rest => orb b (any_true rest) end.]: the
    whole declaration is one [decl:fixgroup] wrapping a single
    [fixgroup:item] (the group has exactly one member here -- general
    *mutually*-recursive fixgroups are not yet modeled), whose own
    [value] is the familiar [expr:lambda]/[argnames] wrapper. Two
    things line up with already-documented findings, not new
    surprises: [orb]'s own definition inlines on the spot exactly the
    way [andb]'s already does (this file's header), so the [Cons] case
    is a 2-case [expr:case] on [b], not a named [orb] call; and the
    recursive call in its [False] branch is an ordinary [expr:apply]
    of [expr:global "any_true"] -- the function's *own* declared name,
    exactly the same JSON shape an unrelated intrinsic call would
    have, distinguishable only by knowing which name the enclosing
    fixgroup itself declared (a genuine new finding, specific to
    [RSelf]).
    [RSelf] is therefore deliberately *not* interpreted by [real_eval]
    or [real_to_expr] (both give it [None], the same honest partiality
    every other unrecognized shape already gets) -- translating it
    needs to know the enclosing function's own name, which only
    [real_to_expr_ctx]/[real_fix_decl] below (not a bare [real_expr])
    carry. Checking the translated [ERec] against the real Gallina
    [Fixpoint] then follows the same concrete-instance style already
    established for *any* [ERec]-based recursion in this project
    (Kinematics.v's [fall_until_landed_expr], Example 7): a genuinely
    recursive [expr]'s step count depends on its argument, not on
    [rfd_body]'s static size, so there is no fixed fuel bound to quote
    in a universally-quantified theorem the way the non-recursive
    fragment's [real_to_expr_preserves_semantics] has one -- "enough
    fuel for this particular run" is the right (and already-precedented)
    standard, not a gap specific to [RSelf]. See examples/NaturalCoq.v's
    [any_true_expr_matches_real_definition]. *)

(** [RCall fname arg]: [RSelf]'s generalization to *general*
    mutually-recursive fixgroups ([Fixpoint ... with ...], more than
    one member) -- confirmed directly against a real extracted
    [Fixpoint is_even (n : nat) : bool := match n with O => true | S
    n' => is_odd n' end with is_odd (n : nat) : bool := match n with O
    => false | S n' => is_even n' end.]: the whole declaration is one
    [decl:fixgroup] whose [fixlist] now has *two* [fixgroup:item]s, and
    a call to *either* member -- [is_even]'s own call to [is_odd], or
    [is_odd]'s call back to [is_even] -- is an ordinary [expr:apply] of
    [expr:global <name>], the exact same shape a self-call or an
    unrelated intrinsic call would have, distinguishable only by
    knowing the *whole group's* declared names, not just one. [RSelf]
    itself is deliberately left untouched (still exactly the
    single-function, one-name case it always was, so every existing
    proof about it keeps working unchanged) -- [RCall] is a new,
    additive sibling for when the enclosing group has more than one
    name to check against, recording *which* member was called since,
    unlike [RSelf], it is no longer always "this same function". Like
    [RSelf], deliberately not interpreted by [real_eval]/[real_to_expr]
    (both [None] unconditionally): resolving it needs the enclosing
    group's full member list, which only [real_to_expr_ctx]/
    [real_fix_group_decl] below carry. *)

(** [RSelfN]/[RCallN]: [RSelf]/[RCall]'s generalization to a
    recursive function of *more than one* argument -- confirmed
    directly against a real extracted [Fixpoint sum_upto (acc n : Z)
    (fuel : nat) : Z := match fuel with O => acc | S fuel' => sum_upto
    (acc + n) (n - 1) fuel' end.]: the recursive call [sum_upto (acc +
    n) (n - 1) fuel'] is *one* [expr:apply] node with a flat, 3-element
    [args] list, not curried -- the same "direct list, not curried"
    shape this file's own header already confirmed for an ordinary
    [expr:lambda]'s [argnames], now confirmed for the *call* side of a
    recursive one too. [RSelf]/[RCall] are deliberately left untouched
    (still exactly the one-argument case they always were) --
    [RSelfN]/[RCallN] are new, additive siblings carrying the whole
    argument list, for when a self/sibling call has more than one.
    Translating these needs no new [Lang.v]/[PyLang.v]/[Translate.v]/
    [Json.v]/[PyPrint.v]/[PyRename.v] constructor at all: a recursive
    call with [n] arguments curries into [n] nested, already-proven
    [EApp]s (the same way a multi-argument *non-recursive* call could
    always be curried, just never needed to be, since [real_decl]'s
    direct [argnames] handles that case without currying) -- see
    [real_to_expr_ctx]'s own cases below. Like [RSelf]/[RCall],
    deliberately not interpreted by [real_eval]/[real_to_expr] (both
    [None] unconditionally). *)

(** [RRecord3]/[RProj3_1]/[RProj3_2]/[RProj3_3]: a real, human-written
    *3*-field [Record] -- confirmed directly against a real extracted
    [Record point3 := mkpoint3 { px : Z; py : Z; pz : Z }.]: just like
    the 2-field case, construction is a single [expr:constructor] (now
    with 3 args instead of 2), and each field *access* is a 1-case
    [expr:case] match on that constructor with [argnames] binding
    exactly the accessed field to a real name and the other two to
    ["_"] -- e.g. [["_"; "py"; "_"]] for [py]. [Lang.v]'s own
    [expr]/[value] have no 3-ary product, so -- the same way the
    2-field case already models a [Record] as the plain-pair shape
    [RPair]/[VPair] already has, not a new keyed representation --
    these model a 3-field [Record] as the *nested* pair
    [EPair e1 (EPair e2 e3)] a human would write by hand to work
    around [ERecord]'s own 2-field cap (`docs/roadmap.md`), rather
    than reaching for the genuinely-N-ary [ERecordN]: field *names*
    live only in the extracted projection functions (confirmed by the
    2-field case already), never in the runtime representation, so
    there is no name to recover and key an [ERecordN] by here either.
    This is also the first case in this file whose translation nests
    two levels deep (`EFst (ESnd _)`/`ESnd (ESnd _)` for the 2nd/3rd
    field), so unlike every single-level case above, [real_expr_depth]
    needs an extra `S` for those two, and the proof needs a second
    [destruct fuel] step to match. *)

(** [RRecordN]/[RProjN]: [RRecord3]/[RProj3_1]/[RProj3_2]/[RProj3_3]
    generalized to genuinely *any* field count, not one more hardcoded
    arity at a time (`docs/roadmap.md`'s own "liftable" item on this).
    Confirmed directly that the nested-pair encoding keeps working
    unchanged at 5 fields: a real [Record point5 := mkpoint5 { rx rz
    ry rw rv : Z }.] extracts its constructor as a plain 5-arg
    [expr:constructor] (same shape as 2/3 fields, just more args), and
    a field access ([rz p], the 3rd of 5) extracts as a 1-case
    [expr:case] with a 5-name [argnames] list, four of them ["_"] and
    one real name at the accessed position -- the exact same shape
    [RProj3_2]'s own 3-name case already has, just longer.

    [RRecordN es] represents the field list [es], meant to always
    hold at least 2 fields -- there is no 0- or 1-field case to
    represent here: those already go through [RNone]/[RSome] or the
    0-arg constructors, and a would-be 1-field "record" is
    indistinguishable from a 1-arg [Some] at this shape-matching layer
    with no further type information to break the tie, the same
    inherent ambiguity a literally-named user constructor could always
    cause -- see [RealJson.v]'s own comment on this where the
    recognizer is wired in. [real_eval]/[real_to_expr]/
    [real_to_expr_ctx]/[real_expr_depth] each walk [es] via an
    anonymous nested [fix] taking [es] itself as its *one* parameter
    and pattern-matching it directly to peel off a head -- the exact
    style [RSelfN]/[RCallN]'s own [real_expr_depth] case already uses
    for its [list_max_depth] -- rather than a [fix] taking a separate
    "already-peeled head" parameter alongside the remaining tail: that
    shape is rejected by the guard checker (confirmed directly --
    "Recursive call to real_eval has principal argument equal to ...
    instead of ..."), since a plain parameter isn't itself one of the
    *pattern-matched* subterms the checker tracks as guarded, only
    something obtained by *matching* the fix's own argument is --
    [e]/[rest] bound by [match xs with | e :: rest => ...] inside the
    SAME fix body qualifies, a separately-threaded [e] parameter
    doesn't, even though both ultimately hold the same values. The
    same reasoning is why [RRecordN] carries one plain [list real_expr]
    field instead of [(e1 e2 : real_expr) (erest : list real_expr)] (a
    static at-least-2 guarantee that seemed cleaner at first): the
    dispatch would then have to *reconstruct* [e1 :: e2 :: erest] to
    hand to a list-walking helper, and a freshly reconstructed list is
    just as unguarded as a bare extra parameter is, for the same
    reason -- built from subterms, but not itself one. Translates to
    the same *right-nested* [EPair e1 (EPair e2 (... (EPair e_{n-1}
    e_n) ...))] chain [RRecord3] already builds for 3, generalized
    over the list. [real_expr_depth]'s own list-walking [fix] adds one
    [S] per field *including* the last one (unlike [RRecord3]'s own
    hand-written formula, which doesn't need to wrap its own final
    field) -- a strict-subterm bound for every element of [es] is what
    the preservation proof below actually needs (well-founded
    induction on depth requires a *strictly* smaller measure to
    recurse with, and a last-field-gets-no-[S] formula would make a
    singleton list's own depth equal, not less, blocking exactly that
    recursion), so this is a deliberately slightly looser, not
    tightest-possible, bound -- still obviously a valid upper bound on
    [eval]'s own fuel need, just not numerically identical to what
    [RRecord3]'s 3 fixed fields produce.

    [RProjN nskip last scrutinee] extracts one field of that chain:
    [nskip] is how many [ESnd] steps reach the accessed field's own
    sub-pair (0 for the 1st field, 1 for the 2nd, ... -- i.e. one less
    than its 1-indexed position), and [last] says whether it is the
    *final* field (no further [EFst] needed -- it already sits bare
    at the end of the chain, not wrapped in one more pair) or not (one
    [EFst] after the skips). This is a faithful generalization, not a
    new idea: [RProj3_1] is [nskip := 0, last := false] (bare [EFst]),
    [RProj3_2] is [nskip := 1, last := false] ([EFst (ESnd _)]),
    [RProj3_3] is [nskip := 2, last := true] ([ESnd (ESnd _)]), and
    the 2-field [RProj1]/[RProj2] are the [n = 2] instances of the
    same two shapes -- all four already-proven cases are literally
    what [RProjN] produces for their own [nskip]/[last], confirmed by
    recomputing each by hand before trusting the general formula.
    [real_expr_depth]'s own count of [EFst]/[ESnd] *operations* --
    [nskip] plus one more if [last] is false -- making the general
    formula pure addition (`nskip + (if last then 0 else 1) +
    real_expr_depth scrutinee`) rather than a recursive wrap, is the
    same arithmetic fact that lets [RProj3_2]'s/[RProj3_3]'s existing
    [S (S _)] stand in that form already: [Nat.iter] applied [k] times
    is exactly [k + _], so there was never a need for the recursive
    shape in the first place, just never written that way until now.
    `examples/NaturalCoq.v`'s [point5]/[getz5] (an extracted,
    hand-encoded, *and* real-JSON-parsed instance, the 3rd-of-5 field)
    is the worked instance. *)

(** [RFLit]/[RApp2]'s new ["rplus"]/["rmult"]/["rminus"]/["rdiv"]
    cases: a first, narrow step into Coquelicot-adjacent code
    (`docs/roadmap.md`'s own section on this, and
    `coq/RealBridge.v`'s header), confirmed directly against a real
    extracted Coquelicot-proven function:

      Definition quad (x : R) : R := x * x + 1.
      Lemma quad_is_derive : forall x, is_derive quad x (2 * x).
      Proof. intro x. unfold quad. auto_derive; auto. ring. Qed.

    extracts [quad]'s own body as [rplus (rmult x x) (iZR (Zpos XH))]
    -- a plain named-global-call shape, exactly like [Z.add]/[Z.ltb]
    already are, confirmed by actually installing [coq-coquelicot]
    (via the [coq-released] opam repo) and running [coqc] on it, not
    assumed. [quad_is_derive] itself never appears in the extracted
    JSON at all -- Coquelicot's calculus lemmas are [Prop]-sorted and
    erase to nothing, exactly as `docs/duality.md`'s model predicts.

    The trust boundary here is deliberately *not* the same one [RZLit]
    draws for [Z]: Coq's own [Rplus]/[Rmult] have no computational
    content at all (`coq/RealBridge.v`'s header spells out why --
    extracting them pulls in [ClassicalDedekindReals]'s internal cut
    representation, not runnable code), so there is no "Coq's own
    stdlib function, called directly" move available for ["rplus"]/
    ["rmult"] the way there is for ["add"]/["ltb"]. Instead, this
    fragment's [real_eval] models them *directly* as [PrimFloat]
    arithmetic ([VFloat]'s own [PrimFloat.add]/[PrimFloat.mul]) -- the
    same trust category as every other [PrimFloat]-backed operation
    already in this project (`docs/roadmap.md`'s own ["PrimFloat.float
    is wired in"] section), not a new kind of assumption. What this
    does *not* claim: that this matches the *original*, classical-[R]
    source semantics [quad_is_derive] was stated about -- that
    correspondence (necessarily approximate, since [R] is exact and
    [PrimFloat] rounds) is tracked separately, honestly, and not yet
    proved end-to-end, by [RealBridge.v]'s [R_of_float]/
    [R_of_float_add_rounded]/[R_of_float_mul_rounded]. Composing that
    bridge with this file's own [real_to_expr_preserves_semantics] --
    i.e. a genuine "translating a Coquelicot-authored [R]-valued
    function preserves its *mathematical* meaning up to a stated,
    bounded rounding error" theorem -- is deliberately not attempted
    here: doing it *compositionally*, for arbitrarily nested
    arithmetic, needs real error-propagation tracking (how do two
    already-approximate sub-results' errors combine under a further
    [+]/[*]?) -- exactly the Flocq-scale numerical-analysis work this
    project's dependency policy avoids re-deriving, the same boundary
    [RealBridge.v]'s own header already draws, not a new one. A
    concrete-instance correspondence (checked for one specific input,
    where the arithmetic involved happens to be exact, no rounding
    error to propagate) is still honestly within reach, and is exactly
    what the worked example below does.

    ["rminus"]/["rdiv"] round out the four basic operations the same
    way, translating into [EFSub]/[EFDiv] (already in [Lang.v]) --
    deliberately *not* ["ropp"] (unary negation) alongside them:
    translating it as [EFSub (EFConst 0) e] would compute
    [PrimFloat.sub 0 f] where [real_eval]'s own reference computes
    [PrimFloat.opp f] directly, and those two differ for [f = 0] under
    IEEE-754's signed zero ([0.0 - 0.0 = +0.0], but [-0.0] is a
    distinct value from [opp 0.0]) -- a genuine edge case, not
    excluded here by fiat.

    ["rabs"] (Coquelicot's [Rabs]) has the same signed-zero problem,
    confirmed directly by extracting a real [Rabs] use ([Rabs (x -
    y)]) and finding it comes out as a plain unary global call
    ["rabs"], despite [Rabs]'s own Gallina definition being a
    decidability case split ([Rcase_abs]/[total_order_T]). An
    [EIf]-based workaround ([EIf (EFLt e (EFConst 0)) (EFOpp e) e])
    is wrong at [e = -0.0]: [-0.0 < 0.0] is [false] under IEEE-754,
    so the [else] branch returns [-0.0] unchanged, while
    [PrimFloat.abs (-0.0) = 0.0]. So ["rabs"] translates to a real,
    dedicated [EFAbs] (added to [Lang.v] alongside [EFOpp]), calling
    [PrimFloat.abs] directly -- the same move as ["ropp"]/[EFOpp].

    ["sqrt"] (Coq's own [Reals.R_sqrt.sqrt], the function Coquelicot's
    own calculus lemmas about square roots are stated over) is the
    simplest case of all three float unary ops here: there isn't even
    an *almost*-right workaround to reject, since nothing already in
    this fragment ([+]/[-]/[*]/[/]) can compute a square root at all --
    a dedicated primitive is not an exactness refinement the way
    [EFOpp]/[EFAbs] are, it is the only way to support this operation.
    Confirmed directly against a real probe ([sqrt (x * x + y * y)]):
    [sqrt] extracts as a plain unary global call, the same shape
    ["ropp"]/["rabs"] already have, even though its own Gallina
    definition goes through [Rsqrt_exists] and a classical
    completeness argument. Translates to a real, dedicated [EFSqrt]
    (added to [Lang.v] alongside [EFOpp]/[EFAbs]), calling
    [PrimFloat.sqrt] directly.

    ["rinv"] (reciprocal, Coquelicot's unary [/]) is the one addition
    here needing *no* new [Lang.v] constructor at all: [PrimFloat]'s
    own division is already a correctly-rounded operation, so
    [1.0 / x] computes the correctly-rounded reciprocal of [x] exactly
    -- confirmed directly (including the signed-zero/infinity cases:
    [1.0 / (-0.0) = -Infinity], matching IEEE-754, the same way
    [PrimFloat.div] itself already would). Translates to the already-
    proven [EFDiv (EFConst 1) e], no new primitive, no new proof
    obligation beyond this file's own.

    ["rmax"]/["rmin"] are a third kind of addition: [PrimFloat] has
    *no* native max/min primitive at all (unlike [sqrt]/[abs]/[opp]),
    so [EFMax]/[EFMin] (added to [Lang.v]) are defined directly in
    Gallina via [PrimFloat.ltb] (already trusted), not by calling out
    to one more primitive. Which operand a tie (signed zero) returns
    is a genuine, explicit choice this project makes here -- classical
    [R] has no signed zero at all, so there is no "faithful to
    Coquelicot" answer to match in the first place (the same kind of
    boundary [RealBridge.v]'s own rounding axioms already draw) --
    confirmed directly to match real Python's own [max]/[min] builtins'
    tie-breaking exactly, so [PyPrint.v] can render them as plain
    [max(...)]/[min(...)] calls. *)

From Coq Require Import ZArith String List Bool Lia.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Require Import Lang.
Open Scope Z_scope.
Open Scope string_scope.

Inductive real_expr : Type :=
  | RRel (name : var)
  | RZLit (z : Z)
  | RBoolLit (b : bool)
  | RApp1 (fn : var) (arg : real_expr)
  | RApp2 (fn : var) (arg1 arg2 : real_expr)
  | RIfBool (scrutinee then_ else_ : real_expr)
  | RNil
  | RCons (hd tl : real_expr)
  | RListMatch (scrutinee nilcase : real_expr) (hd tl : var) (conscase : real_expr)
  | RPair (e1 e2 : real_expr)
  | RProj1 (scrutinee : real_expr)
  | RProj2 (scrutinee : real_expr)
  | RCase (scrutinee : real_expr) (x1 : var) (case1 : real_expr) (x2 : var) (case2 : real_expr)
  | RSelf (arg : real_expr)
  | RCall (fname : var) (arg : real_expr)
  | RSelfN (args : list real_expr)
  | RCallN (fname : var) (args : list real_expr)
  | RRecord3 (e1 e2 e3 : real_expr)
  | RProj3_1 (scrutinee : real_expr)
  | RProj3_2 (scrutinee : real_expr)
  | RProj3_3 (scrutinee : real_expr)
  | RFLit (f : PrimFloat.float)
  | RNone
  | RSome (e : real_expr)
  | ROptionMatch (scrutinee nonecase : real_expr) (x : var) (somecase : real_expr)
  | RRecordN (es : list real_expr)
  | RProjN (nskip : nat) (last : bool) (scrutinee : real_expr).

(** [value_skip_snd n v]: peel [n] [VPair]/[ESnd]-style layers off a
    right-nested pair value, used by [RProjN]'s [real_eval] case below
    to reach the sub-pair an accessed field sits in before (depending
    on [last]) taking its own left component. [None] if [v] runs out
    of [VPair] layers before [n] does -- the same "stuck, not guessed"
    partiality every other shape mismatch in this file already gets. *)
Fixpoint value_skip_snd (n : nat) (v : value) : option value :=
  match n with
  | O => Some v
  | S n' => match v with
            | VPair _ v2 => value_skip_snd n' v2
            | _ => None
            end
  end.

(** [expr_skip_snd n e]: the [expr]-level mirror of [value_skip_snd],
    wrapping [e] in [n] nested [ESnd]s -- total, not partial, since
    this only builds a syntax tree, it does not evaluate anything. *)
Fixpoint expr_skip_snd (n : nat) (e : expr) : expr :=
  match n with
  | O => e
  | S n' => expr_skip_snd n' (ESnd e)
  end.

(** Ties [expr_skip_snd]'s syntax to [value_skip_snd]'s semantics:
    evaluating [n] nested [ESnd]s around [e] with fuel [fuel] is the
    same as evaluating [e] alone with [fuel - n] (exactly how much
    fuel [n] [ESnd] dispatches consume, one apiece, per [eval]'s own
    [ESnd] case in `Lang.v`) and then peeling [n] [VPair] layers off
    whatever value comes back. Proved by induction on [n] -- not on
    [e] or [fuel] -- since [expr_skip_snd]/[value_skip_snd] both
    recurse on their own [n] argument. *)
Lemma eval_expr_skip_snd :
  forall n fuel rho e,
    (n < fuel)%nat ->
    eval fuel rho (expr_skip_snd n e) =
      match eval (fuel - n) rho e with
      | Some v => value_skip_snd n v
      | None => None
      end.
Proof.
  induction n as [| n' IH]; intros fuel rho e Hn.
  - simpl. replace (fuel - 0)%nat with fuel by lia.
    destruct (eval fuel rho e); reflexivity.
  - simpl expr_skip_snd.
    rewrite (IH fuel rho (ESnd e)) by lia.
    destruct (fuel - n')%nat as [| k] eqn:Hk; [lia|].
    replace k with (fuel - S n')%nat by lia.
    simpl.
    destruct (eval (fuel - S n') rho e) as [v|]; [| reflexivity].
    destruct v; reflexivity.
Qed.

(** The reference semantics: not a reimplementation of [Z.add]/
    [Z.ltb]/etc, but a direct call to Coq's own, so this file's trust
    boundary is exactly "Coq's standard library means what it says it
    means" -- the same category of trust as the kernel itself, not a
    new assumption this file introduces. *)
Fixpoint real_eval (rho : env) (re : real_expr) {struct re} : option value :=
  match re with
  | RRel name => lookup rho name
  | RZLit z => Some (VZ z)
  | RBoolLit b => Some (VBool b)
  | RApp1 fn arg =>
      match real_eval rho arg with
      | Some (VBool b) =>
          if string_dec fn "negb" then Some (VBool (negb b)) else None
      | Some (VPair v1 v2) =>
          if string_dec fn "fst" then Some v1
          else if string_dec fn "snd" then Some v2
          else None
      | Some (VFloat f) =>
          if string_dec fn "ropp" then Some (VFloat (PrimFloat.opp f))
          else if string_dec fn "rabs" then Some (VFloat (PrimFloat.abs f))
          else if string_dec fn "sqrt" then Some (VFloat (PrimFloat.sqrt f))
          else if string_dec fn "rinv" then Some (VFloat (PrimFloat.div 1%float f))
          else None
      | _ => None
      end
  | RApp2 fn a1 a2 =>
      match real_eval rho a1, real_eval rho a2 with
      | Some (VZ z1), Some (VZ z2) =>
          if string_dec fn "add" then Some (VZ (Z.add z1 z2))
          else if string_dec fn "sub" then Some (VZ (Z.sub z1 z2))
          else if string_dec fn "mul" then Some (VZ (Z.mul z1 z2))
          else if string_dec fn "eqb" then Some (VBool (Z.eqb z1 z2))
          else if string_dec fn "ltb" then Some (VBool (Z.ltb z1 z2))
          else if string_dec fn "leb" then Some (VBool (Z.leb z1 z2))
          else None
      | Some (VBool b1), Some (VBool b2) =>
          if string_dec fn "andb" then Some (VBool (andb b1 b2))
          else if string_dec fn "orb" then Some (VBool (orb b1 b2))
          else None
      | Some (VFloat f1), Some (VFloat f2) =>
          if string_dec fn "rplus" then Some (VFloat (PrimFloat.add f1 f2))
          else if string_dec fn "rmult" then Some (VFloat (PrimFloat.mul f1 f2))
          else if string_dec fn "rminus" then Some (VFloat (PrimFloat.sub f1 f2))
          else if string_dec fn "rdiv" then Some (VFloat (PrimFloat.div f1 f2))
          else if string_dec fn "rmax" then
            Some (VFloat (if PrimFloat.ltb f1 f2 then f2 else f1))
          else if string_dec fn "rmin" then
            Some (VFloat (if PrimFloat.ltb f2 f1 then f2 else f1))
          else None
      | _, _ => None
      end
  | RIfBool c t e =>
      match real_eval rho c with
      | Some (VBool true) => real_eval rho t
      | Some (VBool false) => real_eval rho e
      | _ => None
      end
  | RNil => Some (VList [])
  | RCons hd tl =>
      match real_eval rho hd, real_eval rho tl with
      | Some hv, Some (VList tvs) => Some (VList (hv :: tvs))
      | _, _ => None
      end
  | RListMatch scrutinee nilcase hd tl conscase =>
      match real_eval rho scrutinee with
      | Some (VList []) => real_eval rho nilcase
      | Some (VList (hv :: tvs)) => real_eval ((hd, hv) :: (tl, VList tvs) :: rho) conscase
      | _ => None
      end
  | RPair e1 e2 =>
      match real_eval rho e1, real_eval rho e2 with
      | Some v1, Some v2 => Some (VPair v1 v2)
      | _, _ => None
      end
  | RProj1 scrutinee =>
      match real_eval rho scrutinee with
      | Some (VPair v1 _) => Some v1
      | _ => None
      end
  | RProj2 scrutinee =>
      match real_eval rho scrutinee with
      | Some (VPair _ v2) => Some v2
      | _ => None
      end
  | RCase scrutinee x1 case1 x2 case2 =>
      match real_eval rho scrutinee with
      | Some (VInl v) => real_eval ((x1, v) :: rho) case1
      | Some (VInr v) => real_eval ((x2, v) :: rho) case2
      | _ => None
      end
  | RSelf _ => None
  | RCall _ _ => None
  | RSelfN _ => None
  | RCallN _ _ => None
  | RRecord3 e1 e2 e3 =>
      match real_eval rho e1, real_eval rho e2, real_eval rho e3 with
      | Some v1, Some v2, Some v3 => Some (VPair v1 (VPair v2 v3))
      | _, _, _ => None
      end
  | RProj3_1 scrutinee =>
      match real_eval rho scrutinee with
      | Some (VPair v1 _) => Some v1
      | _ => None
      end
  | RProj3_2 scrutinee =>
      match real_eval rho scrutinee with
      | Some (VPair _ (VPair v2 _)) => Some v2
      | _ => None
      end
  | RProj3_3 scrutinee =>
      match real_eval rho scrutinee with
      | Some (VPair _ (VPair _ v3)) => Some v3
      | _ => None
      end
  | RFLit f => Some (VFloat f)
  | RNone => Some VNone
  | RSome e1 =>
      match real_eval rho e1 with
      | Some v1 => Some (VSome v1)
      | None => None
      end
  | ROptionMatch scrutinee nonecase x somecase =>
      match real_eval rho scrutinee with
      | Some VNone => real_eval rho nonecase
      | Some (VSome v) => real_eval ((x, v) :: rho) somecase
      | _ => None
      end
  | RRecordN es =>
      (fix go (xs : list real_expr) : option value :=
         match xs with
         | [] => None
         | [e] => real_eval rho e
         | e :: rest =>
             match real_eval rho e, go rest with
             | Some v, Some vrest => Some (VPair v vrest)
             | _, _ => None
             end
         end) es
  | RProjN nskip last scrutinee =>
      match real_eval rho scrutinee with
      | Some v =>
          match value_skip_snd nskip v with
          | Some v' =>
              if last then Some v'
              else match v' with
                   | VPair v1 _ => Some v1
                   | _ => None
                   end
          | None => None
          end
      | None => None
      end
  end.

(** The translator: recognize each intrinsic by the exact unqualified
    name Coq's own extraction emits for it, and map it onto the
    corresponding, already-proven [expr] constructor. *)
Fixpoint real_to_expr (re : real_expr) : option expr :=
  match re with
  | RRel name => Some (EVar name)
  | RZLit z => Some (EConst z)
  | RBoolLit b => Some (EBool b)
  | RApp1 fn arg =>
      match real_to_expr arg with
      | Some e1 =>
          if string_dec fn "negb" then Some (ENot e1)
          else if string_dec fn "fst" then Some (EFst e1)
          else if string_dec fn "snd" then Some (ESnd e1)
          else if string_dec fn "ropp" then Some (EFOpp e1)
          else if string_dec fn "rabs" then Some (EFAbs e1)
          else if string_dec fn "sqrt" then Some (EFSqrt e1)
          else if string_dec fn "rinv" then Some (EFDiv (EFConst 1%float) e1)
          else None
      | None => None
      end
  | RApp2 fn a1 a2 =>
      match real_to_expr a1, real_to_expr a2 with
      | Some e1, Some e2 =>
          if string_dec fn "add" then Some (EAdd e1 e2)
          else if string_dec fn "sub" then Some (ESub e1 e2)
          else if string_dec fn "mul" then Some (EMul e1 e2)
          else if string_dec fn "eqb" then Some (EEq e1 e2)
          else if string_dec fn "ltb" then Some (ELt e1 e2)
          else if string_dec fn "leb" then Some (ELe e1 e2)
          else if string_dec fn "andb" then Some (EAnd e1 e2)
          else if string_dec fn "orb" then Some (EOr e1 e2)
          else if string_dec fn "rplus" then Some (EFAdd e1 e2)
          else if string_dec fn "rmult" then Some (EFMul e1 e2)
          else if string_dec fn "rminus" then Some (EFSub e1 e2)
          else if string_dec fn "rdiv" then Some (EFDiv e1 e2)
          else if string_dec fn "rmax" then Some (EFMax e1 e2)
          else if string_dec fn "rmin" then Some (EFMin e1 e2)
          else None
      | _, _ => None
      end
  | RIfBool c t e =>
      match real_to_expr c, real_to_expr t, real_to_expr e with
      | Some ec, Some et, Some ee => Some (EIf ec et ee)
      | _, _, _ => None
      end
  | RNil => Some ENil
  | RCons hd tl =>
      match real_to_expr hd, real_to_expr tl with
      | Some eh, Some et => Some (ECons eh et)
      | _, _ => None
      end
  | RListMatch scrutinee nilcase hd tl conscase =>
      match real_to_expr scrutinee, real_to_expr nilcase, real_to_expr conscase with
      | Some es, Some en, Some ec => Some (EListMatch es en hd tl ec)
      | _, _, _ => None
      end
  | RPair e1 e2 =>
      match real_to_expr e1, real_to_expr e2 with
      | Some e1', Some e2' => Some (EPair e1' e2')
      | _, _ => None
      end
  | RProj1 scrutinee =>
      match real_to_expr scrutinee with
      | Some e => Some (EFst e)
      | None => None
      end
  | RProj2 scrutinee =>
      match real_to_expr scrutinee with
      | Some e => Some (ESnd e)
      | None => None
      end
  | RCase scrutinee x1 case1 x2 case2 =>
      match real_to_expr scrutinee, real_to_expr case1, real_to_expr case2 with
      | Some es, Some ec1, Some ec2 => Some (ECase es x1 ec1 x2 ec2)
      | _, _, _ => None
      end
  | RSelf _ => None
  | RCall _ _ => None
  | RSelfN _ => None
  | RCallN _ _ => None
  | RRecord3 e1 e2 e3 =>
      match real_to_expr e1, real_to_expr e2, real_to_expr e3 with
      | Some e1', Some e2', Some e3' => Some (EPair e1' (EPair e2' e3'))
      | _, _, _ => None
      end
  | RProj3_1 scrutinee =>
      match real_to_expr scrutinee with
      | Some e => Some (EFst e)
      | None => None
      end
  | RProj3_2 scrutinee =>
      match real_to_expr scrutinee with
      | Some e => Some (EFst (ESnd e))
      | None => None
      end
  | RProj3_3 scrutinee =>
      match real_to_expr scrutinee with
      | Some e => Some (ESnd (ESnd e))
      | None => None
      end
  | RFLit f => Some (EFConst f)
  | RNone => Some ENone
  | RSome e1 =>
      match real_to_expr e1 with
      | Some e1' => Some (ESome e1')
      | None => None
      end
  | ROptionMatch scrutinee nonecase x somecase =>
      match real_to_expr scrutinee, real_to_expr nonecase, real_to_expr somecase with
      | Some es, Some en, Some em => Some (EOptionMatch es en x em)
      | _, _, _ => None
      end
  | RRecordN es =>
      (fix go (xs : list real_expr) : option expr :=
         match xs with
         | [] => None
         | [e] => real_to_expr e
         | e :: rest =>
             match real_to_expr e, go rest with
             | Some ee, Some erest' => Some (EPair ee erest')
             | _, _ => None
             end
         end) es
  | RProjN nskip last scrutinee =>
      match real_to_expr scrutinee with
      | Some e => Some (if last then expr_skip_snd nskip e else EFst (expr_skip_snd nskip e))
      | None => None
      end
  end.

(** [real_expr] has no closures/recursion at all (that is exactly what
    makes it a "recognized fragment", not a general interpreter), so
    unlike [eval]'s own fuel, this is a plain structural depth bound:
    any [fuel] strictly greater suffices, proved by ordinary induction
    on [re], not [Translate.v]'s induction-on-fuel trick. *)
Fixpoint real_expr_depth (re : real_expr) : nat :=
  match re with
  | RRel _ | RZLit _ | RBoolLit _ => O
  | RApp1 _ arg => S (real_expr_depth arg)
  | RApp2 _ a1 a2 => S (Nat.max (real_expr_depth a1) (real_expr_depth a2))
  | RIfBool c t e =>
      S (Nat.max (real_expr_depth c) (Nat.max (real_expr_depth t) (real_expr_depth e)))
  | RNil => O
  | RCons hd tl => S (Nat.max (real_expr_depth hd) (real_expr_depth tl))
  | RListMatch scrutinee nilcase _ _ conscase =>
      S (Nat.max (real_expr_depth scrutinee) (Nat.max (real_expr_depth nilcase) (real_expr_depth conscase)))
  | RPair e1 e2 => S (Nat.max (real_expr_depth e1) (real_expr_depth e2))
  | RProj1 scrutinee => S (real_expr_depth scrutinee)
  | RProj2 scrutinee => S (real_expr_depth scrutinee)
  | RCase scrutinee _ case1 _ case2 =>
      S (Nat.max (real_expr_depth scrutinee) (Nat.max (real_expr_depth case1) (real_expr_depth case2)))
  | RSelf arg => S (real_expr_depth arg)
  | RCall _ arg => S (real_expr_depth arg)
  | RSelfN args =>
      S ((fix list_max_depth (es : list real_expr) : nat :=
            match es with
            | [] => O
            | e :: rest => Nat.max (real_expr_depth e) (list_max_depth rest)
            end) args)
  | RCallN _ args =>
      S ((fix list_max_depth (es : list real_expr) : nat :=
            match es with
            | [] => O
            | e :: rest => Nat.max (real_expr_depth e) (list_max_depth rest)
            end) args)
  | RRecord3 e1 e2 e3 =>
      (* translates to the nested [EPair e1' (EPair e2' e3')] -- [e2]/
         [e3] sit one [EPair] dispatch deeper than [e1], so they need
         one more fuel unit, not a flat 3-way max. *)
      S (Nat.max (real_expr_depth e1) (S (Nat.max (real_expr_depth e2) (real_expr_depth e3))))
  | RProj3_1 scrutinee => S (real_expr_depth scrutinee)
  | RProj3_2 scrutinee => S (S (real_expr_depth scrutinee))
  | RProj3_3 scrutinee => S (S (real_expr_depth scrutinee))
  | RFLit _ => O
  | RNone => O
  | RSome e1 => S (real_expr_depth e1)
  | ROptionMatch scrutinee nonecase _ somecase =>
      S (Nat.max (real_expr_depth scrutinee) (Nat.max (real_expr_depth nonecase) (real_expr_depth somecase)))
  | RRecordN es =>
      (fix go (xs : list real_expr) : nat :=
         match xs with
         | [] => O
         | [e] => S (real_expr_depth e)
         | e :: rest => S (Nat.max (real_expr_depth e) (go rest))
         end) es
  | RProjN nskip last scrutinee =>
      (nskip + (if last then 0 else 1)) + real_expr_depth scrutinee
  end.

(** A *named* copy of [real_expr_depth]'s own anonymous [RRecordN]
    helper -- needed so there is something to state and prove a lemma
    about by ordinary structural induction on the list (the same
    "identify an anonymous [fix] with a named, reusable version"
    technique already used elsewhere in this project, e.g.
    [PyLang.v]'s anonymous [fix]es). *)
Fixpoint real_expr_depth_list (es : list real_expr) : nat :=
  match es with
  | [] => O
  | [e] => S (real_expr_depth e)
  | e :: rest => S (Nat.max (real_expr_depth e) (real_expr_depth_list rest))
  end.

Lemma real_expr_depth_record_eq :
  forall es, real_expr_depth (RRecordN es) = real_expr_depth_list es.
Proof.
  induction es as [| e1 es' IH].
  - reflexivity.
  - destruct es' as [| e2 rest].
    + reflexivity.
    + change (real_expr_depth_list (e1 :: e2 :: rest))
        with (S (Nat.max (real_expr_depth e1) (real_expr_depth_list (e2 :: rest)))).
      rewrite <- IH. reflexivity.
Qed.

(** [fix SELF 1] opens with an *explicit* self-reference (Coq's
    tactic-mode equivalent of writing this theorem as a [Fixpoint]
    instead of proving it via [induction]), kept purely as a backup
    for [RRecordN] below -- every pre-existing bullet still uses its
    own [induction re]-supplied [IHre]/[IHre1]/[IHre2] exactly as
    before (that per-case structural IH is perfectly sufficient for
    every non-list-carrying constructor, and confirmed directly that
    [fix SELF 1] followed by a plain [induction re] doesn't disturb
    that auto-generated IH at all, so there was never a reason to
    touch those bullets). The reason [SELF] is needed at all: a first
    attempt wrapped the whole proof in an *outer* strong induction on
    [real_expr_depth re] instead (the [well_founded_induction lt_wf]
    pattern `coq/RealJson.v`'s [jvalue_parse_print_roundtrip] uses) --
    but introducing that bound *before* [induction re] made [induction
    re] revert it back into every single bullet's own [IHre], changing
    its type and breaking all ~30 of them at once (confirmed directly);
    deferring the bound's introduction to *after* [induction re]
    didn't help either, since the bound already mentions [re] in the
    still-un-introduced goal, which [induction re] generalizes over
    regardless of whether it has been [intro]'d yet. [fix SELF 1] sidesteps
    this architecture problem entirely: [induction re]'s own
    auto-generated IH for [RRecordN] is of no use here regardless
    (confirmed directly, by inspecting the open goal: no [Forall]-
    shaped hypothesis appears for a nested list field, only [es]
    itself), so [RRecordN]'s own bullet reaches for [SELF] instead, on
    each element of [es] in turn via a fresh, local induction on the
    list -- and [fix]'s own guardedness check turns out to be more
    permissive than a plain [Fixpoint]'s anonymous nested [fix]
    (confirmed directly in isolation first: the exact "element reached
    through a *separate* nested list induction" shape that blocked
    [real_eval]/[real_to_expr]/[real_expr_depth]'s own [RRecordN] cases
    above is accepted without complaint for [SELF]). *)
Theorem real_to_expr_preserves_semantics :
  forall re e, real_to_expr re = Some e ->
    forall fuel rho, (real_expr_depth re < fuel)%nat ->
      eval fuel rho e = real_eval rho re.
Proof.
  fix SELF 1.
  induction re; intros e Htrans fuel rho Hfuel; simpl in Htrans.
  - (* RRel *) inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|]. reflexivity.
  - (* RZLit *) inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|]. reflexivity.
  - (* RBoolLit *) inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|]. reflexivity.
  - (* RApp1 *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1 : (real_expr_depth re < fuel')%nat) by lia.
    pose proof (IHre e1 eq_refl fuel' rho Hd1) as IH1.
    destruct (string_dec fn "negb") as [Heq|Hne1];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|];
       reflexivity|].
    destruct (string_dec fn "fst") as [Heq|Hne2];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|];
       reflexivity|].
    destruct (string_dec fn "snd") as [Heq|Hne3];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|];
       reflexivity|].
    destruct (string_dec fn "ropp") as [Heq|Hne4];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|];
       reflexivity|].
    destruct (string_dec fn "rabs") as [Heq|Hne5];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|];
       reflexivity|].
    destruct (string_dec fn "sqrt") as [Heq|Hne6];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|];
       reflexivity|].
    destruct (string_dec fn "rinv") as [Heq|Hne7];
      [inversion Htrans; subst;
       assert (Hconst1 : eval fuel' rho (EFConst 1%float) = Some (VFloat 1%float))
         by (destruct fuel' as [|fuel'']; [lia|]; reflexivity);
       simpl; rewrite Hconst1, IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|];
       reflexivity|].
    discriminate.
  - (* RApp2 *)
    destruct (real_to_expr re1) as [e1|] eqn:Hre1; [|destruct (real_to_expr re2); discriminate].
    destruct (real_to_expr re2) as [e2|] eqn:Hre2; [|discriminate].
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1' : (real_expr_depth re1 < fuel')%nat) by lia.
    assert (Hd2' : (real_expr_depth re2 < fuel')%nat) by lia.
    pose proof (IHre1 e1 eq_refl fuel' rho Hd1') as IH1.
    pose proof (IHre2 e2 eq_refl fuel' rho Hd2') as IH2.
    destruct (string_dec fn "add") as [Heq|Hne1];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "sub") as [Heq|Hne2];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "mul") as [Heq|Hne3];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "eqb") as [Heq|Hne4];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "ltb") as [Heq|Hne5];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "leb") as [Heq|Hne6];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "andb") as [Heq|Hne7];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "orb") as [Heq|Hne8];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "rplus") as [Heq|Hne9];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "rmult") as [Heq|Hne10];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "rminus") as [Heq|Hne11];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "rdiv") as [Heq|Hne12];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "rmax") as [Heq|Hne13];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    destruct (string_dec fn "rmin") as [Heq|Hne14];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1|cg1a cg1b cg1c| |sov1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2|cg2a cg2b cg2c| |sov2]|];
       reflexivity|].
    discriminate.
  - (* RIfBool *)
    destruct (real_to_expr re1) as [ec|] eqn:Hrec; [|discriminate].
    destruct (real_to_expr re2) as [et|] eqn:Hret; [|discriminate].
    destruct (real_to_expr re3) as [ee|] eqn:Hree; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hdc' : (real_expr_depth re1 < fuel')%nat) by lia.
    assert (Hdt' : (real_expr_depth re2 < fuel')%nat) by lia.
    assert (Hde' : (real_expr_depth re3 < fuel')%nat) by lia.
    simpl.
    rewrite (IHre1 ec eq_refl fuel' rho Hdc').
    destruct (real_eval rho re1) as [[zc|bc|p1 p2|fc|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|]; try reflexivity.
    destruct bc.
    + apply (IHre2 et eq_refl fuel' rho Hdt').
    + apply (IHre3 ee eq_refl fuel' rho Hde').
  - (* RNil *) inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|]. reflexivity.
  - (* RCons *)
    destruct (real_to_expr re1) as [eh|] eqn:Hreh; [|discriminate].
    destruct (real_to_expr re2) as [et|] eqn:Hret; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hdh' : (real_expr_depth re1 < fuel')%nat) by lia.
    assert (Hdt' : (real_expr_depth re2 < fuel')%nat) by lia.
    simpl.
    rewrite (IHre1 eh eq_refl fuel' rho Hdh'), (IHre2 et eq_refl fuel' rho Hdt').
    destruct (real_eval rho re1) as [[zh|bh|p1h p2h|fh|sh prh bdh ceh|vsh|rk1h rv1h rk2h rv2h|cf1h cp1h cb1h cf2h cp2h cb2h cceh cwh|iv1h|iv2h|isvh|fnvh|cgha cghb cghc| |sovh]|];
      destruct (real_eval rho re2) as [[zt|bt|p1t p2t|ft|st prt bdt cet|vst|rk1t rv1t rk2t rv2t|cf1t cp1t cb1t cf2t cp2t cb2t ccet cwt|iv1t|iv2t|isvt|fnvt|cgta cgtb cgtc| |sovt]|];
      reflexivity.
  - (* RListMatch *)
    destruct (real_to_expr re1) as [es|] eqn:Hres; [|discriminate].
    destruct (real_to_expr re2) as [en|] eqn:Hren; [|discriminate].
    destruct (real_to_expr re3) as [ec|] eqn:Hrec; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hds' : (real_expr_depth re1 < fuel')%nat) by lia.
    assert (Hdn' : (real_expr_depth re2 < fuel')%nat) by lia.
    assert (Hdc' : (real_expr_depth re3 < fuel')%nat) by lia.
    simpl.
    rewrite (IHre1 es eq_refl fuel' rho Hds').
    destruct (real_eval rho re1) as [[zs|bs|p1s p2s|fs|ss prs bds ces|vs|rk1s rv1s rk2s rv2s|cf1s cp1s cb1s cf2s cp2s cb2s cces cws|iv1s|iv2s|isvs|fnvs|cgsa cgsb cgsc| |sovs]|]; try reflexivity.
    destruct vs as [| hv tvs].
    + apply (IHre2 en eq_refl fuel' rho Hdn').
    + apply (IHre3 ec eq_refl fuel' ((hd, hv) :: (tl, VList tvs) :: rho) Hdc').
  - (* RPair *)
    destruct (real_to_expr re1) as [e1|] eqn:Hre1; [|discriminate].
    destruct (real_to_expr re2) as [e2|] eqn:Hre2; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1' : (real_expr_depth re1 < fuel')%nat) by lia.
    assert (Hd2' : (real_expr_depth re2 < fuel')%nat) by lia.
    simpl.
    rewrite (IHre1 e1 eq_refl fuel' rho Hd1'), (IHre2 e2 eq_refl fuel' rho Hd2').
    destruct (real_eval rho re1); destruct (real_eval rho re2); reflexivity.
  - (* RProj1 *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1 : (real_expr_depth re < fuel')%nat) by lia.
    simpl. rewrite (IHre e1 eq_refl fuel' rho Hd1).
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|]; reflexivity.
  - (* RProj2 *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1 : (real_expr_depth re < fuel')%nat) by lia.
    simpl. rewrite (IHre e1 eq_refl fuel' rho Hd1).
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|]; reflexivity.
  - (* RCase *)
    destruct (real_to_expr re1) as [es|] eqn:Hres; [|discriminate].
    destruct (real_to_expr re2) as [ec1|] eqn:Hrec1; [|discriminate].
    destruct (real_to_expr re3) as [ec2|] eqn:Hrec2; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hds' : (real_expr_depth re1 < fuel')%nat) by lia.
    assert (Hdc1' : (real_expr_depth re2 < fuel')%nat) by lia.
    assert (Hdc2' : (real_expr_depth re3 < fuel')%nat) by lia.
    simpl.
    rewrite (IHre1 es eq_refl fuel' rho Hds').
    destruct (real_eval rho re1) as [[zs|bs|p1s p2s|fs|ss prs bds ces|vs|rk1s rv1s rk2s rv2s|cf1s cp1s cb1s cf2s cp2s cb2s cces cws|iv1s|iv2s|isvs|fnvs|cgsa cgsb cgsc| |sovs]|]; try reflexivity.
    + apply (IHre2 ec1 eq_refl fuel' ((x1, iv1s) :: rho) Hdc1').
    + apply (IHre3 ec2 eq_refl fuel' ((x2, iv2s) :: rho) Hdc2').
  - (* RSelf: [real_to_expr] gives it [None] unconditionally (see this
       file's header), so the hypothesis [Htrans] is vacuous here. *)
    discriminate Htrans.
  - (* RCall: same as RSelf -- [real_to_expr] gives it [None]
       unconditionally, so [Htrans] is vacuous here too. *)
    discriminate Htrans.
  - (* RSelfN: same as RSelf/RCall -- [real_to_expr] gives it [None]
       unconditionally, so [Htrans] is vacuous here too. *)
    discriminate Htrans.
  - (* RCallN: same as RSelfN. *)
    discriminate Htrans.
  - (* RRecord3: translates to the nested [EPair e1 (EPair e2 e3)],
       so [e2]/[e3] need one more fuel level than [e1] -- the first
       case in this file needing two [destruct fuel] steps, not one.
       [e1] is rewritten (at the still-opaque [fuel1]) *before* the
       second [destruct], so [simpl] has no concrete [S _] fuel
       argument yet to eagerly unfold [eval] through. *)
    destruct (real_to_expr re1) as [e1|] eqn:Hre1; [|discriminate].
    destruct (real_to_expr re2) as [e2|] eqn:Hre2; [|discriminate].
    destruct (real_to_expr re3) as [e3|] eqn:Hre3; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel1]; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    pose proof (Nat.le_max_l (real_expr_depth re1)
                  (S (Nat.max (real_expr_depth re2) (real_expr_depth re3)))) as Hmax1.
    pose proof (Nat.le_max_r (real_expr_depth re1)
                  (S (Nat.max (real_expr_depth re2) (real_expr_depth re3)))) as Hmax2.
    assert (Hd1 : (real_expr_depth re1 < fuel1)%nat) by lia.
    simpl.
    rewrite (IHre1 e1 eq_refl fuel1 rho Hd1).
    destruct fuel1 as [|fuel2]; [lia|].
    pose proof (Nat.le_max_l (real_expr_depth re2) (real_expr_depth re3)) as Hmax3.
    pose proof (Nat.le_max_r (real_expr_depth re2) (real_expr_depth re3)) as Hmax4.
    assert (Hd2 : (real_expr_depth re2 < fuel2)%nat) by lia.
    assert (Hd3 : (real_expr_depth re3 < fuel2)%nat) by lia.
    simpl.
    rewrite (IHre2 e2 eq_refl fuel2 rho Hd2).
    rewrite (IHre3 e3 eq_refl fuel2 rho Hd3).
    destruct (real_eval rho re1); destruct (real_eval rho re2); destruct (real_eval rho re3); reflexivity.
  - (* RProj3_1 *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1 : (real_expr_depth re < fuel')%nat) by lia.
    simpl. rewrite (IHre e1 eq_refl fuel' rho Hd1).
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|]; reflexivity.
  - (* RProj3_2: translates to [EFst (ESnd e)] -- a two-level
       composition, needing a second [destruct fuel] the same way
       [RRecord3] does, but [reflexivity] alone closes every case: a
       [match p2 with VPair v2 _ => Some v2 | _ => None end]-shaped
       term appears *identically* on both sides, with no need to know
       [p2] concretely. *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel1]; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    destruct fuel1 as [|fuel2]; [lia|].
    assert (Hd1 : (real_expr_depth re < fuel2)%nat) by lia.
    simpl. rewrite (IHre e1 eq_refl fuel2 rho Hd1).
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|]; reflexivity.
  - (* RProj3_3: symmetric to [RProj3_2]. *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel1]; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    destruct fuel1 as [|fuel2]; [lia|].
    assert (Hd1 : (real_expr_depth re < fuel2)%nat) by lia.
    simpl. rewrite (IHre e1 eq_refl fuel2 rho Hd1).
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|]; reflexivity.
  - (* RFLit *)
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|]. reflexivity.
  - (* RNone *)
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|]. reflexivity.
  - (* RSome *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1 : (real_expr_depth re < fuel')%nat) by lia.
    simpl. rewrite (IHre e1 eq_refl fuel' rho Hd1).
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv|cga cgb cgc| |sov]|]; reflexivity.
  - (* ROptionMatch *)
    destruct (real_to_expr re1) as [es|] eqn:Hres; [|discriminate].
    destruct (real_to_expr re2) as [en|] eqn:Hren; [|discriminate].
    destruct (real_to_expr re3) as [em|] eqn:Hrem; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hds' : (real_expr_depth re1 < fuel')%nat) by lia.
    assert (Hdn' : (real_expr_depth re2 < fuel')%nat) by lia.
    assert (Hdm' : (real_expr_depth re3 < fuel')%nat) by lia.
    simpl.
    rewrite (IHre1 es eq_refl fuel' rho Hds').
    destruct (real_eval rho re1) as [[zs|bs|p1s p2s|fs|ss prs bds ces|vs|rk1s rv1s rk2s rv2s|cf1s cp1s cb1s cf2s cp2s cb2s cces cws|iv1s|iv2s|isvs|fnvs|cgsa cgsb cgsc| |sovs]|]; try reflexivity.
    + apply (IHre2 en eq_refl fuel' rho Hdn').
    + apply (IHre3 em eq_refl fuel' ((x, sovs) :: rho) Hdm').
  - (* RRecordN: no per-case [induction re]-supplied IH at all for
       [es]'s own elements (confirmed directly -- the open goal here
       carries no [Forall]-shaped hypothesis, only [es] itself), so
       this recurses by hand: a fresh, local induction on the list
       [es] for the "walk the tail" part, reaching for [SELF] -- the
       [fix SELF 1] self-reference this whole proof opened with,
       usable here precisely because [fix]'s own guardedness check is
       more permissive than a [Fixpoint]'s nested anonymous nested-fix
       one (confirmed directly: the very same "element obtained by a
       *separate*, nested list induction" shape that [real_eval]/
       [real_to_expr]/[real_expr_depth] above all had to work around
       is accepted without complaint here) -- for each list *head*'s
       own preservation, since a head can be any [real_expr] shape,
       not just another [RRecordN]. *)
    rewrite real_expr_depth_record_eq in Hfuel.
    revert e Htrans fuel rho Hfuel.
    induction es as [| e1 es' IHes]; intros e Htrans fuel rho Hfuel;
      simpl in Htrans, Hfuel.
    + discriminate.
    + destruct es' as [| e2 rest].
      * (* es = [e1] *)
        assert (Hf1 : (real_expr_depth e1 < fuel)%nat) by lia.
        exact (SELF e1 e Htrans fuel rho Hf1).
      * (* es = e1 :: e2 :: rest *)
        destruct (real_to_expr e1) as [ee|] eqn:He1; [|discriminate].
        destruct ((fix go (xs : list real_expr) : option expr :=
                     match xs with
                     | [] => None
                     | [e0] => real_to_expr e0
                     | e0 :: rest0 =>
                         match real_to_expr e0 with
                         | Some ee0 =>
                             match go rest0 with
                             | Some erest0 => Some (EPair ee0 erest0)
                             | None => None
                             end
                         | None => None
                         end
                     end) (e2 :: rest)) as [erest'|] eqn:Hrest; [|discriminate].
        inversion Htrans; subst e.
        destruct fuel as [|fuel']; [lia|].
        assert (Hf1 : (real_expr_depth e1 < fuel')%nat) by lia.
        pose proof (SELF e1 ee He1 fuel' rho Hf1) as IH1.
        assert (Hfuel' : (real_expr_depth (RRecordN (e2 :: rest)) < fuel')%nat)
          by (rewrite real_expr_depth_record_eq; lia).
        pose proof (IHes erest' eq_refl fuel' rho Hfuel') as IH2.
        simpl. rewrite IH1, IH2. reflexivity.
  - (* RProjN: unlike [RRecordN], [scrutinee] is an ordinary [real_expr]
       field, so [induction re]'s own auto-generated [IHre] already
       suffices -- no need for the outer [IHn] here. The only new
       machinery needed is [eval_expr_skip_snd], turning the *variable*
       number of [ESnd]s [expr_skip_snd nskip] builds into a single
       fuel-arithmetic step instead of [destruct fuel] once per skip
       (which [RProj3_2]/[RProj3_3] above could afford, fixed at
       exactly one, but a genuinely-[n]-ary [nskip] cannot). *)
    destruct (real_to_expr re) as [es|] eqn:Hres; [|discriminate].
    inversion Htrans; subst e.
    destruct last eqn:Hlast; simpl in Hfuel.
    + (* last field: bare [expr_skip_snd nskip es], no further [EFst] *)
      assert (Hskip : (nskip < fuel)%nat) by lia.
      assert (Hd1 : (real_expr_depth re < fuel - nskip)%nat) by lia.
      pose proof (IHre es eq_refl (fuel - nskip)%nat rho Hd1) as IH1.
      simpl. rewrite (eval_expr_skip_snd nskip fuel rho es Hskip), IH1.
      destruct (real_eval rho re) as [v|]; [| reflexivity].
      destruct (value_skip_snd nskip v); reflexivity.
    + (* not last: one [EFst] wraps the skip chain *)
      destruct fuel as [|fuel'']; [lia|].
      assert (Hskip : (nskip < fuel'')%nat) by lia.
      assert (Hd1 : (real_expr_depth re < fuel'' - nskip)%nat) by lia.
      pose proof (IHre es eq_refl (fuel'' - nskip)%nat rho Hd1) as IH1.
      simpl. rewrite (eval_expr_skip_snd nskip fuel'' rho es Hskip), IH1.
      destruct (real_eval rho re) as [v|]; [| reflexivity].
      destruct (value_skip_snd nskip v) as [v'|]; [destruct v' | ]; reflexivity.
Qed.

(** [real_to_expr_ctx]: [real_to_expr] again, case for case, but
    carrying one extra piece of context -- the name of the [Fixpoint]
    currently being translated, if any -- so an [RSelf arg] can
    translate to a real self-call, [EApp (EVar f) arg'], the same
    shape [eval]'s own [ERec]/[EApp] case already expects for a
    self-referencing closure (Lang.v). A deliberate near-duplicate of
    [real_to_expr] rather than a generalization of it: every other
    case is untouched (just threads [self] through unchanged), and
    keeping [real_to_expr] itself exactly as proved above means
    nothing above this line needed re-proving to add this. *)
Fixpoint real_to_expr_ctx (self : option var) (siblings : list var) (re : real_expr) : option expr :=
  match re with
  | RRel name => Some (EVar name)
  | RZLit z => Some (EConst z)
  | RBoolLit b => Some (EBool b)
  | RApp1 fn arg =>
      match real_to_expr_ctx self siblings arg with
      | Some e1 =>
          if string_dec fn "negb" then Some (ENot e1)
          else if string_dec fn "fst" then Some (EFst e1)
          else if string_dec fn "snd" then Some (ESnd e1)
          else None
      | None => None
      end
  | RApp2 fn a1 a2 =>
      match real_to_expr_ctx self siblings a1, real_to_expr_ctx self siblings a2 with
      | Some e1, Some e2 =>
          if string_dec fn "add" then Some (EAdd e1 e2)
          else if string_dec fn "sub" then Some (ESub e1 e2)
          else if string_dec fn "mul" then Some (EMul e1 e2)
          else if string_dec fn "eqb" then Some (EEq e1 e2)
          else if string_dec fn "ltb" then Some (ELt e1 e2)
          else if string_dec fn "leb" then Some (ELe e1 e2)
          else if string_dec fn "andb" then Some (EAnd e1 e2)
          else if string_dec fn "orb" then Some (EOr e1 e2)
          else None
      | _, _ => None
      end
  | RIfBool c t e =>
      match real_to_expr_ctx self siblings c, real_to_expr_ctx self siblings t, real_to_expr_ctx self siblings e with
      | Some ec, Some et, Some ee => Some (EIf ec et ee)
      | _, _, _ => None
      end
  | RNil => Some ENil
  | RCons hd tl =>
      match real_to_expr_ctx self siblings hd, real_to_expr_ctx self siblings tl with
      | Some eh, Some et => Some (ECons eh et)
      | _, _ => None
      end
  | RListMatch scrutinee nilcase hd tl conscase =>
      match real_to_expr_ctx self siblings scrutinee, real_to_expr_ctx self siblings nilcase,
            real_to_expr_ctx self siblings conscase with
      | Some es, Some en, Some ec => Some (EListMatch es en hd tl ec)
      | _, _, _ => None
      end
  | RPair e1 e2 =>
      match real_to_expr_ctx self siblings e1, real_to_expr_ctx self siblings e2 with
      | Some e1', Some e2' => Some (EPair e1' e2')
      | _, _ => None
      end
  | RProj1 scrutinee =>
      match real_to_expr_ctx self siblings scrutinee with
      | Some e => Some (EFst e)
      | None => None
      end
  | RProj2 scrutinee =>
      match real_to_expr_ctx self siblings scrutinee with
      | Some e => Some (ESnd e)
      | None => None
      end
  | RCase scrutinee x1 case1 x2 case2 =>
      match real_to_expr_ctx self siblings scrutinee, real_to_expr_ctx self siblings case1, real_to_expr_ctx self siblings case2 with
      | Some es, Some ec1, Some ec2 => Some (ECase es x1 ec1 x2 ec2)
      | _, _, _ => None
      end
  | RSelf arg =>
      match self, real_to_expr_ctx self siblings arg with
      | Some f, Some arg' => Some (EApp (EVar f) arg')
      | _, _ => None
      end
  | RCall fname arg =>
      match real_to_expr_ctx self siblings arg with
      | Some arg' =>
          if List.existsb (fun s => if string_dec fname s then true else false) siblings
          then Some (EApp (EVar fname) arg')
          else None
      | None => None
      end
  | RSelfN args =>
      match self with
      | Some f =>
          (fix curry_args (es : list real_expr) (acc : expr) : option expr :=
             match es with
             | [] => Some acc
             | e :: rest =>
                 match real_to_expr_ctx self siblings e with
                 | Some e' => curry_args rest (EApp acc e')
                 | None => None
                 end
             end) args (EVar f)
      | None => None
      end
  | RCallN fname args =>
      if List.existsb (fun s => if string_dec fname s then true else false) siblings
      then
        (fix curry_args (es : list real_expr) (acc : expr) : option expr :=
           match es with
           | [] => Some acc
           | e :: rest =>
               match real_to_expr_ctx self siblings e with
               | Some e' => curry_args rest (EApp acc e')
               | None => None
               end
           end) args (EVar fname)
      else None
  | RRecord3 e1 e2 e3 =>
      match real_to_expr_ctx self siblings e1, real_to_expr_ctx self siblings e2, real_to_expr_ctx self siblings e3 with
      | Some e1', Some e2', Some e3' => Some (EPair e1' (EPair e2' e3'))
      | _, _, _ => None
      end
  | RProj3_1 scrutinee =>
      match real_to_expr_ctx self siblings scrutinee with
      | Some e => Some (EFst e)
      | None => None
      end
  | RProj3_2 scrutinee =>
      match real_to_expr_ctx self siblings scrutinee with
      | Some e => Some (EFst (ESnd e))
      | None => None
      end
  | RProj3_3 scrutinee =>
      match real_to_expr_ctx self siblings scrutinee with
      | Some e => Some (ESnd (ESnd e))
      | None => None
      end
  | RFLit f => Some (EFConst f)
  | RNone => Some ENone
  | RSome e1 =>
      match real_to_expr_ctx self siblings e1 with
      | Some e1' => Some (ESome e1')
      | None => None
      end
  | ROptionMatch scrutinee nonecase x somecase =>
      match real_to_expr_ctx self siblings scrutinee, real_to_expr_ctx self siblings nonecase,
            real_to_expr_ctx self siblings somecase with
      | Some es, Some en, Some em => Some (EOptionMatch es en x em)
      | _, _, _ => None
      end
  | RRecordN es =>
      (fix go (xs : list real_expr) : option expr :=
         match xs with
         | [] => None
         | [e] => real_to_expr_ctx self siblings e
         | e :: rest =>
             match real_to_expr_ctx self siblings e, go rest with
             | Some ee, Some erest' => Some (EPair ee erest')
             | _, _ => None
             end
         end) es
  | RProjN nskip last scrutinee =>
      match real_to_expr_ctx self siblings scrutinee with
      | Some e => Some (if last then expr_skip_snd nskip e else EFst (expr_skip_snd nskip e))
      | None => None
      end
  end.

(** [real_fix_decl]: [real_decl]'s cousin for a single self-recursive
    [Fixpoint] of exactly one argument. [real_fix_decl_multi] just
    below is its generalization to more than one argument -- this
    one-argument record and its own [real_fix_decl_to_expr] are left
    exactly as they always were, so every existing proof/example
    using them keeps working unchanged. *)
Record real_fix_decl : Type := mk_real_fix_decl {
  rfd_name : var;
  rfd_param : var;
  rfd_body : real_expr
}.

Definition real_fix_decl_to_expr (rfd : real_fix_decl) : option expr :=
  match real_to_expr_ctx (Some rfd.(rfd_name)) [] rfd.(rfd_body) with
  | Some body => Some (ERec rfd.(rfd_name) rfd.(rfd_param) body)
  | None => None
  end.

(** [real_fix_decl_multi]: the general, N-argument generalization of
    [real_fix_decl] (this file's header's [RSelfN]/[RCallN] comment
    has the confirmed-by-probe design). [rfdm_params] must be
    non-empty -- a 0-argument "recursive function" isn't a shape any
    real [Fixpoint] extracts as (every [fixgroup:item] this project
    has seen has at least one [argnames] entry), so
    [real_fix_decl_multi_to_expr] simply gives [None] for one. For a
    singleton [rfdm_params], this degenerates to *exactly*
    [real_fix_decl_to_expr]'s own output ([ERec f p1 body'], no extra
    [ELam] wrapper) -- confirmed by the [fold_left] below visiting an
    empty tail. *)
Record real_fix_decl_multi : Type := mk_real_fix_decl_multi {
  rfdm_name : var;
  rfdm_params : list var;
  rfdm_body : real_expr
}.

(** Curry: [ERec f p1 (ELam p2 (... (ELam pn body') ...))] -- [p1] is
    bound the same way [real_fix_decl_to_expr] already binds its one
    parameter (via [ERec] itself), every further parameter via a
    plain, already-proven [ELam], right-associated so [pn] is
    innermost (closest to [body']), matching the left-to-right
    [args]/[argnames] order a real multi-argument call/declaration
    already carries (this file's header). *)
Definition real_fix_decl_multi_to_expr (rfdm : real_fix_decl_multi) : option expr :=
  match rfdm.(rfdm_params) with
  | [] => None
  | p1 :: rest_params =>
      match real_to_expr_ctx (Some rfdm.(rfdm_name)) [] rfdm.(rfdm_body) with
      | Some body =>
          Some (ERec rfdm.(rfdm_name) p1
                  (fold_right (fun p acc => ELam p acc) body rest_params))
      | None => None
      end
  end.

(** [real_fix_decl] deliberately has no generic preservation theorem
    of its own, the way [real_decl_to_expr_preserves_semantics] does:
    a [Fixpoint]'s recursion depth depends on its *argument* (e.g. a
    list's length), not on [rfd_body]'s own static size, the same
    reason [eval]'s own [fuel] for [EApp] can't be derived from
    [expr_fuel] either (Lang.v's header). The right proof shape is a
    direct induction on the argument against the real Gallina
    [Fixpoint], per declaration -- see examples/NaturalCoq.v's
    [any_true_expr_matches_real_definition] for a worked instance. *)

(** [real_fix_group_decl]: the *general*, N-way mutually-recursive
    generalization of [real_fix_decl] -- a real [Fixpoint ... with
    ...] group of two or more single-argument functions, each
    possibly calling any member (including itself) by name. Mirrors
    [Lang.v]'s own [ERecGroup fns]'s representation almost exactly: a
    list of [(name, param, body)] triples, one per group member, in
    declaration order. *)
Record real_fix_group_decl : Type := mk_real_fix_group_decl {
  rfgd_fns : list (var * var * real_expr)
}.

(** Translating a member's own body uses [self := None]/[siblings :=
    every member's name]: within an N-way group, *every* call to a
    group member -- including a self-call -- was parsed as [RCall],
    never [RSelf] (see [RealJson.v]'s [decl_fixgroup_of_json]), so
    there is no distinguished "self" name to pass here the way
    [real_fix_decl_to_expr] passes one. Builds [ERecGroup], the exact
    target [eval]'s own [EApp]/[VClosureGroup] case already expects
    for a group member's closure (Lang.v) -- already proven there, so
    nothing above this line needed re-proving to add this. *)
Definition real_fix_group_decl_to_expr (rfgd : real_fix_group_decl) : option expr :=
  let names := List.map (fun x => fst (fst x)) rfgd.(rfgd_fns) in
  match
    (fix go (fns : list (var * var * real_expr)) : option (list (var * var * expr)) :=
       match fns with
       | [] => Some []
       | (f, p, b) :: rest =>
           match real_to_expr_ctx None names b, go rest with
           | Some b', Some rest' => Some ((f, p, b') :: rest')
           | _, _ => None
           end
       end) rfgd.(rfgd_fns)
  with
  | Some fns' => Some (ERecGroup fns')
  | None => None
  end.

(** Like [real_fix_decl], deliberately no generic preservation
    theorem: an N-way group's recursion depth is just as
    argument-dependent as a single [Fixpoint]'s, for the same reason
    (this file's [real_fix_decl] comment just above). The right proof
    shape is the same concrete-instance style, now one induction per
    member that's actually exercised by the check -- see
    examples/NaturalCoq.v's [is_even_expr_matches_real_definition] for
    a worked instance (an actual 2-way cross-call, confirmed against
    the real Gallina [is_even]/[is_odd] pair, not just analogous to
    [any_true]'s single-function case). *)

(** [real_decl]: models the [decl:term]/[expr:lambda] wrapper around a
    whole real, human-written multi-argument [Definition] -- not just
    its body. Coq's own extraction JSON presents a multi-arg function
    as *one* [expr:lambda] node carrying a direct [argnames] list, not
    curried (confirmed directly, see this file's header) -- so this is
    a thin wrapper around [real_to_expr], not a new translation
    target: the body is translated exactly as before, and [argnames]
    is carried through only to supply the generated Python function's
    own parameter list ([PyPrint.v]'s [py_function]), the same names
    [examples/Kinematics.v]/[examples/NaturalCoq.v] already pass by
    hand at the call site -- now read off the real declaration itself
    instead. *)
Record real_decl : Type := mk_real_decl {
  rd_argnames : list var;
  rd_body : real_expr
}.

Definition real_decl_to_expr (rd : real_decl) : option expr :=
  real_to_expr rd.(rd_body).

(** The calling convention [py_function]'s generated Python parameter
    list already assumes: [rd_argnames] zipped positionally against
    the supplied arguments. Mismatched arity is simply [None] -- the
    same honest partiality [real_to_expr] itself already uses, not a
    new kind of runtime check. *)
Fixpoint zip_env (names : list var) (args : list value) : option env :=
  match names, args with
  | [], [] => Some []
  | n :: names', a :: args' =>
      match zip_env names' args' with
      | Some rest => Some ((n, a) :: rest)
      | None => None
      end
  | _, _ => None
  end.

Definition real_decl_eval (rd : real_decl) (args : list value) : option value :=
  match zip_env rd.(rd_argnames) args with
  | Some rho => real_eval rho rd.(rd_body)
  | None => None
  end.

(** A direct corollary of [real_to_expr_preserves_semantics]: nothing
    new to prove about the body, only that the same environment built
    from [rd_argnames]/[args] is what both sides evaluate under. *)
Theorem real_decl_to_expr_preserves_semantics :
  forall rd e, real_decl_to_expr rd = Some e ->
    forall fuel args rho, (real_expr_depth rd.(rd_body) < fuel)%nat ->
      zip_env rd.(rd_argnames) args = Some rho ->
      eval fuel rho e = real_decl_eval rd args.
Proof.
  intros rd e Htrans fuel args rho Hfuel Hzip.
  unfold real_decl_eval. rewrite Hzip.
  apply (real_to_expr_preserves_semantics rd.(rd_body) e Htrans fuel rho Hfuel).
Qed.
