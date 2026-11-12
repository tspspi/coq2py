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
    access. [option]'s [None]/[Some] is deliberately not covered the
    same way: [None] carries *no* payload, so it doesn't fit
    [EInl]/[EInr]'s both-sides-have-a-payload shape without a second,
    separate encoding -- not attempted here. *)
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

From Coq Require Import ZArith String List Bool Lia.
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
  | RSelf (arg : real_expr).

(** The reference semantics: not a reimplementation of [Z.add]/
    [Z.ltb]/etc, but a direct call to Coq's own, so this file's trust
    boundary is exactly "Coq's standard library means what it says it
    means" -- the same category of trust as the kernel itself, not a
    new assumption this file introduces. *)
Fixpoint real_eval (rho : env) (re : real_expr) : option value :=
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
  end.

Theorem real_to_expr_preserves_semantics :
  forall re e, real_to_expr re = Some e ->
    forall fuel rho, (real_expr_depth re < fuel)%nat ->
      eval fuel rho e = real_eval rho re.
Proof.
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
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv]|];
       reflexivity|].
    destruct (string_dec fn "fst") as [Heq|Hne2];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv]|];
       reflexivity|].
    destruct (string_dec fn "snd") as [Heq|Hne3];
      [inversion Htrans; subst; simpl; rewrite IH1;
       destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv]|];
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
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
       reflexivity|].
    destruct (string_dec fn "sub") as [Heq|Hne2];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
       reflexivity|].
    destruct (string_dec fn "mul") as [Heq|Hne3];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
       reflexivity|].
    destruct (string_dec fn "eqb") as [Heq|Hne4];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
       reflexivity|].
    destruct (string_dec fn "ltb") as [Heq|Hne5];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
       reflexivity|].
    destruct (string_dec fn "leb") as [Heq|Hne6];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
       reflexivity|].
    destruct (string_dec fn "andb") as [Heq|Hne7];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
       reflexivity|].
    destruct (string_dec fn "orb") as [Heq|Hne8];
      [inversion Htrans; subst; simpl; rewrite IH1, IH2;
       destruct (real_eval rho re1) as [[z1|b1|p1a p1b|f1|s1 pr1 bd1 ce1|vs1|rk1a rv1a rk1b rv1b|cf1a cp1a cb1a cf1b cp1b cb1b cce1 cw1|iv1a|iv1b|isv1|fnv1]|];
       destruct (real_eval rho re2) as [[z2|b2|p2a p2b|f2|s2 pr2 bd2 ce2|vs2|rk2a rv2a rk2b rv2b|cf2a cp2a cb2a cf2b cp2b cb2b cce2 cw2|iv2a|iv2b|isv2|fnv2]|];
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
    destruct (real_eval rho re1) as [[zc|bc|p1 p2|fc|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv]|]; try reflexivity.
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
    destruct (real_eval rho re1) as [[zh|bh|p1h p2h|fh|sh prh bdh ceh|vsh|rk1h rv1h rk2h rv2h|cf1h cp1h cb1h cf2h cp2h cb2h cceh cwh|iv1h|iv2h|isvh|fnvh]|];
      destruct (real_eval rho re2) as [[zt|bt|p1t p2t|ft|st prt bdt cet|vst|rk1t rv1t rk2t rv2t|cf1t cp1t cb1t cf2t cp2t cb2t ccet cwt|iv1t|iv2t|isvt|fnvt]|];
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
    destruct (real_eval rho re1) as [[zs|bs|p1s p2s|fs|ss prs bds ces|vs|rk1s rv1s rk2s rv2s|cf1s cp1s cb1s cf2s cp2s cb2s cces cws|iv1s|iv2s|isvs|fnvs]|]; try reflexivity.
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
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv]|]; reflexivity.
  - (* RProj2 *)
    destruct (real_to_expr re) as [e1|] eqn:Hre1; [|discriminate].
    inversion Htrans; subst.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl in Hfuel.
    assert (Hd1 : (real_expr_depth re < fuel')%nat) by lia.
    simpl. rewrite (IHre e1 eq_refl fuel' rho Hd1).
    destruct (real_eval rho re) as [[z|b|p1 p2|f|s pr bd ce|vs|rk1 rv1 rk2 rv2|cf1 cp1 cb1 cf2 cp2 cb2 cce cw|iv1|iv2|isv|fnv]|]; reflexivity.
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
    destruct (real_eval rho re1) as [[zs|bs|p1s p2s|fs|ss prs bds ces|vs|rk1s rv1s rk2s rv2s|cf1s cp1s cb1s cf2s cp2s cb2s cces cws|iv1s|iv2s|isvs|fnvs]|]; try reflexivity.
    + apply (IHre2 ec1 eq_refl fuel' ((x1, iv1s) :: rho) Hdc1').
    + apply (IHre3 ec2 eq_refl fuel' ((x2, iv2s) :: rho) Hdc2').
  - (* RSelf: [real_to_expr] gives it [None] unconditionally (see this
       file's header), so the hypothesis [Htrans] is vacuous here. *)
    discriminate Htrans.
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
Fixpoint real_to_expr_ctx (self : option var) (re : real_expr) : option expr :=
  match re with
  | RRel name => Some (EVar name)
  | RZLit z => Some (EConst z)
  | RBoolLit b => Some (EBool b)
  | RApp1 fn arg =>
      match real_to_expr_ctx self arg with
      | Some e1 =>
          if string_dec fn "negb" then Some (ENot e1)
          else if string_dec fn "fst" then Some (EFst e1)
          else if string_dec fn "snd" then Some (ESnd e1)
          else None
      | None => None
      end
  | RApp2 fn a1 a2 =>
      match real_to_expr_ctx self a1, real_to_expr_ctx self a2 with
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
      match real_to_expr_ctx self c, real_to_expr_ctx self t, real_to_expr_ctx self e with
      | Some ec, Some et, Some ee => Some (EIf ec et ee)
      | _, _, _ => None
      end
  | RNil => Some ENil
  | RCons hd tl =>
      match real_to_expr_ctx self hd, real_to_expr_ctx self tl with
      | Some eh, Some et => Some (ECons eh et)
      | _, _ => None
      end
  | RListMatch scrutinee nilcase hd tl conscase =>
      match real_to_expr_ctx self scrutinee, real_to_expr_ctx self nilcase,
            real_to_expr_ctx self conscase with
      | Some es, Some en, Some ec => Some (EListMatch es en hd tl ec)
      | _, _, _ => None
      end
  | RPair e1 e2 =>
      match real_to_expr_ctx self e1, real_to_expr_ctx self e2 with
      | Some e1', Some e2' => Some (EPair e1' e2')
      | _, _ => None
      end
  | RProj1 scrutinee =>
      match real_to_expr_ctx self scrutinee with
      | Some e => Some (EFst e)
      | None => None
      end
  | RProj2 scrutinee =>
      match real_to_expr_ctx self scrutinee with
      | Some e => Some (ESnd e)
      | None => None
      end
  | RCase scrutinee x1 case1 x2 case2 =>
      match real_to_expr_ctx self scrutinee, real_to_expr_ctx self case1, real_to_expr_ctx self case2 with
      | Some es, Some ec1, Some ec2 => Some (ECase es x1 ec1 x2 ec2)
      | _, _, _ => None
      end
  | RSelf arg =>
      match self, real_to_expr_ctx self arg with
      | Some f, Some arg' => Some (EApp (EVar f) arg')
      | _, _ => None
      end
  end.

(** [real_fix_decl]: [real_decl]'s cousin for a single self-recursive
    [Fixpoint] of exactly one argument -- general mutually-recursive
    fixgroups, and recursive functions of more than one argument, are
    not yet modeled (see this file's header). *)
Record real_fix_decl : Type := mk_real_fix_decl {
  rfd_name : var;
  rfd_param : var;
  rfd_body : real_expr
}.

Definition real_fix_decl_to_expr (rfd : real_fix_decl) : option expr :=
  match real_to_expr_ctx (Some rfd.(rfd_name)) rfd.(rfd_body) with
  | Some body => Some (ERec rfd.(rfd_name) rfd.(rfd_param) body)
  | None => None
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
