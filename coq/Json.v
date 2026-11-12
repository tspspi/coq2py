(** Json.v

    A textual codec for [expr] (Lang.v), in a JSON-flavoured syntax
    restricted to exactly what's needed for our supported subset: no
    whitespace flexibility, no general string escaping (identifiers are
    required to be ASCII alnum/underscore, nonempty), fixed field order per
    constructor. This stands in for Coq's own [Extraction Language JSON]
    output -- see docs/roadmap.md for the honest status of reconciling the
    two.

    This is the proof GOAL.md calls for on the ingestion side: "it is
    acceptable if it only accepts Coq's subset language", so the theorem
    below is a round-trip property over exactly that restricted grammar,
    not a general JSON parser. [print_expr] *is* the grammar specification
    (there is no separate prose grammar to be faithful to); [parse_expr] is
    proved to invert it on every [expr] whose identifiers are valid. *)

From Coq Require Import ZArith String List Ascii Bool Lia.
From Coq Require Import Decimal DecimalString DecimalPos DecimalZ.
From Coq Require Import Floats.PrimFloat Floats.FloatOps Floats.SpecFloat Floats.FloatAxioms.
Import ListNotations.
Require Import Lang.
Open Scope Z_scope.
Open Scope string_scope.

(* ----------------------------------------------------------------- *)
(** * Character classification *)

Definition is_digit (a : ascii) : bool :=
  let n := nat_of_ascii a in
  andb (Nat.leb 48 n) (Nat.leb n 57).

Definition is_alpha (a : ascii) : bool :=
  let n := nat_of_ascii a in
  orb (andb (Nat.leb 65 n) (Nat.leb n 90))
      (andb (Nat.leb 97 n) (Nat.leb n 122)).

Definition is_alnum (a : ascii) : bool :=
  orb (is_digit a) (orb (is_alpha a) (Ascii.eqb a "_"%char)).

Definition quote_char : ascii := """"%char.
Definition minus_char : ascii := "-"%char.

Fixpoint string_forallb (p : ascii -> bool) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String a s' => andb (p a) (string_forallb p s')
  end.

Definition is_valid_ident (s : string) : bool :=
  match s with
  | EmptyString => false
  | _ => string_forallb is_alnum s
  end.

(* ----------------------------------------------------------------- *)
(** * Small parsing combinators over [string] *)

Fixpoint take_while (p : ascii -> bool) (s : string) : (string * string) :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String a s' =>
      if p a then
        let (tok, rest) := take_while p s' in
        (String a tok, rest)
      else (EmptyString, s)
  end.

(** Consume an expected literal prefix, failing if [s] doesn't start with
    [lit]. *)
Fixpoint expect (lit s : string) : option string :=
  match lit with
  | EmptyString => Some s
  | String a lit' =>
      match s with
      | String b s' => if Ascii.eqb a b then expect lit' s' else None
      | EmptyString => None
      end
  end.

Lemma string_append_assoc : forall a b c : string, (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  induction a as [| x a' IH]; intros b c; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma expect_app : forall lit rest, expect lit (lit ++ rest) = Some rest.
Proof.
  induction lit as [| a lit' IH]; intro rest; simpl.
  - reflexivity.
  - rewrite Ascii.eqb_refl. apply IH.
Qed.

Lemma take_while_app_stop :
  forall (p : ascii -> bool) (x : string),
    string_forallb p x = true ->
    forall (a : ascii) (rest : string),
      p a = false ->
      take_while p (x ++ String a rest) = (x, String a rest).
Proof.
  induction x as [| c x' IH]; intros Hall a rest Ha; simpl.
  - rewrite Ha. reflexivity.
  - simpl in Hall. apply andb_true_iff in Hall as [Hc Hall'].
    rewrite Hc. rewrite (IH Hall' a rest Ha). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** * Integers *)

Definition z_to_string (z : Z) : string := NilZero.string_of_int (Z.to_int z).

Definition z_of_string (s : string) : option Z :=
  match NilZero.int_of_string s with
  | Some d => Some (Z.of_int d)
  | None => None
  end.

Lemma to_int_not_pos_nil : forall z : Z, Z.to_int z <> Decimal.Pos Decimal.Nil.
Proof.
  intro z; unfold Z.to_int; destruct z.
  - discriminate.
  - intro H; injection H as H; now apply (DecimalPos.Unsigned.to_uint_nonnil p).
  - discriminate.
Qed.

Lemma to_int_not_neg_nil : forall z : Z, Z.to_int z <> Decimal.Neg Decimal.Nil.
Proof.
  intro z; unfold Z.to_int; destruct z.
  - discriminate.
  - discriminate.
  - intro H; injection H as H; now apply (DecimalPos.Unsigned.to_uint_nonnil p).
Qed.

(** Every integer round-trips through [z_to_string]/[z_of_string]. *)
Lemma z_round_trip : forall z : Z, z_of_string (z_to_string z) = Some z.
Proof.
  intro z. unfold z_of_string, z_to_string.
  rewrite NilZero.isi by (auto using to_int_not_pos_nil, to_int_not_neg_nil).
  f_equal. apply DecimalZ.of_to.
Qed.

Lemma nilempty_string_of_uint_all_digits :
  forall d, string_forallb is_digit (NilEmpty.string_of_uint d) = true.
Proof.
  induction d; simpl; try reflexivity; rewrite IHd; reflexivity.
Qed.

Lemma nilzero_string_of_uint_cons :
  forall d, exists c s, NilZero.string_of_uint d = String c s.
Proof.
  intro d. unfold NilZero.string_of_uint. destruct d; simpl; eauto.
Qed.

Lemma nilzero_string_of_uint_all_digits :
  forall d, string_forallb is_digit (NilZero.string_of_uint d) = true.
Proof.
  intro d. unfold NilZero.string_of_uint. destruct d; try reflexivity.
  all: apply nilempty_string_of_uint_all_digits.
Qed.

(** The parser for numbers: an optional leading [-] followed by a run of
    digits, decoded via the very same [NilZero] machinery [z_to_string]
    uses to print -- so [z_round_trip] carries over directly. *)
Definition parse_number (s : string) : option (Z * string) :=
  match s with
  | EmptyString => None
  | String a s1 =>
      if Ascii.eqb a minus_char then
        let (digits, rest) := take_while is_digit s1 in
        match z_of_string (String minus_char digits) with
        | Some z => Some (z, rest)
        | None => None
        end
      else
        let (digits, rest) := take_while is_digit s in
        match z_of_string digits with
        | Some z => Some (z, rest)
        | None => None
        end
  end.

(** A reflexivity-proved restatement of [parse_number] on an explicit
    [String h t] argument. [rewrite]-ing with this (rather than relying on
    [simpl]/[unfold] to fire through whatever append/rewrite steps built up
    the argument) is what makes the proof below robust. *)
Lemma string_app_cons : forall h t rest, String h t ++ rest = String h (t ++ rest).
Proof. reflexivity. Qed.

Lemma parse_number_unfold :
  forall h t,
    parse_number (String h t) =
      if Ascii.eqb h minus_char then
        let (digits, rest) := take_while is_digit t in
        match z_of_string (String minus_char digits) with
        | Some z => Some (z, rest)
        | None => None
        end
      else
        let (digits, rest) := take_while is_digit (String h t) in
        match z_of_string digits with
        | Some z => Some (z, rest)
        | None => None
        end.
Proof. reflexivity. Qed.

Lemma parse_number_print :
  forall z (a : ascii) rest,
    is_digit a = false -> a <> minus_char ->
    parse_number (z_to_string z ++ String a rest) = Some (z, String a rest).
Proof.
  intros z a rest Hdig Hmin.
  destruct z as [|p|p].
  - (* z = 0 *)
    change (z_to_string 0 ++ String a rest) with (String "0"%char (String a rest)).
    rewrite parse_number_unfold.
    simpl. rewrite Hdig. reflexivity.
  - (* z = Zpos p *)
    destruct (nilzero_string_of_uint_cons (Pos.to_uint p)) as (c & s0 & Hcs).
    pose proof (nilzero_string_of_uint_all_digits (Pos.to_uint p)) as Hall.
    rewrite Hcs in Hall.
    assert (Hzp : z_to_string (Zpos p) = String c s0).
    { unfold z_to_string, NilZero.string_of_int.
      replace (Z.to_int (Zpos p)) with (Decimal.Pos (Pos.to_uint p)) by reflexivity.
      simpl. exact Hcs. }
    rewrite Hzp.
    rewrite (string_app_cons c s0 (String a rest)).
    rewrite parse_number_unfold.
    assert (Hcm : c <> minus_char) by (intro Heq; subst c; simpl in Hall; discriminate).
    assert (Hcmb : Ascii.eqb c minus_char = false) by (apply (proj2 (Ascii.eqb_neq _ _)); exact Hcm).
    rewrite Hcmb.
    rewrite <- (string_app_cons c s0 (String a rest)).
    rewrite (take_while_app_stop is_digit (String c s0) Hall a rest Hdig).
    assert (Hfinal : z_of_string (String c s0) = Some (Zpos p))
      by (rewrite <- Hzp; apply z_round_trip).
    rewrite Hfinal. reflexivity.
  - (* z = Zneg p *)
    assert (Hzn : z_to_string (Zneg p) = String minus_char (NilZero.string_of_uint (Pos.to_uint p))).
    { unfold z_to_string, NilZero.string_of_int.
      replace (Z.to_int (Zneg p)) with (Decimal.Neg (Pos.to_uint p)) by reflexivity.
      reflexivity. }
    rewrite Hzn.
    change (String minus_char (NilZero.string_of_uint (Pos.to_uint p)) ++ String a rest)
      with (String minus_char (NilZero.string_of_uint (Pos.to_uint p) ++ String a rest)).
    rewrite parse_number_unfold.
    rewrite Ascii.eqb_refl.
    pose proof (nilzero_string_of_uint_all_digits (Pos.to_uint p)) as Hall.
    rewrite (take_while_app_stop is_digit (NilZero.string_of_uint (Pos.to_uint p)) Hall a rest Hdig).
    assert (Hfinal : z_of_string (String minus_char (NilZero.string_of_uint (Pos.to_uint p))) = Some (Zneg p))
      by (rewrite <- Hzn; apply z_round_trip).
    rewrite Hfinal. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** * Natural numbers (the [ERepeat] iteration count) *)

(** Reuses the [Z] codec entirely -- a [nat] is just a [Z] known to be
    non-negative, so there is no new numeral syntax here, and the
    round-trip carries straight over from [parse_number_print] plus
    [Nat2Z.id] (a standard-library fact, not a new assumption). *)
Definition nat_to_string (n : nat) : string := z_to_string (Z.of_nat n).

Definition parse_nat (s : string) : option (nat * string) :=
  match parse_number s with
  | Some (z, rest) => Some (Z.to_nat z, rest)
  | None => None
  end.

Lemma parse_nat_print :
  forall n (a : ascii) rest,
    is_digit a = false -> a <> minus_char ->
    parse_nat (nat_to_string n ++ String a rest) = Some (n, String a rest).
Proof.
  intros n a rest Hdig Hmin.
  unfold parse_nat, nat_to_string.
  rewrite (parse_number_print (Z.of_nat n) a rest Hdig Hmin).
  rewrite Nat2Z.id. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** * Quoted identifiers *)

Definition quote_string (x : string) : string :=
  String quote_char (x ++ String quote_char EmptyString).

Definition parse_qstring (s : string) : option (string * string) :=
  match s with
  | String a s1 =>
      if Ascii.eqb a quote_char then
        let (tok, rest) := take_while is_alnum s1 in
        match rest with
        | String b rest' =>
            if Ascii.eqb b quote_char then Some (tok, rest') else None
        | EmptyString => None
        end
      else None
  | EmptyString => None
  end.

Lemma quote_char_not_alnum : is_alnum quote_char = false.
Proof. reflexivity. Qed.

Lemma parse_qstring_unfold :
  forall h t,
    parse_qstring (String h t) =
      if Ascii.eqb h quote_char then
        let (tok, rest) := take_while is_alnum t in
        match rest with
        | String b rest' => if Ascii.eqb b quote_char then Some (tok, rest') else None
        | EmptyString => None
        end
      else None.
Proof. reflexivity. Qed.

Lemma append_quote_rest :
  forall x rest, (x ++ String quote_char EmptyString) ++ rest = x ++ String quote_char rest.
Proof.
  induction x as [| c x' IH]; intro rest; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma parse_qstring_print :
  forall x, is_valid_ident x = true ->
  forall rest, parse_qstring (quote_string x ++ rest) = Some (x, rest).
Proof.
  intros x Hvalid rest.
  assert (Hall : string_forallb is_alnum x = true).
  { unfold is_valid_ident in Hvalid. destruct x; [discriminate|exact Hvalid]. }
  unfold quote_string.
  rewrite (string_app_cons quote_char (x ++ String quote_char EmptyString) rest).
  rewrite parse_qstring_unfold.
  rewrite Ascii.eqb_refl.
  rewrite (append_quote_rest x rest).
  rewrite (take_while_app_stop is_alnum x Hall quote_char rest quote_char_not_alnum).
  rewrite Ascii.eqb_refl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** * Booleans *)

(** Printed as bare [true]/[false] tokens, matching real JSON's boolean
    literal syntax (unlike identifiers, which we quote, and numbers,
    which real JSON also leaves bare). *)
Definition bool_to_string (b : bool) : string := if b then "true" else "false".

Definition parse_bool (s : string) : option (bool * string) :=
  match expect "true" s with
  | Some rest => Some (true, rest)
  | None =>
      match expect "false" s with
      | Some rest => Some (false, rest)
      | None => None
      end
  end.

Lemma expect_true_false_mismatch :
  forall rest, expect "true" ("false" ++ rest) = None.
Proof. intro rest. reflexivity. Qed.

Lemma parse_bool_print :
  forall b rest, parse_bool (bool_to_string b ++ rest) = Some (b, rest).
Proof.
  intros b rest. destruct b; unfold parse_bool, bool_to_string.
  - rewrite expect_app. reflexivity.
  - rewrite expect_true_false_mismatch. rewrite expect_app. reflexivity.
Qed.

(** Keep [simpl]/[cbn] from peeking inside these during the round-trip
    proof below: we only ever want to reason about them through the
    already-proven [parse_number_print]/[parse_qstring_print]/
    [parse_bool_print] equations, uniformly across every constructor case,
    rather than have [simpl] eagerly (and inconsistently) inline some but
    not others depending on whether their first character happens to be
    syntactically concrete. *)
Opaque parse_number parse_qstring quote_string parse_bool parse_nat nat_to_string.

(* ----------------------------------------------------------------- *)
(** * Floats

    [PrimFloat.float] has no built-in decimal codec (unlike [Z], which
    [NilZero]/[DecimalZ] already give us an exact, proven round-trip
    through). Rather than invent a decimal-rounding scheme -- a genuinely
    hard problem (shortest round-tripping decimal representation of a
    binary float) that would need its own nontrivial proof -- this encodes
    a float exactly, with no rounding at all, through Coq's own
    [Prim2SF]/[SF2Prim] (Flocq-style [spec_float]: a sign bit, plus either
    "zero"/"infinity"/"nan" or a [(mantissa, exponent)] integer pair with
    value [(-1)^sign * mantissa * 2^exponent]). [spec_float] is a plain
    inductive built from bits we already know how to round-trip ([bool]
    via [parse_bool], [Z]/[positive] via [parse_number]), so serializing
    *it* needs no new numeric codec -- only [SF2Prim_Prim2SF] (a Coq
    standard-library axiom, same trust category as the Coq kernel itself;
    not something this project introduces) is needed to carry the
    [spec_float] round-trip back up to an actual [float] round-trip. *)

Lemma not_digit_rbrace : is_digit "}"%char = false.
Proof. reflexivity. Qed.

Lemma not_minus_rbrace : "}"%char <> minus_char.
Proof. discriminate. Qed.

Lemma not_digit_comma : is_digit ","%char = false.
Proof. reflexivity. Qed.

Lemma not_minus_comma : ","%char <> minus_char.
Proof. discriminate. Qed.

(** Every branch ends on a literal ["}"], matching the closing brace
    [print_expr]'s [EFConst] case leaves for it to supply -- see the
    comment on [spec_float_round_trip] for why that matters. *)
Definition spec_float_to_string (sf : spec_float) : string :=
  match sf with
  | S754_zero s =>
      """kind"":""zero"",""sign"":" ++ bool_to_string s ++ "}"
  | S754_infinity s =>
      """kind"":""inf"",""sign"":" ++ bool_to_string s ++ "}"
  | S754_nan =>
      """kind"":""nan""}"
  | S754_finite s m e =>
      """kind"":""finite"",""sign"":" ++ bool_to_string s
        ++ ",""mantissa"":" ++ z_to_string (Zpos m)
        ++ ",""exponent"":" ++ z_to_string e ++ "}"
  end.

Definition parse_spec_float (s : string) : option (spec_float * string) :=
  match expect """kind"":""zero"",""sign"":" s with
  | Some s1 =>
      match parse_bool s1 with
      | Some (b, s2) =>
          match expect "}" s2 with
          | Some s3 => Some (S754_zero b, s3)
          | None => None
          end
      | None => None
      end
  | None =>
  match expect """kind"":""inf"",""sign"":" s with
  | Some s1 =>
      match parse_bool s1 with
      | Some (b, s2) =>
          match expect "}" s2 with
          | Some s3 => Some (S754_infinity b, s3)
          | None => None
          end
      | None => None
      end
  | None =>
  match expect """kind"":""nan""}" s with
  | Some s1 => Some (S754_nan, s1)
  | None =>
  match expect """kind"":""finite"",""sign"":" s with
  | Some s1 =>
      match parse_bool s1 with
      | Some (b, s2) =>
          match expect ",""mantissa"":" s2 with
          | Some s3 =>
              match parse_number s3 with
              | Some (zm, s4) =>
                  match expect ",""exponent"":" s4 with
                  | Some s5 =>
                      match parse_number s5 with
                      | Some (ze, s6) =>
                          match expect "}" s6 with
                          | Some s7 => Some (S754_finite b (Z.to_pos zm) ze, s7)
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end end end end.

(** Purely structural: every [spec_float] round-trips through
    [spec_float_to_string]/[parse_spec_float], no side conditions (in
    particular, no [valid_binary sf] premise -- the mantissa field is
    already a [positive], so [Z.to_pos (Zpos m) = m] needs nothing beyond
    that). As with [parse_print_roundtrip] below, this only goes through
    because every field (including the last one in each branch) is
    immediately followed by a fixed literal character from the format
    itself -- here, a closing ["}"] -- rather than abutting the
    free/universally-quantified [rest] directly; [parse_number_print]
    needs that literal character to know where a digit run ends. *)
Lemma spec_float_round_trip :
  forall sf rest, parse_spec_float (spec_float_to_string sf ++ rest) = Some (sf, rest).
Proof.
  intros sf rest.
  unfold parse_spec_float, spec_float_to_string.
  destruct sf as [s|s| |s m e].
  - (* S754_zero *)
    repeat rewrite string_append_assoc. simpl.
    rewrite (parse_bool_print s (String "}"%char rest)). reflexivity.
  - (* S754_infinity *)
    repeat rewrite string_append_assoc. simpl.
    rewrite (parse_bool_print s (String "}"%char rest)). reflexivity.
  - (* S754_nan *)
    reflexivity.
  - (* S754_finite *)
    repeat rewrite string_append_assoc. simpl.
    rewrite (parse_bool_print s _). simpl.
    rewrite (parse_number_print (Zpos m) ","%char _ not_digit_comma not_minus_comma). simpl.
    rewrite (parse_number_print e "}"%char rest not_digit_rbrace not_minus_rbrace). simpl.
    reflexivity.
Qed.

(** Keep [simpl]/[cbn] from peeking inside these during the main
    round-trip theorem below, same reasoning as the [Opaque] block above
    for [parse_number]/[parse_qstring]/[parse_bool]. *)
Opaque parse_spec_float spec_float_to_string.

(* ----------------------------------------------------------------- *)
(** * The [expr] codec itself *)


Fixpoint print_expr (e : expr) : string :=
  match e with
  | EConst z =>
      "{""tag"":""const"",""value"":" ++ z_to_string z ++ "}"
  | EBool b =>
      "{""tag"":""bool"",""value"":" ++ bool_to_string b ++ "}"
  | EVar x =>
      "{""tag"":""var"",""name"":" ++ quote_string x ++ "}"
  | EAdd e1 e2 =>
      "{""tag"":""add"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ESub e1 e2 =>
      "{""tag"":""sub"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EMul e1 e2 =>
      "{""tag"":""mul"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EEq e1 e2 =>
      "{""tag"":""eq"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ELt e1 e2 =>
      "{""tag"":""lt"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ELe e1 e2 =>
      "{""tag"":""le"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EAnd e1 e2 =>
      "{""tag"":""and"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EOr e1 e2 =>
      "{""tag"":""or"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ENot e1 =>
      "{""tag"":""not"",""value"":" ++ print_expr e1 ++ "}"
  | EIf c e1 e2 =>
      "{""tag"":""if"",""cond"":" ++ print_expr c
        ++ ",""then"":" ++ print_expr e1 ++ ",""else"":" ++ print_expr e2 ++ "}"
  | EPair e1 e2 =>
      "{""tag"":""pair"",""fst"":" ++ print_expr e1 ++ ",""snd"":" ++ print_expr e2 ++ "}"
  | EFst e1 =>
      "{""tag"":""fst"",""value"":" ++ print_expr e1 ++ "}"
  | ESnd e1 =>
      "{""tag"":""snd"",""value"":" ++ print_expr e1 ++ "}"
  | ELet x e1 e2 =>
      "{""tag"":""let"",""name"":" ++ quote_string x
        ++ ",""value"":" ++ print_expr e1 ++ ",""body"":" ++ print_expr e2 ++ "}"
  | EFConst f =>
      (** No extra ["}"] here -- [spec_float_to_string] already supplies
          the closing brace (see its comment for why that's load-bearing
          for the round-trip proof). *)
      "{""tag"":""fconst""," ++ spec_float_to_string (Prim2SF f)
  | EFAdd e1 e2 =>
      "{""tag"":""fadd"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EFSub e1 e2 =>
      "{""tag"":""fsub"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EFMul e1 e2 =>
      "{""tag"":""fmul"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EFDiv e1 e2 =>
      "{""tag"":""fdiv"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EFEq e1 e2 =>
      "{""tag"":""feq"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EFLt e1 e2 =>
      "{""tag"":""flt"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EFLe e1 e2 =>
      "{""tag"":""fle"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ERepeat n x body init =>
      "{""tag"":""repeat"",""count"":" ++ nat_to_string n
        ++ ",""name"":" ++ quote_string x
        ++ ",""body"":" ++ print_expr body ++ ",""init"":" ++ print_expr init ++ "}"
  | EDiv e1 e2 =>
      "{""tag"":""div"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EMod e1 e2 =>
      "{""tag"":""mod"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ELam param body =>
      "{""tag"":""lam"",""param"":" ++ quote_string param ++ ",""body"":" ++ print_expr body ++ "}"
  | ERec f param body =>
      "{""tag"":""rec"",""name"":" ++ quote_string f
        ++ ",""param"":" ++ quote_string param ++ ",""body"":" ++ print_expr body ++ "}"
  | ERecMut f1 param1 body1 f2 param2 body2 =>
      "{""tag"":""recmut"",""name1"":" ++ quote_string f1
        ++ ",""param1"":" ++ quote_string param1 ++ ",""body1"":" ++ print_expr body1
        ++ ",""name2"":" ++ quote_string f2
        ++ ",""param2"":" ++ quote_string param2 ++ ",""body2"":" ++ print_expr body2 ++ "}"
  | EApp func arg =>
      "{""tag"":""app"",""func"":" ++ print_expr func ++ ",""arg"":" ++ print_expr arg ++ "}"
  | ENil => "{""tag"":""nil""}"
  | ECons hd tl =>
      "{""tag"":""cons"",""hd"":" ++ print_expr hd ++ ",""tl"":" ++ print_expr tl ++ "}"
  | EListMatch scrutinee nilcase hd tl conscase =>
      "{""tag"":""listmatch"",""scrutinee"":" ++ print_expr scrutinee
        ++ ",""nilcase"":" ++ print_expr nilcase
        ++ ",""hd"":" ++ quote_string hd ++ ",""tl"":" ++ quote_string tl
        ++ ",""conscase"":" ++ print_expr conscase ++ "}"
  | ERecord k1 e1 k2 e2 =>
      "{""tag"":""record"",""key1"":" ++ quote_string k1 ++ ",""value1"":" ++ print_expr e1
        ++ ",""key2"":" ++ quote_string k2 ++ ",""value2"":" ++ print_expr e2 ++ "}"
  | EField name e1 =>
      "{""tag"":""field"",""name"":" ++ quote_string name ++ ",""value"":" ++ print_expr e1 ++ "}"
  | EInl e1 => "{""tag"":""inl"",""value"":" ++ print_expr e1 ++ "}"
  | EInr e1 => "{""tag"":""inr"",""value"":" ++ print_expr e1 ++ "}"
  | ECase scrutinee x1 case1 x2 case2 =>
      "{""tag"":""case"",""scrutinee"":" ++ print_expr scrutinee
        ++ ",""x1"":" ++ quote_string x1 ++ ",""case1"":" ++ print_expr case1
        ++ ",""x2"":" ++ quote_string x2 ++ ",""case2"":" ++ print_expr case2 ++ "}"
  | EStrConst s => "{""tag"":""strconst"",""value"":" ++ quote_string s ++ "}"
  | EStrConcat e1 e2 =>
      "{""tag"":""strconcat"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EStrEq e1 e2 =>
      "{""tag"":""streq"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ERecordN fields =>
      "{""tag"":""recordn"",""fields"":[" ++
      (fix print_fields (fs : list (var * expr)) : string :=
         match fs with
         | [] => ""
         | [(k, fe)] =>
             "{""key"":" ++ quote_string k ++ ",""value"":" ++ print_expr fe ++ "}"
         | (k, fe) :: rest =>
             "{""key"":" ++ quote_string k ++ ",""value"":" ++ print_expr fe ++ "},"
               ++ print_fields rest
         end) fields
      ++ "]}"
  | EFieldN name e1 =>
      "{""tag"":""fieldn"",""name"":" ++ quote_string name ++ ",""value"":" ++ print_expr e1 ++ "}"
  end.

(** Note: this [expr_fuel] is this module's own parser-recursion-depth
    bound (how deep [parse_expr] needs to descend through nested JSON
    text) -- a different, unrelated concept from [Lang.eval]'s evaluation
    fuel (how many function-application steps [eval] may take), despite
    the name collision. One is about parsing a fixed piece of text; the
    other is about a potentially-nonterminating computation. *)
Fixpoint expr_fuel (e : expr) : nat :=
  match e with
  | EConst _ | EBool _ | EVar _ | EFConst _ => 1
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2
  | EEq e1 e2 | ELt e1 e2 | ELe e1 e2
  | EAnd e1 e2 | EOr e1 e2 | EPair e1 e2 => S (Nat.max (expr_fuel e1) (expr_fuel e2))
  | ENot e1 | EFst e1 | ESnd e1 => S (expr_fuel e1)
  | EIf c e1 e2 => S (Nat.max (expr_fuel c) (Nat.max (expr_fuel e1) (expr_fuel e2)))
  | ELet _ e1 e2 => S (Nat.max (expr_fuel e1) (expr_fuel e2))
  | EFAdd e1 e2 | EFSub e1 e2 | EFMul e1 e2 | EFDiv e1 e2
  | EFEq e1 e2 | EFLt e1 e2 | EFLe e1 e2
  | EDiv e1 e2 | EMod e1 e2 | EApp e1 e2 =>
      S (Nat.max (expr_fuel e1) (expr_fuel e2))
  | ERepeat _ _ body init => S (Nat.max (expr_fuel body) (expr_fuel init))
  | ELam _ body => S (expr_fuel body)
  | ERec _ _ body => S (expr_fuel body)
  | ERecMut _ _ body1 _ _ body2 => S (Nat.max (expr_fuel body1) (expr_fuel body2))
  | ENil => 1
  | ECons hd tl => S (Nat.max (expr_fuel hd) (expr_fuel tl))
  | EListMatch scrutinee nilcase _ _ conscase =>
      S (Nat.max (expr_fuel scrutinee) (Nat.max (expr_fuel nilcase) (expr_fuel conscase)))
  | ERecord _ e1 _ e2 => S (Nat.max (expr_fuel e1) (expr_fuel e2))
  | EField _ e1 => S (expr_fuel e1)
  | EInl e1 => S (expr_fuel e1)
  | EInr e1 => S (expr_fuel e1)
  | ECase scrutinee _ case1 _ case2 =>
      S (Nat.max (expr_fuel scrutinee) (Nat.max (expr_fuel case1) (expr_fuel case2)))
  | EStrConst _ => 1
  | EStrConcat e1 e2 | EStrEq e1 e2 => S (Nat.max (expr_fuel e1) (expr_fuel e2))
  | ERecordN fields =>
      S (length fields + fold_right (fun kf acc => Nat.max (expr_fuel (snd kf)) acc) O fields)
  | EFieldN _ e1 => S (expr_fuel e1)
  end.

(** Dispatch on the full fixed literal prefix of each constructor's
    printed form directly, trying each in turn, rather than reading the
    "tag" field generically and comparing strings -- see the comment on
    the original (smaller) version of this function for why. *)
Fixpoint parse_expr (fuel : nat) (s : string) : option (expr * string) :=
  match fuel with
  | O => None
  | S fuel' =>
    match expect "{""tag"":""const"",""value"":" s with
    | Some s1 =>
        match parse_number s1 with
        | Some (z, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (EConst z, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""bool"",""value"":" s with
    | Some s1 =>
        match parse_bool s1 with
        | Some (b, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (EBool b, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""var"",""name"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (x, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (EVar x, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""add"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EAdd e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""sub"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (ESub e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""mul"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EMul e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""eq"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EEq e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""lt"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (ELt e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""le"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (ELe e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""and"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EAnd e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""or"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EOr e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""not"",""value"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (ENot e1, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""if"",""cond"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (c, s2) =>
            match expect ",""then"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e1, s4) =>
                    match expect ",""else"":" s4 with
                    | Some s5 =>
                        match parse_expr fuel' s5 with
                        | Some (e2, s6) =>
                            match expect "}" s6 with
                            | Some s7 => Some (EIf c e1 e2, s7)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""pair"",""fst"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""snd"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EPair e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""fst"",""value"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (EFst e1, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""snd"",""value"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (ESnd e1, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""let"",""name"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (x, s2) =>
            match expect ",""value"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e1, s4) =>
                    match expect ",""body"":" s4 with
                    | Some s5 =>
                        match parse_expr fuel' s5 with
                        | Some (e2, s6) =>
                            match expect "}" s6 with
                            | Some s7 => Some (ELet x e1 e2, s7)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""fconst""," s with
    | Some s1 =>
        match parse_spec_float s1 with
        | Some (sf, s2) => Some (EFConst (SF2Prim sf), s2)
        | None => None
        end
    | None =>
    match expect "{""tag"":""fadd"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFAdd e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""fsub"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFSub e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""fmul"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFMul e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""fdiv"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFDiv e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""feq"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFEq e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""flt"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFLt e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""fle"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFLe e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""repeat"",""count"":" s with
    | Some s1 =>
        match parse_nat s1 with
        | Some (n, s2) =>
            match expect ",""name"":" s2 with
            | Some s3 =>
                match parse_qstring s3 with
                | Some (x, s4) =>
                    match expect ",""body"":" s4 with
                    | Some s5 =>
                        match parse_expr fuel' s5 with
                        | Some (body, s6) =>
                            match expect ",""init"":" s6 with
                            | Some s7 =>
                                match parse_expr fuel' s7 with
                                | Some (init, s8) =>
                    match expect "}" s8 with
                                    | Some s9 => Some (ERepeat n x body init, s9)
                                    | None => None
                                    end
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""div"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EDiv e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""mod"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EMod e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""lam"",""param"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (param, s2) =>
            match expect ",""body"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (body, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (ELam param body, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""rec"",""name"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (f, s2) =>
            match expect ",""param"":" s2 with
            | Some s3 =>
                match parse_qstring s3 with
                | Some (param, s4) =>
                    match expect ",""body"":" s4 with
                    | Some s5 =>
                        match parse_expr fuel' s5 with
                        | Some (body, s6) =>
                            match expect "}" s6 with
                            | Some s7 => Some (ERec f param body, s7)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""recmut"",""name1"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (f1, s2) =>
            match expect ",""param1"":" s2 with
            | Some s3 =>
                match parse_qstring s3 with
                | Some (param1, s4) =>
                    match expect ",""body1"":" s4 with
                    | Some s5 =>
                        match parse_expr fuel' s5 with
                        | Some (body1, s6) =>
                            match expect ",""name2"":" s6 with
                            | Some s7 =>
                                match parse_qstring s7 with
                                | Some (f2, s8) =>
                                    match expect ",""param2"":" s8 with
                                    | Some s9 =>
                                        match parse_qstring s9 with
                                        | Some (param2, s10) =>
                                            match expect ",""body2"":" s10 with
                                            | Some s11 =>
                                                match parse_expr fuel' s11 with
                                                | Some (body2, s12) =>
                                                    match expect "}" s12 with
                                                    | Some s13 => Some (ERecMut f1 param1 body1 f2 param2 body2, s13)
                                                    | None => None
                                                    end
                                                | None => None
                                                end
                                            | None => None
                                            end
                                        | None => None
                                        end
                                    | None => None
                                    end
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""app"",""func"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (func, s2) =>
            match expect ",""arg"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (arg, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EApp func arg, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""nil""}" s with
    | Some s1 => Some (ENil, s1)
    | None =>
    match expect "{""tag"":""cons"",""hd"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (hd, s2) =>
            match expect ",""tl"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (tl, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (ECons hd tl, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""listmatch"",""scrutinee"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (scrutinee, s2) =>
            match expect ",""nilcase"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (nilcase, s4) =>
                    match expect ",""hd"":" s4 with
                    | Some s5 =>
                        match parse_qstring s5 with
                        | Some (hd, s6) =>
                            match expect ",""tl"":" s6 with
                            | Some s7 =>
                                match parse_qstring s7 with
                                | Some (tl, s8) =>
                                    match expect ",""conscase"":" s8 with
                                    | Some s9 =>
                                        match parse_expr fuel' s9 with
                                        | Some (conscase, s10) =>
                                            match expect "}" s10 with
                                            | Some s11 => Some (EListMatch scrutinee nilcase hd tl conscase, s11)
                                            | None => None
                                            end
                                        | None => None
                                        end
                                    | None => None
                                    end
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""record"",""key1"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (k1, s2) =>
            match expect ",""value1"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e1, s4) =>
                    match expect ",""key2"":" s4 with
                    | Some s5 =>
                        match parse_qstring s5 with
                        | Some (k2, s6) =>
                            match expect ",""value2"":" s6 with
                            | Some s7 =>
                                match parse_expr fuel' s7 with
                                | Some (e2, s8) =>
                                    match expect "}" s8 with
                                    | Some s9 => Some (ERecord k1 e1 k2 e2, s9)
                                    | None => None
                                    end
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""field"",""name"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (name, s2) =>
            match expect ",""value"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e1, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EField name e1, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""inl"",""value"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (EInl e1, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""inr"",""value"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (EInr e1, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""case"",""scrutinee"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (scrutinee, s2) =>
            match expect ",""x1"":" s2 with
            | Some s3 =>
                match parse_qstring s3 with
                | Some (x1, s4) =>
                    match expect ",""case1"":" s4 with
                    | Some s5 =>
                        match parse_expr fuel' s5 with
                        | Some (case1, s6) =>
                            match expect ",""x2"":" s6 with
                            | Some s7 =>
                                match parse_qstring s7 with
                                | Some (x2, s8) =>
                                    match expect ",""case2"":" s8 with
                                    | Some s9 =>
                                        match parse_expr fuel' s9 with
                                        | Some (case2, s10) =>
                                            match expect "}" s10 with
                                            | Some s11 => Some (ECase scrutinee x1 case1 x2 case2, s11)
                                            | None => None
                                            end
                                        | None => None
                                        end
                                    | None => None
                                    end
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""strconst"",""value"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (sval, s2) =>
            match expect "}" s2 with
            | Some s3 => Some (EStrConst sval, s3)
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""strconcat"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EStrConcat e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""streq"",""lhs"":" s with
    | Some s1 =>
        match parse_expr fuel' s1 with
        | Some (e1, s2) =>
            match expect ",""rhs"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e2, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EStrEq e1 e2, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None =>
    match expect "{""tag"":""recordn"",""fields"":[" s with
    | Some s1 =>
        match expect "]}" s1 with
        | Some s2 => Some (ERecordN [], s2)
        | None =>
            match (fix parse_fields (fuel : nat) (ss : string) : option (list (var * expr) * string) :=
                     match fuel with
                     | O => None
                     | S fuel'0 =>
                         match expect "{""key"":" ss with
                         | Some ss1 =>
                             match parse_qstring ss1 with
                             | Some (k, ss2) =>
                                 match expect ",""value"":" ss2 with
                                 | Some ss3 =>
                                     match parse_expr fuel'0 ss3 with
                                     | Some (fe, ss4) =>
                                         match expect "}" ss4 with
                                         | Some ss5 =>
                                             match expect "," ss5 with
                                             | Some ss6 =>
                                                 match parse_fields fuel'0 ss6 with
                                                 | Some (rest, ss7) => Some ((k, fe) :: rest, ss7)
                                                 | None => None
                                                 end
                                             | None => Some ([(k, fe)], ss5)
                                             end
                                         | None => None
                                         end
                                     | None => None
                                     end
                                 | None => None
                                 end
                             | None => None
                             end
                         | None => None
                         end
                     end) fuel' s1
            with
            | Some (fields, s2) =>
                match expect "]}" s2 with
                | Some s3 => Some (ERecordN fields, s3)
                | None => None
                end
            | None => None
            end
        end
    | None =>
    match expect "{""tag"":""fieldn"",""name"":" s with
    | Some s1 =>
        match parse_qstring s1 with
        | Some (name, s2) =>
            match expect ",""value"":" s2 with
            | Some s3 =>
                match parse_expr fuel' s3 with
                | Some (e1, s4) =>
                    match expect "}" s4 with
                    | Some s5 => Some (EFieldN name e1, s5)
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None => None
    end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end
  end.

Definition parse_expr_top (s : string) : option (expr * string) :=
  parse_expr (String.length s + 1) s.

(** The headline theorem: for every [expr] with valid identifiers, printing
    it and parsing the result back (with enough fuel, any amount at least
    [expr_fuel e]) recovers exactly the original term and consumes exactly
    the printed text, leaving [rest] untouched. This is the "parser is a
    proven inverse of our own grammar" correctness statement discussed in
    GOAL.md.

    Proved by *strong induction on [expr_fuel e]* ([well_founded_induction
    lt_wf], via the [Hstrong] helper below), not structural induction on
    [e] -- this is new as of this proof (it used to be [induction e as
    [...]]), and the reason for the switch is exactly the obstacle
    docs/roadmap.md's N-field-record/mutual-recursion entries describe:
    structural induction on [e] gives no usable hypothesis for a
    sub-[expr] buried inside a [list expr]-shaped field, since Coq's
    auto-derived scheme has no clause connecting a list field's elements
    back to the goal. Strong induction on the *fuel*, not on [e]'s shape,
    sidesteps this entirely: the hypothesis [IHn] becomes a blanket fact
    over *any* [expr] with smaller fuel, usable for a list field's
    elements exactly the same way it's used for an ordinary sub-[expr] --
    confirmed directly in an isolated prototype before this file was
    touched (see docs/roadmap.md), then applied here mechanically (every
    former [IHk Hv fuel' Hf]-style call becomes [(IHn (expr_fuel ek) Hltk
    ek (le_n _)) Hv fuel' Hf], with each [Hltk] asserted from [Hn] by
    [lia]) across every existing case -- a refactor, not a new feature;
    no case's own reasoning changed, only how its induction hypothesis is
    obtained. This is the same fuel-not-shape trick [Translate.v]'s own
    proof already uses to get past [EApp]'s non-structural recursion into
    a closure, just applied here to get past a different non-structural
    shape (a list field) instead. *)

(** [ERecordN]/[EFieldN]'s own helper, mirroring [Translate.v]'s
    [eval_fields_translate_correct]: the array-of-fields structure is
    reasoned about by plain [induction] on the (non-empty) field list
    itself, *not* by [parse_print_roundtrip]'s own strong induction on
    [expr_fuel] -- the two inductions are independent, this one needs
    nothing from [n]/[IHn] beyond a per-field roundtrip fact handed in
    as a hypothesis. Validated first in an isolated prototype (see
    docs/roadmap.md) before being applied here verbatim. *)
Fixpoint fields_fuel (fields : list (var * expr)) : nat :=
  match fields with
  | [] => O
  | (_, fe) :: rest => S (Nat.max (expr_fuel fe) (fields_fuel rest))
  end.

(** [fields_fuel]'s own recursion charges one extra unit of fuel per
    field (it is the parser's own recursion-depth bound), while
    [expr_fuel]'s [ERecordN] case charges a flat [length + max]
    instead -- the two formulas are not equal (e.g. at [a = 5],
    [L = 3], [F = 1]: [max a (L + F) = 5] but [L + max a F = 8]), only
    [fields_fuel]-is-no-bigger, which is all a fuel *bound* ever needs. *)
Lemma fields_fuel_le_len_fold :
  forall fs, (fields_fuel fs <=
    length fs + fold_right (fun kf acc => Nat.max (expr_fuel (snd kf)) acc) O fs)%nat.
Proof.
  induction fs as [| [k fe] fs' IH]; simpl.
  - lia.
  - apply le_n_S.
    rewrite <- Nat.add_max_distr_l.
    apply Nat.max_le_compat; [lia | exact IH].
Qed.

Lemma print_parse_fieldsN_roundtrip :
  forall k fe fields'
    (Hvk : is_valid_ident k = true)
    (Hvfe : expr_idents_valid is_valid_ident fe = true)
    (Hbody : forall fuel, (expr_fuel fe <= fuel)%nat ->
               forall rest, parse_expr fuel (print_expr fe ++ rest) = Some (fe, rest))
    (Hall : Forall (fun kf => is_valid_ident (fst kf) = true /\
                     expr_idents_valid is_valid_ident (snd kf) = true /\
                     forall fuel, (expr_fuel (snd kf) <= fuel)%nat ->
                       forall rest, parse_expr fuel (print_expr (snd kf) ++ rest) = Some (snd kf, rest))
                   fields')
    fuel,
    (fields_fuel ((k, fe) :: fields') <= fuel)%nat ->
    forall rest,
      (fix parse_fields (fuel0 : nat) (ss : string) : option (list (var * expr) * string) :=
         match fuel0 with
         | O => None
         | S fuel0' =>
             match expect "{""key"":" ss with
             | Some ss1 =>
                 match parse_qstring ss1 with
                 | Some (k0, ss2) =>
                     match expect ",""value"":" ss2 with
                     | Some ss3 =>
                         match parse_expr fuel0' ss3 with
                         | Some (fe0, ss4) =>
                             match expect "}" ss4 with
                             | Some ss5 =>
                                 match expect "," ss5 with
                                 | Some ss6 =>
                                     match parse_fields fuel0' ss6 with
                                     | Some (rest0, ss7) => Some ((k0, fe0) :: rest0, ss7)
                                     | None => None
                                     end
                                 | None => Some ([(k0, fe0)], ss5)
                                 end
                             | None => None
                             end
                         | None => None
                         end
                     | None => None
                     end
                 | None => None
                 end
             | None => None
             end
         end) fuel
        ((fix print_fields (fs : list (var * expr)) : string :=
            match fs with
            | [] => ""
            | [(k0, fe0)] =>
                "{""key"":" ++ quote_string k0 ++ ",""value"":" ++ print_expr fe0 ++ "}"
            | (k0, fe0) :: rest0 =>
                "{""key"":" ++ quote_string k0 ++ ",""value"":" ++ print_expr fe0 ++ "},"
                  ++ print_fields rest0
            end) ((k, fe) :: fields') ++ "]" ++ rest)
      = Some ((k, fe) :: fields', "]" ++ rest).
Proof.
  intros k fe fields'. revert k fe.
  induction fields' as [| [k2 fe2] fields'' IH]; intros k fe Hvk Hvfe Hbody Hall fuel Hfuel rest.
  - (* singleton: [(k, fe)] *)
    simpl in Hfuel. destruct fuel as [|fuel']; [lia|]. simpl in Hfuel.
    assert (Hone : (expr_fuel fe <= fuel')%nat) by lia.
    simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print k Hvk). simpl.
    repeat rewrite string_append_assoc.
    simpl.
    repeat rewrite string_append_assoc.
    rewrite (Hbody fuel' Hone).
    simpl.
    destruct (expect "," ("]" ++ rest)) eqn:Hcomma.
    + unfold expect in Hcomma. simpl in Hcomma. discriminate.
    + reflexivity.
  - (* cons: [(k, fe) :: (k2, fe2) :: fields'']; the tail is itself a
       non-empty list, so [IH] (specialized to [k2]/[fe2]/[fields'']
       directly) applies unchanged. *)
    simpl in Hfuel. destruct fuel as [|fuel']; [lia|]. simpl in Hfuel.
    assert (Hone : (expr_fuel fe <= fuel')%nat) by lia.
    pose proof (Nat.le_max_r (expr_fuel fe) (S (Nat.max (expr_fuel fe2) (fields_fuel fields'')))) as Hmax.
    assert (Hfuel' : (fields_fuel ((k2, fe2) :: fields'') <= fuel')%nat) by (simpl; lia).
    inversion Hall as [| x l Hx Hl]; subst.
    destruct Hx as [Hvk2 [Hvfe2 Hbody2]].
    simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print k Hvk). simpl.
    repeat rewrite string_append_assoc.
    simpl.
    repeat rewrite string_append_assoc.
    rewrite (Hbody fuel' Hone).
    simpl.
    repeat rewrite string_append_assoc.
    pose proof (IH k2 fe2 Hvk2 Hvfe2 Hbody2 Hl fuel' Hfuel' rest) as IH'.
    simpl in IH'.
    rewrite IH'.
    reflexivity.
Qed.

Theorem parse_print_roundtrip :
  forall e,
    expr_idents_valid is_valid_ident e = true ->
    forall fuel, (expr_fuel e <= fuel)%nat ->
    forall rest, parse_expr fuel (print_expr e ++ rest) = Some (e, rest).
Proof.
  assert (Hstrong : forall n e,
    (expr_fuel e <= n)%nat ->
    expr_idents_valid is_valid_ident e = true ->
    forall fuel, (expr_fuel e <= fuel)%nat ->
    forall rest, parse_expr fuel (print_expr e ++ rest) = Some (e, rest)).
  {
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros e Hn Hvalid fuel Hfuel rest.
  destruct e as
      [ z                     (* EConst *)
      | b                     (* EBool *)
      | x                     (* EVar *)
      | e1 e2                 (* EAdd *)
      | e1 e2                 (* ESub *)
      | e1 e2                 (* EMul *)
      | e1 e2                 (* EEq *)
      | e1 e2                 (* ELt *)
      | e1 e2                 (* ELe *)
      | e1 e2                 (* EAnd *)
      | e1 e2                 (* EOr *)
      | e1                    (* ENot *)
      | c e1 e2               (* EIf *)
      | e1 e2                 (* EPair *)
      | e1                    (* EFst *)
      | e1                    (* ESnd *)
      | x e1 e2               (* ELet *)
      | f                     (* EFConst *)
      | e1 e2                 (* EFAdd *)
      | e1 e2                 (* EFSub *)
      | e1 e2                 (* EFMul *)
      | e1 e2                 (* EFDiv *)
      | e1 e2                 (* EFEq *)
      | e1 e2                 (* EFLt *)
      | e1 e2                 (* EFLe *)
      | rep_n x body init     (* ERepeat *)
      | e1 e2                 (* EDiv *)
      | e1 e2                 (* EMod *)
      | param body            (* ELam *)
      | f param body          (* ERec *)
      | f1 param1 body1 f2 param2 body2 (* ERecMut *)
      | func arg              (* EApp *)
      |                       (* ENil *)
      | hd tl                 (* ECons *)
      | scrutinee nilcase hd tl conscase (* EListMatch *)
      | k1 e1 k2 e2           (* ERecord *)
      | name e1               (* EField *)
      | e1                    (* EInl *)
      | e1                    (* EInr *)
      | scrutinee x1 case1 x2 case2 (* ECase *)
      | s                     (* EStrConst *)
      | e1 e2                 (* EStrConcat *)
      | e1 e2                 (* EStrEq *)
      | fields                (* ERecordN *)
      | name e1 ];            (* EFieldN *)
  destruct fuel as [| fuel']; simpl in Hfuel; try lia;
  simpl.
  - (* EConst *)
    simpl in Hn.
    rewrite string_append_assoc. simpl.
    rewrite (parse_number_print z "}"%char rest not_digit_rbrace not_minus_rbrace).
    reflexivity.
  - (* EBool *)
    simpl in Hn.
    rewrite string_append_assoc. simpl.
    rewrite (parse_bool_print b (String "}"%char rest)).
    reflexivity.
  - (* EVar *)
    simpl in Hn.
    simpl in Hvalid.
    rewrite string_append_assoc. simpl.
    rewrite (parse_qstring_print x Hvalid (String "}"%char rest)).
    reflexivity.
  - (* EAdd *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ESub *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EMul *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EEq *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ELt *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ELe *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EAnd *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EOr *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ENot *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hvalid fuel' Hf1). reflexivity.
  - (* EIf *)
    simpl in Hn.
    assert (Hltc : (expr_fuel c < n)%nat) by lia.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hvc Hv12].
    apply andb_true_iff in Hv12 as [Hv1 Hv2].
    assert (Hfc : (expr_fuel c <= fuel')%nat) by lia.
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel c) Hltc c (le_n _)) Hvc fuel' Hfc). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EPair *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFst *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hvalid fuel' Hf1). reflexivity.
  - (* ESnd *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hvalid fuel' Hf1). reflexivity.
  - (* ELet *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hvx Hv12].
    apply andb_true_iff in Hv12 as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print x Hvx). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFConst *)
    simpl in Hn.
    rewrite (spec_float_round_trip (Prim2SF f) rest).
    rewrite SF2Prim_Prim2SF. reflexivity.
  - (* EFAdd *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFSub *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFMul *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFDiv *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFEq *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFLt *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EFLe *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ERepeat *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel body < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel init < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hvx Hv12].
    apply andb_true_iff in Hv12 as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel body <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel init <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc. simpl.
    rewrite (parse_nat_print rep_n ","%char _ not_digit_comma not_minus_comma). simpl.
    repeat rewrite string_append_assoc. simpl.
    rewrite (parse_qstring_print x Hvx). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel body) Hlt1 body (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel init) Hlt2 init (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EDiv *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EMod *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ELam *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel body < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hvp Hv1].
    assert (Hf1 : (expr_fuel body <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print param Hvp). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel body) Hlt1 body (le_n _)) Hv1 fuel' Hf1). reflexivity.
  - (* ERec *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel body < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hvf Hv12].
    apply andb_true_iff in Hv12 as [Hvp Hv1].
    assert (Hf1 : (expr_fuel body <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print f Hvf). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print param Hvp). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel body) Hlt1 body (le_n _)) Hv1 fuel' Hf1). reflexivity.
  - (* ERecMut *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel body1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel body2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hvf1 Hrest1].
    apply andb_true_iff in Hrest1 as [Hvp1 Hrest2].
    apply andb_true_iff in Hrest2 as [Hv1 Hrest3].
    apply andb_true_iff in Hrest3 as [Hvf2 Hrest4].
    apply andb_true_iff in Hrest4 as [Hvp2 Hv2].
    assert (Hf1 : (expr_fuel body1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel body2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print f1 Hvf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print param1 Hvp1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel body1) Hlt1 body1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print f2 Hvf2). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print param2 Hvp2). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel body2) Hlt2 body2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EApp *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel func < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel arg < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel func <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel arg <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel func) Hlt1 func (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel arg) Hlt2 arg (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ENil *)
    simpl in Hn.
reflexivity.
  - (* ECons *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel hd < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel tl < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel hd <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel tl <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel hd) Hlt1 hd (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel tl) Hlt2 tl (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EListMatch *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel scrutinee < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel nilcase < n)%nat) by lia.
    assert (Hlt3 : (expr_fuel conscase < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hrest1].
    apply andb_true_iff in Hrest1 as [Hv2 Hrest2].
    apply andb_true_iff in Hrest2 as [Hvhd Hrest3].
    apply andb_true_iff in Hrest3 as [Hvtl Hv3].
    assert (Hf1 : (expr_fuel scrutinee <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel nilcase <= fuel')%nat) by lia.
    assert (Hf3 : (expr_fuel conscase <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel scrutinee) Hlt1 scrutinee (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel nilcase) Hlt2 nilcase (le_n _)) Hv2 fuel' Hf2). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print hd Hvhd). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print tl Hvtl). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel conscase) Hlt3 conscase (le_n _)) Hv3 fuel' Hf3). reflexivity.
  - (* ERecord *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hk1 Hrest1].
    apply andb_true_iff in Hrest1 as [Hv1 Hrest2].
    apply andb_true_iff in Hrest2 as [Hk2 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print k1 Hk1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print k2 Hk2). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EField *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hname Hv1].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print name Hname). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). reflexivity.
  - (* EInl *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hvalid fuel' Hf1). reflexivity.
  - (* EInr *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hvalid fuel' Hf1). reflexivity.
  - (* ECase *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel scrutinee < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel case1 < n)%nat) by lia.
    assert (Hlt3 : (expr_fuel case2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hrest1].
    apply andb_true_iff in Hrest1 as [Hvx1 Hrest2].
    apply andb_true_iff in Hrest2 as [Hv2 Hrest3].
    apply andb_true_iff in Hrest3 as [Hvx2 Hv3].
    assert (Hf1 : (expr_fuel scrutinee <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel case1 <= fuel')%nat) by lia.
    assert (Hf3 : (expr_fuel case2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel scrutinee) Hlt1 scrutinee (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print x1 Hvx1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel case1) Hlt2 case1 (le_n _)) Hv2 fuel' Hf2). simpl.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print x2 Hvx2). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel case2) Hlt3 case2 (le_n _)) Hv3 fuel' Hf3). reflexivity.
  - (* EStrConst *)
    simpl in Hn.
    simpl in Hvalid.
    rewrite string_append_assoc. simpl.
    rewrite (parse_qstring_print s Hvalid (String "}"%char rest)).
    reflexivity.
  - (* EStrConcat *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* EStrEq *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    assert (Hlt2 : (expr_fuel e2 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e2) Hlt2 e2 (le_n _)) Hv2 fuel' Hf2). reflexivity.
  - (* ERecordN *)
    simpl in Hn.
    destruct fields as [| [k fe] fields'].
    + simpl. reflexivity.
    + simpl in Hn.
      simpl in Hfuel.
      simpl in Hvalid.
      apply andb_true_iff in Hvalid as [Hvk0 Hvrest].
      apply andb_true_iff in Hvk0 as [Hvk Hvfe].
      assert (Hone : (expr_fuel fe < n)%nat).
      { pose proof (Nat.le_max_l (expr_fuel fe)
                      (fold_right (fun kf acc => Nat.max (expr_fuel (snd kf)) acc) O fields')) as Hmax.
        lia. }
      assert (Hall : Forall (fun kf => is_valid_ident (fst kf) = true /\
                       expr_idents_valid is_valid_ident (snd kf) = true /\
                       forall fuel0, (expr_fuel (snd kf) <= fuel0)%nat ->
                         forall rest0, parse_expr fuel0 (print_expr (snd kf) ++ rest0) = Some (snd kf, rest0))
                     fields').
      { apply Forall_forall. intros [k0 fe0] Hin.
        pose proof Hvrest as Hvrest0.
        apply forallb_forall with (x := (k0, fe0)) in Hvrest0; [| exact Hin].
        apply andb_true_iff in Hvrest0 as [Hvk0 Hvfe0].
        assert (Hlt0 : (expr_fuel fe0 < n)%nat).
        { assert (Hle : (expr_fuel fe0 <= fold_right (fun kf acc => Nat.max (expr_fuel (snd kf)) acc) O fields')%nat).
          { clear -Hin. induction fields' as [| f' fields'' IHf]; simpl in *.
            - inversion Hin.
            - destruct Hin as [Heq | Hin'].
              + subst. apply Nat.le_max_l.
              + eapply Nat.le_trans; [apply IHf, Hin' | apply Nat.le_max_r]. }
          simpl in Hn. lia. }
        repeat split; try assumption.
        intros fuel0 Hf0 rest0.
        exact ((IHn (expr_fuel fe0) Hlt0 fe0 (le_n _)) Hvfe0 fuel0 Hf0 rest0). }
      assert (Hfone : (fields_fuel ((k, fe) :: fields') <= fuel')%nat).
      { pose proof (fields_fuel_le_len_fold ((k, fe) :: fields')) as Hle.
        simpl in Hle. simpl. lia. }
      pose proof (print_parse_fieldsN_roundtrip k fe fields' Hvk Hvfe
                    (fun fuel0 Hf0 rest0 => (IHn (expr_fuel fe) Hone fe (le_n _)) Hvfe fuel0 Hf0 rest0)
                    Hall fuel' Hfone) as Hpf.
      destruct fields' as [| [k2 fe2] fields''];
        repeat rewrite string_append_assoc; simpl; simpl in Hpf;
        rewrite (Hpf (String "}"%char rest)); reflexivity.
  - (* EFieldN *)
    simpl in Hn.
    assert (Hlt1 : (expr_fuel e1 < n)%nat) by lia.
    apply andb_true_iff in Hvalid as [Hname Hv1].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    repeat rewrite string_append_assoc.
    rewrite (parse_qstring_print name Hname). simpl.
    repeat rewrite string_append_assoc.
    rewrite ((IHn (expr_fuel e1) Hlt1 e1 (le_n _)) Hv1 fuel' Hf1). reflexivity.

  }
  intros e Hvalid fuel Hfuel rest.
  exact (Hstrong (expr_fuel e) e (le_n _) Hvalid fuel Hfuel rest).
Qed.
