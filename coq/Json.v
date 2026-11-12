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
(** * The [expr] codec itself *)

Fixpoint print_expr (e : expr) : string :=
  match e with
  | EConst z =>
      "{""tag"":""const"",""value"":" ++ z_to_string z ++ "}"
  | EVar x =>
      "{""tag"":""var"",""name"":" ++ quote_string x ++ "}"
  | EAdd e1 e2 =>
      "{""tag"":""add"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | ESub e1 e2 =>
      "{""tag"":""sub"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EMul e1 e2 =>
      "{""tag"":""mul"",""lhs"":" ++ print_expr e1 ++ ",""rhs"":" ++ print_expr e2 ++ "}"
  | EIf0 c e1 e2 =>
      "{""tag"":""if0"",""cond"":" ++ print_expr c
        ++ ",""then"":" ++ print_expr e1 ++ ",""else"":" ++ print_expr e2 ++ "}"
  | ELet x e1 e2 =>
      "{""tag"":""let"",""name"":" ++ quote_string x
        ++ ",""value"":" ++ print_expr e1 ++ ",""body"":" ++ print_expr e2 ++ "}"
  end.

Fixpoint expr_fuel (e : expr) : nat :=
  match e with
  | EConst _ | EVar _ => 1
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => S (Nat.max (expr_fuel e1) (expr_fuel e2))
  | EIf0 c e1 e2 => S (Nat.max (expr_fuel c) (Nat.max (expr_fuel e1) (expr_fuel e2)))
  | ELet _ e1 e2 => S (Nat.max (expr_fuel e1) (expr_fuel e2))
  end.

(** Dispatch on the full fixed literal prefix of each constructor's
    printed form directly, trying each in turn, rather than reading the
    "tag" field generically and comparing strings. This is what makes the
    round-trip proof tractable: every literal [expect] call here matches
    a literal chunk [print_expr] produces byte-for-byte, so the proof is
    just [expect_app] (plus the recursive hypothesis / [parse_number_print]
    / [parse_qstring_print] for the dynamic parts) all the way down -- no
    separate reasoning about tag extraction or string comparison is
    needed. A non-matching candidate's [expect] call fails purely by
    comparing concrete characters (it never needs to inspect what follows),
    so trying one candidate costs nothing when the input is shaped like a
    different constructor. *)
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
    match expect "{""tag"":""if0"",""cond"":" s with
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
                            | Some s7 => Some (EIf0 c e1 e2, s7)
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
    | None => None
    end end end end end end end
  end.

Definition parse_expr_top (s : string) : option (expr * string) :=
  parse_expr (String.length s + 1) s.

(** The headline theorem: for every [expr] with valid identifiers, printing
    it and parsing the result back (with enough fuel, any amount at least
    [expr_fuel e]) recovers exactly the original term and consumes exactly
    the printed text, leaving [rest] untouched. This is the "parser is a
    proven inverse of our own grammar" correctness statement discussed in
    GOAL.md. *)
(** Keep [simpl]/[cbn] from peeking inside these during the round-trip
    proof below: we only ever want to reason about them through the
    already-proven [parse_number_print]/[parse_qstring_print] equations,
    uniformly across every constructor case, rather than have [simpl]
    eagerly (and inconsistently) inline one but not the other depending on
    whether its first character happens to be syntactically concrete. *)
Opaque parse_number parse_qstring quote_string.

Lemma not_digit_rbrace : is_digit "}"%char = false.
Proof. reflexivity. Qed.

Lemma not_minus_rbrace : "}"%char <> minus_char.
Proof. discriminate. Qed.

Theorem parse_print_roundtrip :
  forall e,
    expr_idents_valid is_valid_ident e = true ->
    forall fuel, (expr_fuel e <= fuel)%nat ->
    forall rest, parse_expr fuel (print_expr e ++ rest) = Some (e, rest).
Proof.
  induction e as
    [ z
    | x
    | e1 IH1 e2 IH2
    | e1 IH1 e2 IH2
    | e1 IH1 e2 IH2
    | c IHc e1 IH1 e2 IH2
    | x e1 IH1 e2 IH2 ];
  intros Hvalid fuel Hfuel rest;
  destruct fuel as [| fuel']; simpl in Hfuel; try lia;
  simpl.
  - (* EConst *)
    rewrite string_append_assoc. simpl.
    rewrite (parse_number_print z "}"%char rest not_digit_rbrace not_minus_rbrace).
    reflexivity.
  - (* EVar *)
    simpl in Hvalid.
    rewrite string_append_assoc. simpl.
    rewrite (parse_qstring_print x Hvalid (String "}"%char rest)).
    reflexivity.
  - (* EAdd *)
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    rewrite string_append_assoc. simpl. rewrite string_append_assoc.
    rewrite (IH1 Hv1 fuel' Hf1).
    simpl.
    rewrite (IH2 Hv2 fuel' Hf2).
    reflexivity.
  - (* ESub *)
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    rewrite string_append_assoc. simpl. rewrite string_append_assoc.
    rewrite (IH1 Hv1 fuel' Hf1).
    simpl.
    rewrite (IH2 Hv2 fuel' Hf2).
    reflexivity.
  - (* EMul *)
    apply andb_true_iff in Hvalid as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    rewrite string_append_assoc. simpl. rewrite string_append_assoc.
    rewrite (IH1 Hv1 fuel' Hf1).
    simpl.
    rewrite (IH2 Hv2 fuel' Hf2).
    reflexivity.
  - (* EIf0 *)
    apply andb_true_iff in Hvalid as [Hvc Hv12].
    apply andb_true_iff in Hv12 as [Hv1 Hv2].
    assert (Hfc : (expr_fuel c <= fuel')%nat) by lia.
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    rewrite string_append_assoc. simpl. rewrite string_append_assoc.
    rewrite (IHc Hvc fuel' Hfc).
    simpl. rewrite string_append_assoc.
    rewrite (IH1 Hv1 fuel' Hf1).
    simpl.
    rewrite (IH2 Hv2 fuel' Hf2).
    reflexivity.
  - (* ELet *)
    apply andb_true_iff in Hvalid as [Hvx Hv12].
    apply andb_true_iff in Hv12 as [Hv1 Hv2].
    assert (Hf1 : (expr_fuel e1 <= fuel')%nat) by lia.
    assert (Hf2 : (expr_fuel e2 <= fuel')%nat) by lia.
    rewrite string_append_assoc. simpl. rewrite string_append_assoc.
    rewrite (parse_qstring_print x Hvx).
    simpl. rewrite string_append_assoc.
    rewrite (IH1 Hv1 fuel' Hf1).
    simpl.
    rewrite (IH2 Hv2 fuel' Hf2).
    reflexivity.
Qed.
