(** RealJson.v

    A real JSON-*text* parser for Coq's own [Extraction Language JSON]
    output -- the piece [RealIR.v]'s header has flagged, since that
    file's very first commit, as "not yet written": until now, every
    [real_decl]/[real_expr] in the examples was built *by hand* to
    match what a probe run of [coqc] was observed to emit, never
    mechanically parsed from the actual JSON bytes. This file closes
    that gap.

    Two layers, kept deliberately separate:
    - [jvalue]/[parse_json]: a small, *generic* JSON value parser
      (objects/arrays/strings/numbers/bools/null), independent of
      anything [RealIR.v]-specific, reusing [Json.v]'s string/number
      lexing ([parse_qtext]/[parse_number]) unchanged. The one
      substantive difference from [Json.v]'s own bespoke grammar: real
      [coqc] extraction output is pretty-printed with embedded
      newlines/indentation (confirmed directly -- [Json.v]'s grammar
      is deliberately whitespace-free), so every token boundary here
      skips whitespace first.
    - [real_expr_of_json]/[real_decl_of_json]/[real_fix_decl_of_json]:
      the [RealIR.v]-specific *interpreter* from [jvalue] into this
      project's already-proven [real_expr]/[real_decl]/
      [real_fix_decl], recognizing exactly the real, [coqc]-confirmed
      shapes: [decl:term] / [decl:fixgroup]'s [fixgroup:item] /
      [expr:lambda] (with a direct, non-curried [argnames] list) /
      [expr:case] + [case] + [pat:constructor] / [expr:apply] /
      [expr:global] / [expr:rel] / [expr:constructor] (covering
      [True]/[False], [Nil]/[Cons], [Pair], [Inl]/[Inr], [Z0]/[Zpos]/
      [Zneg] applied to nested [XI]/[XO]/[XH] for a numeral, and an
      arbitrary N-ary record constructor name for [RRecord3]), a
      self-recursive call recognized as an [expr:apply] whose [func] is
      an [expr:global] naming the enclosing [fixgroup:item] itself, and
      (confirmed against a real, Coquelicot-adjacent probe -- see
      [RealIR.v]'s own header) a Coquelicot-adjacent [R] literal, which
      extracts as [expr:apply]/[expr:global "iZR"] applied to a nested
      [Z] numeral -- recognized specially (via [float_of_Z], turning
      the parsed numeral directly into an [RFLit]) rather than falling
      through to the generic [expr:apply]/[expr:global] dispatch below,
      which would otherwise build an unrecognized [RApp1 "iZR" (RZLit
      z)] (["iZR"] is not a name [RealIR.v]'s [real_eval]/
      [real_to_expr] know, only [RFLit] is).
      Every one of these shapes was confirmed by a *fresh* probe run of
      [coqc] 8.18.0 on genuine, human-written [Definition]s/
      [Fixpoint]s (not reused from this file's own prose, and not
      assumed) -- see the scratch probes this commit's message points
      to. Anything outside the already-recognized [real_expr] fragment
      is simply [None], the same honest partiality [real_to_expr]
      itself already uses.

    One confirmed limitation, not yet handled: Coq's extraction will
    eta-reduce a definition whose body is *exactly* another function
    applied to all its arguments in order (e.g. [Definition getfst p
    := fst p] extracts as a bare [expr:global "fst"], not an
    [expr:lambda] applying it) -- probed directly. [real_decl_of_json]
    does not re-expand this; a [decl:term] whose [value] is not an
    [expr:lambda] is simply not recognized. This does not affect
    ordinary, non-point-free physics/math definitions (the only kind
    this project's examples use), but is worth naming rather than
    silently mishandling.

    Performance: the straightforward version of this parser, run on a
    real 22KB [coqc]-extracted module, took 45 *seconds* -- traced to
    four separate O(n^2) spots in [Json.v]'s/this file's string-scanning
    primitives under [ExtrOcamlNativeString]'s realization of [string]
    pattern-matching (one re-slices the remaining input per character
    consumed) plus [nat]'s default unary representation. Fixed via four
    targeted [Extract Constant] realizers in [Extract.v] -- replacing
    only the *extracted OCaml*, not the Coq-level definitions or any
    proof about them -- bringing the same 22KB module under 0.2
    seconds; see [Extract.v]'s comment for the full before/after
    trail. This is why every entry point below takes a [fuel] derived
    from [String.length s + 1] ([Json.v]'s own [parse_expr_top]
    convention) rather than something tighter: fuel is now cheap to
    have plenty of.

    What is proved here and what is not, stated plainly: [parse_json]
    is a total, fuel-bounded function (it always terminates), and now
    *does* carry a machine-checked roundtrip theorem of its own --
    [jvalue_parse_print_roundtrip], right after [parse_json] below,
    mirroring [Json.v]'s own [parse_print_roundtrip] for this file's
    generic [jvalue] layer (zero axioms, confirmed via [Print
    Assumptions]). That theorem is deliberately scoped to *only* the
    generic [jvalue] layer, not the [real_expr_of_json]/
    [real_decl_of_json] interpretation layer below it -- the proved,
    trusted end of the *semantic* pipeline still starts at [real_decl]
    ([real_decl_to_expr_preserves_semantics], already proved, in
    [RealIR.v]). Correctness of parsing real [coqc] output into a
    [real_decl] is checked, for now, by actually running it on real
    extracted JSON (four confirmed, working instances: [clamp_nonneg]'s
    [if], [classify]'s 2-case sum, [swap_xz]'s 3-field record, and
    [any_true]'s self-recursive [Fixpoint] over a list -- each
    producing, through the full, already-proven rest of the pipeline,
    *exactly* the same generated Python the hand-built [real_decl]/
    [real_fix_decl] for the same source definition already produces in
    [examples/NaturalCoq.v]) -- not yet by proof, and not a gap this
    file's own [jvalue] round-trip theorem closes: that interpretation
    layer's target is "whatever shapes [coqc]'s extraction can ever
    produce", an open-ended, moving target this project has already
    declined to chase elsewhere (see [resolve_intrinsic_name]'s own
    extraction-name-instability discussion). See docs/roadmap.md for
    the full account of both halves. *)

From Coq Require Import ZArith String List Bool Ascii Lia.
From Coq Require Import Decimal DecimalString DecimalPos DecimalZ.
From Coq Require Import Floats.PrimFloat Floats.FloatOps Floats.SpecFloat.
Import ListNotations.
Require Import Lang.
Require Import RealIR.
Require Import Json.
Open Scope string_scope.
Open Scope nat_scope.

(* ------------------------------------------------------------------ *)
(** * A generic JSON value, and a parser for it *)

Inductive jvalue : Type :=
  | JString (s : string)
  | JBool (b : bool)
  | JNull
  | JNum (z : Z)
  | JArray (vs : list jvalue)
  | JObject (fields : list (string * jvalue)).

Definition is_ws (a : ascii) : bool :=
  orb (Ascii.eqb a " "%char)
      (orb (Ascii.eqb a (ascii_of_nat 10))
           (orb (Ascii.eqb a (ascii_of_nat 13)) (Ascii.eqb a (ascii_of_nat 9)))).

Definition skip_ws (s : string) : string := snd (take_while is_ws s).

(** One [fuel] unit is spent per [jvalue] level of nesting *and* per
    sibling visited inside one [JObject]/[JArray] (both the per-level
    [parse_members]/[parse_elems] loop and [parse_jvalue] itself
    decrement it) -- generous, but always at least the real recursion
    depth, the same margin [Json.v]'s [String.length s + 1] convention
    already relies on elsewhere ([parse_expr_top]). *)
Fixpoint parse_jvalue (fuel : nat) (s : string) : option (jvalue * string) :=
  match fuel with
  | O => None
  | S fuel' =>
      let s := skip_ws s in
      match expect "{" s with
      | Some rest =>
          match
            (fix parse_members (fuel0 : nat) (s0 : string) : option (list (string * jvalue) * string) :=
               match fuel0 with
               | O => None
               | S fuel0' =>
                   let s0 := skip_ws s0 in
                   match expect "}" s0 with
                   | Some rest0 => Some ([], rest0)
                   | None =>
                       match parse_qtext s0 with
                       | Some (key, rest1) =>
                           match expect ":" (skip_ws rest1) with
                           | Some rest2 =>
                               match parse_jvalue fuel0' (skip_ws rest2) with
                               | Some (v, rest3) =>
                                   let rest3 := skip_ws rest3 in
                                   match expect "," rest3 with
                                   | Some rest4 =>
                                       match parse_members fuel0' (skip_ws rest4) with
                                       | Some (fs, rest5) => Some ((key, v) :: fs, rest5)
                                       | None => None
                                       end
                                   | None =>
                                       match expect "}" rest3 with
                                       | Some rest4 => Some ([(key, v)], rest4)
                                       | None => None
                                       end
                                   end
                               | None => None
                               end
                           | None => None
                           end
                       | None => None
                       end
                   end
               end) fuel' (skip_ws rest)
          with
          | Some (fs, rest') => Some (JObject fs, rest')
          | None => None
          end
      | None =>
      match expect "[" s with
      | Some rest =>
          match
            (fix parse_elems (fuel0 : nat) (s0 : string) : option (list jvalue * string) :=
               match fuel0 with
               | O => None
               | S fuel0' =>
                   let s0 := skip_ws s0 in
                   match expect "]" s0 with
                   | Some rest0 => Some ([], rest0)
                   | None =>
                       match parse_jvalue fuel0' s0 with
                       | Some (v, rest1) =>
                           let rest1 := skip_ws rest1 in
                           match expect "," rest1 with
                           | Some rest2 =>
                               match parse_elems fuel0' (skip_ws rest2) with
                               | Some (vs, rest3) => Some (v :: vs, rest3)
                               | None => None
                               end
                           | None =>
                               match expect "]" rest1 with
                               | Some rest2 => Some ([v], rest2)
                               | None => None
                               end
                           end
                       | None => None
                       end
                   end
               end) fuel' (skip_ws rest)
          with
          | Some (vs, rest') => Some (JArray vs, rest')
          | None => None
          end
      | None =>
      match s with
      | String """"%char _ =>
          match parse_qtext s with
          | Some (str, rest) => Some (JString str, rest)
          | None => None
          end
      | _ =>
          match expect "true" s with
          | Some rest => Some (JBool true, rest)
          | None =>
          match expect "false" s with
          | Some rest => Some (JBool false, rest)
          | None =>
          match expect "null" s with
          | Some rest => Some (JNull, rest)
          | None =>
          match parse_number s with
          | Some (z, rest) => Some (JNum z, rest)
          | None => None
          end end end end
      end
      end
      end
  end.

Definition parse_json (s : string) : option jvalue :=
  match parse_jvalue (S (String.length s)) s with
  | Some (v, _) => Some v
  | None => None
  end.

(* ------------------------------------------------------------------ *)
(** * Soundness: a generic [jvalue] print/parse round-trip

    [jvalue_parse_print_roundtrip] below proves that [parse_jvalue] can
    always recover a [jvalue] from what [print_jvalue] (defined here
    purely for this proof -- nothing upstream of this file ever prints
    a [jvalue] in practice, since the real JSON text this file parses
    comes from [coqc]'s own extraction, not from this project) printed
    for it, for any fuel budget at least [jvalue_fuel v], and any
    trailing [rest] that cannot be mistaken for more digits of a
    trailing [JNum] ([safe_rest] -- the same proviso [Json.v]'s own
    [parse_number_print] already carries, for the same reason: a
    text-based number grammar is inherently ambiguous against an
    adjacent digit without *some* terminator).

    Deliberately scoped to *only* this generic [jvalue] layer (the
    closed, stable JSON-value grammar), not the [real_expr_of_json]
    interpretation layer built on top of it below: that layer's own
    target is "whatever shapes [coqc]'s extraction can ever produce",
    an open-ended, moving target this project has already declined to
    chase elsewhere (see the extraction-name-instability discussion
    above [resolve_intrinsic_name]) -- it remains checked empirically,
    against real probes, same as before. The boundary is the same one
    [Json.v] itself draws between its own proven [expr]/[parse_expr]
    round-trip and the hand-verified (not mechanically proven) claim
    that real [coqc]-extracted terms actually print through [PyPrint.v]
    the way the worked examples show. *)


Fixpoint print_jvalue (j : jvalue) : string :=
  match j with
  | JString s => quote_text s
  | JBool true => "true"
  | JBool false => "false"
  | JNull => "null"
  | JNum z => z_to_string z
  | JArray vs =>
      "[" ++
      (fix go (vs : list jvalue) : string :=
         match vs with
         | [] => ""
         | [v] => print_jvalue v
         | v :: rest => print_jvalue v ++ "," ++ go rest
         end) vs
      ++ "]"
  | JObject fs =>
      "{" ++
      (fix go (fs : list (string * jvalue)) : string :=
         match fs with
         | [] => ""
         | [(k, v)] => quote_text k ++ ":" ++ print_jvalue v
         | (k, v) :: rest => quote_text k ++ ":" ++ print_jvalue v ++ "," ++ go rest
         end) fs
      ++ "}"
  end.

Fixpoint jvalue_fuel (j : jvalue) : nat :=
  match j with
  | JString _ | JBool _ | JNull | JNum _ => 1
  | JArray vs => S (S (length vs + fold_right (fun v acc => Nat.max (jvalue_fuel v) acc) O vs))
  | JObject fs => S (S (length fs + fold_right (fun kv acc => Nat.max (jvalue_fuel (snd kv)) acc) O fs))
  end.

Lemma bracket_app : forall X : string, "[" ++ X = String "["%char X.
Proof. reflexivity. Qed.

Lemma skip_ws_bracket_noop : forall X, skip_ws (String "]"%char X) = String "]"%char X.
Proof. intro X. unfold skip_ws. simpl. reflexivity. Qed.

Lemma skip_ws_brace_noop : forall X, skip_ws (String "}"%char X) = String "}"%char X.
Proof. intro X. unfold skip_ws. simpl. reflexivity. Qed.

Lemma expect_bracket_eq : forall rest, expect "]" (String "]"%char rest) = Some rest.
Proof. reflexivity. Qed.

Lemma expect_brace_eq : forall rest, expect "}" (String "}"%char rest) = Some rest.
Proof. reflexivity. Qed.

Lemma brace_app : forall X : string, "{" ++ X = String "{"%char X.
Proof. reflexivity. Qed.

Lemma in_le_fold_max : forall v1 vs,
  In v1 vs -> jvalue_fuel v1 <= fold_right (fun v acc => Nat.max (jvalue_fuel v) acc) O vs.
Proof.
  induction vs as [|v vs' IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma jvalue_fuel_array_head_lt : forall v0 vs', jvalue_fuel v0 < jvalue_fuel (JArray (v0 :: vs')).
Proof.
  intros v0 vs'. simpl.
  pose proof (Nat.le_max_l (jvalue_fuel v0)
                (fold_right (fun v acc => Nat.max (jvalue_fuel v) acc) O vs')) as H.
  lia.
Qed.

Lemma jvalue_fuel_array_elem_lt : forall v0 vs' v1,
  In v1 vs' -> jvalue_fuel v1 < jvalue_fuel (JArray (v0 :: vs')).
Proof.
  intros v0 vs' v1 Hin. simpl.
  pose proof (in_le_fold_max v1 vs' Hin) as H1.
  pose proof (Nat.le_max_r (jvalue_fuel v0)
                (fold_right (fun v acc => Nat.max (jvalue_fuel v) acc) O vs')) as H2.
  lia.
Qed.

Lemma in_le_fold_max_fields : forall (kv : string * jvalue) (fs : list (string * jvalue)),
  In kv fs -> jvalue_fuel (snd kv) <= fold_right (fun kv0 acc => Nat.max (jvalue_fuel (snd kv0)) acc) O fs.
Proof.
  induction fs as [|kv0 fs' IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma jvalue_fuel_object_head_lt : forall (kv0 : string * jvalue) fs', jvalue_fuel (snd kv0) < jvalue_fuel (JObject (kv0 :: fs')).
Proof.
  intros kv0 fs'. simpl.
  pose proof (Nat.le_max_l (jvalue_fuel (snd kv0))
                (fold_right (fun kv acc => Nat.max (jvalue_fuel (snd kv)) acc) O fs')) as H.
  lia.
Qed.

Lemma jvalue_fuel_object_elem_lt : forall (kv0 : string * jvalue) fs' (kv1 : string * jvalue),
  In kv1 fs' -> jvalue_fuel (snd kv1) < jvalue_fuel (JObject (kv0 :: fs')).
Proof.
  intros kv0 fs' kv1 Hin. simpl.
  pose proof (in_le_fold_max_fields kv1 fs' Hin) as H1.
  pose proof (Nat.le_max_r (jvalue_fuel (snd kv0))
                (fold_right (fun kv acc => Nat.max (jvalue_fuel (snd kv)) acc) O fs')) as H2.
  lia.
Qed.

Lemma skip_ws_noop : forall s, (match s with String a _ => is_ws a = false | EmptyString => True end) -> skip_ws s = s.
Proof.
  intros s. unfold skip_ws. destruct s as [| a s'].
  - reflexivity.
  - intro H. simpl. rewrite H. reflexivity.
Qed.

(* A "safe" trailing string: either empty, or starts with a character
   that can never be mistaken for more digits of a preceding number. *)
Definition safe_rest (rest : string) : Prop :=
  match rest with
  | EmptyString => True
  | String a _ => is_digit a = false /\ a <> minus_char
  end.

(* Structural chars { } [ ] , : are all non-digit, non-whitespace. *)
Lemma safe_rest_struct : forall (c : ascii) (s : string),
  In c ["{"%char;"}"%char;"["%char;"]"%char;","%char;":"%char] ->
  safe_rest (String c s).
Proof.
  intros c s Hin. unfold safe_rest, is_digit.
  simpl in Hin.
  repeat (destruct Hin as [Heq|Hin]; [subst; split; [reflexivity | discriminate] |]).
  contradiction.
Qed.

Lemma safe_rest_bracket : forall rest, safe_rest ("]" ++ rest).
Proof. intro rest. apply safe_rest_struct. simpl. tauto. Qed.

Lemma safe_rest_brace : forall rest, safe_rest ("}" ++ rest).
Proof. intro rest. apply safe_rest_struct. simpl. tauto. Qed.

Lemma safe_rest_comma : forall rest, safe_rest ("," ++ rest).
Proof. intro rest. apply safe_rest_struct. simpl. tauto. Qed.

Lemma take_while_all : forall (p : ascii -> bool) (x : string),
  string_forallb p x = true -> take_while p x = (x, EmptyString).
Proof.
  induction x as [| c x' IH]; intros Hall; simpl.
  - reflexivity.
  - simpl in Hall. apply andb_true_iff in Hall as [Hc Hall'].
    rewrite Hc. rewrite (IH Hall'). reflexivity.
Qed.

Lemma string_append_nil_r : forall s, s ++ "" = s.
Proof. induction s as [|c s' IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma parse_number_print_nil :
  forall z, parse_number (z_to_string z) = Some (z, EmptyString).
Proof.
  intro z. destruct z as [|p|p].
  - reflexivity.
  - destruct (nilzero_string_of_uint_cons (Pos.to_uint p)) as (c & s0 & Hcs).
    pose proof (nilzero_string_of_uint_all_digits (Pos.to_uint p)) as Hall.
    rewrite Hcs in Hall.
    assert (Hzp : z_to_string (Zpos p) = String c s0).
    { unfold z_to_string, NilZero.string_of_int.
      replace (Z.to_int (Zpos p)) with (Decimal.Pos (Pos.to_uint p)) by reflexivity.
      simpl. exact Hcs. }
    rewrite Hzp.
    rewrite parse_number_unfold.
    assert (Hcm : c <> minus_char) by (intro Heq; subst c; simpl in Hall; discriminate).
    assert (Hcmb : Ascii.eqb c minus_char = false) by (apply (proj2 (Ascii.eqb_neq _ _)); exact Hcm).
    rewrite Hcmb.
    rewrite (take_while_all is_digit (String c s0) Hall).
    assert (Hfinal : z_of_string (String c s0) = Some (Zpos p))
      by (rewrite <- Hzp; apply z_round_trip).
    rewrite Hfinal. reflexivity.
  - assert (Hzn : z_to_string (Zneg p) = String minus_char (NilZero.string_of_uint (Pos.to_uint p))).
    { unfold z_to_string, NilZero.string_of_int.
      replace (Z.to_int (Zneg p)) with (Decimal.Neg (Pos.to_uint p)) by reflexivity.
      reflexivity. }
    rewrite Hzn.
    rewrite parse_number_unfold.
    rewrite Ascii.eqb_refl.
    pose proof (nilzero_string_of_uint_all_digits (Pos.to_uint p)) as Hall.
    rewrite (take_while_all is_digit (NilZero.string_of_uint (Pos.to_uint p)) Hall).
    assert (Hfinal : z_of_string (String minus_char (NilZero.string_of_uint (Pos.to_uint p))) = Some (Zneg p))
      by (rewrite <- Hzn; apply z_round_trip).
    rewrite Hfinal. reflexivity.
Qed.

Lemma z_to_string_first_char :
  forall z, exists c s, z_to_string z = String c s /\
    (is_digit c = true \/ c = minus_char).
Proof.
  intro z. destruct z as [|p|p].
  - exists "0"%char, EmptyString. split; [reflexivity | left; reflexivity].
  - unfold z_to_string, NilZero.string_of_int.
    replace (Z.to_int (Zpos p)) with (Decimal.Pos (Pos.to_uint p)) by reflexivity.
    simpl.
    destruct (nilzero_string_of_uint_cons (Pos.to_uint p)) as (c & s0 & Hcs).
    pose proof (nilzero_string_of_uint_all_digits (Pos.to_uint p)) as Hall.
    rewrite Hcs in Hall. simpl in Hall.
    apply andb_true_iff in Hall as [Hd _].
    exists c, s0. split; [exact Hcs | left; exact Hd].
  - unfold z_to_string, NilZero.string_of_int.
    replace (Z.to_int (Zneg p)) with (Decimal.Neg (Pos.to_uint p)) by reflexivity.
    simpl. eexists _, _. split; [reflexivity | right; reflexivity].
Qed.

Lemma print_jvalue_first_char :
  forall j, exists c s, print_jvalue j = String c s /\
    (c = quote_char \/ c = "t"%char \/ c = "f"%char \/ c = "n"%char \/
     is_digit c = true \/ c = minus_char \/ c = "["%char \/ c = "{"%char).
Proof.
  intros [s | [] | | z | vs | fs]; simpl.
  - eexists _, _. split; [reflexivity | left; reflexivity].
  - eexists _, _. split; [reflexivity | right; left; reflexivity].
  - eexists _, _. split; [reflexivity | right; right; left; reflexivity].
  - eexists _, _. split; [reflexivity | right; right; right; left; reflexivity].
  - destruct (z_to_string_first_char z) as (c & s0 & Heq & Hc).
    rewrite Heq. eexists _, _. split; [reflexivity |].
    destruct Hc as [Hc|Hc]; [right; right; right; right; left; exact Hc
                            | right; right; right; right; right; left; exact Hc].
  - eexists _, _. split; [reflexivity | right; right; right; right; right; right; left; reflexivity].
  - eexists _, _. split; [reflexivity | right; right; right; right; right; right; right; reflexivity].
Qed.

Lemma is_digit_not_ws : forall c, is_digit c = true -> is_ws c = false.
Proof.
  intro c. unfold is_digit. intro H.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  unfold is_ws.
  assert (H10 : (10 < 256)%nat) by lia.
  assert (H13 : (13 < 256)%nat) by lia.
  assert (H9 : (9 < 256)%nat) by lia.
  assert (Hsp : Ascii.eqb c " "%char = false).
  { apply Ascii.eqb_neq. intro Hc. subst c. compute in H1, H2. lia. }
  assert (Hnl : Ascii.eqb c (ascii_of_nat 10) = false).
  { apply Ascii.eqb_neq. intro Hc. subst c.
    rewrite (nat_ascii_embedding 10 H10) in H1, H2. lia. }
  assert (Hcr : Ascii.eqb c (ascii_of_nat 13) = false).
  { apply Ascii.eqb_neq. intro Hc. subst c.
    rewrite (nat_ascii_embedding 13 H13) in H1, H2. lia. }
  assert (Htb : Ascii.eqb c (ascii_of_nat 9) = false).
  { apply Ascii.eqb_neq. intro Hc. subst c.
    rewrite (nat_ascii_embedding 9 H9) in H1, H2. lia. }
  rewrite Hsp, Hnl, Hcr, Htb. reflexivity.
Qed.

Lemma minus_char_not_ws : is_ws minus_char = false.
Proof. reflexivity. Qed.

Lemma print_jvalue_not_ws : forall j rest c s,
  print_jvalue j ++ rest = String c s -> is_ws c = false.
Proof.
  intros j rest c s Heq.
  destruct (print_jvalue_first_char j) as (c0 & s0 & Hp & Hclass).
  rewrite Hp in Heq. simpl in Heq. injection Heq as Hc0 _. subst c0.
  destruct Hclass as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst;
    try reflexivity; try (apply is_digit_not_ws; exact H); try (apply minus_char_not_ws).
Qed.

Fixpoint parse_jarray_elems (fuel0 : nat) (s0 : string) : option (list jvalue * string) :=
  match fuel0 with
  | O => None
  | S fuel0' =>
      let s0 := skip_ws s0 in
      match expect "]" s0 with
      | Some rest0 => Some ([], rest0)
      | None =>
          match parse_jvalue fuel0' s0 with
          | Some (v, rest1) =>
              let rest1 := skip_ws rest1 in
              match expect "," rest1 with
              | Some rest2 =>
                  match parse_jarray_elems fuel0' (skip_ws rest2) with
                  | Some (vs, rest3) => Some (v :: vs, rest3)
                  | None => None
                  end
              | None =>
                  match expect "]" rest1 with
                  | Some rest2 => Some ([v], rest2)
                  | None => None
                  end
              end
          | None => None
          end
      end
  end.

Lemma parse_jvalue_array_eq : forall fuel' rest,
  parse_jvalue (S fuel') (String "["%char rest) =
    match parse_jarray_elems fuel' (skip_ws rest) with
    | Some (vs, rest') => Some (JArray vs, rest')
    | None => None
    end.
Proof. intros. reflexivity. Qed.

Fixpoint parse_jobject_fields (fuel0 : nat) (s0 : string) : option (list (string * jvalue) * string) :=
  match fuel0 with
  | O => None
  | S fuel0' =>
      let s0 := skip_ws s0 in
      match expect "}" s0 with
      | Some rest0 => Some ([], rest0)
      | None =>
          match parse_qtext s0 with
          | Some (key, rest1) =>
              match expect ":" (skip_ws rest1) with
              | Some rest2 =>
                  match parse_jvalue fuel0' (skip_ws rest2) with
                  | Some (v, rest3) =>
                      let rest3 := skip_ws rest3 in
                      match expect "," rest3 with
                      | Some rest4 =>
                          match parse_jobject_fields fuel0' (skip_ws rest4) with
                          | Some (fs, rest5) => Some ((key, v) :: fs, rest5)
                          | None => None
                          end
                      | None =>
                          match expect "}" rest3 with
                          | Some rest4 => Some ([(key, v)], rest4)
                          | None => None
                          end
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      end
  end.

Lemma parse_jvalue_object_eq : forall fuel' rest,
  parse_jvalue (S fuel') (String "{"%char rest) =
    match parse_jobject_fields fuel' (skip_ws rest) with
    | Some (fs, rest') => Some (JObject fs, rest')
    | None => None
    end.
Proof. intros. reflexivity. Qed.

Fixpoint print_jvalue_list (vs : list jvalue) : string :=
  match vs with
  | [] => ""
  | [v] => print_jvalue v
  | v :: rest => print_jvalue v ++ "," ++ print_jvalue_list rest
  end.

Lemma print_jvalue_list_cons2 : forall v v2 vs'',
  print_jvalue_list (v :: v2 :: vs'') = print_jvalue v ++ "," ++ print_jvalue_list (v2 :: vs'').
Proof. reflexivity. Qed.

Lemma print_jvalue_list_first_char :
  forall v vs, exists c s, print_jvalue_list (v :: vs) = String c s /\
    (c = quote_char \/ c = "t"%char \/ c = "f"%char \/ c = "n"%char \/
     is_digit c = true \/ c = minus_char \/ c = "["%char \/ c = "{"%char).
Proof.
  intros v vs.
  destruct (print_jvalue_first_char v) as (c & s & Hp & Hclass).
  destruct vs as [|v2 vs2]; simpl; rewrite Hp; eexists _, _; split; [reflexivity | exact Hclass | reflexivity | exact Hclass].
Qed.

Lemma print_jvalue_list_not_ws : forall v vs rest c s,
  print_jvalue_list (v :: vs) ++ rest = String c s -> is_ws c = false.
Proof.
  intros v vs rest c s Heq.
  destruct (print_jvalue_list_first_char v vs) as (c0 & s0 & Hp & Hclass).
  rewrite Hp in Heq. simpl in Heq. injection Heq as Hc0 _. subst c0.
  destruct Hclass as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst;
    try reflexivity; try (apply is_digit_not_ws; exact H); try (apply minus_char_not_ws).
Qed.

Lemma skip_ws_noop_print_list : forall v vs rest,
  skip_ws (print_jvalue_list (v :: vs) ++ rest) = print_jvalue_list (v :: vs) ++ rest.
Proof.
  intros v vs rest.
  destruct (print_jvalue_list_first_char v vs) as (c & s & Hp & _).
  rewrite Hp. simpl.
  apply skip_ws_noop.
  simpl.
  apply (print_jvalue_list_not_ws v vs rest c (s ++ rest)).
  rewrite Hp. reflexivity.
Qed.

Fixpoint print_jvalue_fields (fs : list (string * jvalue)) : string :=
  match fs with
  | [] => ""
  | [(k, v)] => quote_text k ++ ":" ++ print_jvalue v
  | (k, v) :: rest => quote_text k ++ ":" ++ print_jvalue v ++ "," ++ print_jvalue_fields rest
  end.

Lemma print_jvalue_array_eq : forall vs, print_jvalue (JArray vs) = "[" ++ print_jvalue_list vs ++ "]".
Proof. intro vs. destruct vs as [|v vs']; reflexivity. Qed.

Lemma print_jvalue_object_eq : forall fs, print_jvalue (JObject fs) = "{" ++ print_jvalue_fields fs ++ "}".
Proof. intro fs. destruct fs as [|[k v] fs']; reflexivity. Qed.


Lemma parse_jarray_elems_unfold : forall fuel0 s0,
  parse_jarray_elems (S fuel0) s0 =
    let s0 := skip_ws s0 in
    match expect "]" s0 with
    | Some rest0 => Some ([], rest0)
    | None =>
        match parse_jvalue fuel0 s0 with
        | Some (v, rest1) =>
            let rest1 := skip_ws rest1 in
            match expect "," rest1 with
            | Some rest2 =>
                match parse_jarray_elems fuel0 (skip_ws rest2) with
                | Some (vs, rest3) => Some (v :: vs, rest3)
                | None => None
                end
            | None =>
                match expect "]" rest1 with
                | Some rest2 => Some ([v], rest2)
                | None => None
                end
            end
        | None => None
        end
    end.
Proof. reflexivity. Qed.


Lemma expect_single_neq : forall (a c : ascii) (s : string), a <> c -> expect (String a EmptyString) (String c s) = None.
Proof.
  intros a c s Hne. simpl.
  destruct (Ascii.eqb a c) eqn:E.
  - apply Ascii.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma print_jvalue_app_not_char : forall v rest (a : ascii),
  (forall c s, print_jvalue v = String c s -> a <> c) ->
  expect (String a EmptyString) (print_jvalue v ++ rest) = None.
Proof.
  intros v rest a Hneq.
  destruct (print_jvalue_first_char v) as (c & s & Hp & _).
  rewrite Hp. simpl. apply expect_single_neq. apply (Hneq c s Hp).
Qed.

Lemma print_jvalue_class_neq : forall v (c0 : ascii) s,
  print_jvalue v = String c0 s ->
  c0 = quote_char \/ c0 = "t"%char \/ c0 = "f"%char \/ c0 = "n"%char \/
  is_digit c0 = true \/ c0 = minus_char \/ c0 = "["%char \/ c0 = "{"%char.
Proof.
  intros v c0 s Hp.
  destruct (print_jvalue_first_char v) as (c1 & s1 & Hp1 & Hclass).
  rewrite Hp in Hp1. injection Hp1 as Hc _. subst c1. exact Hclass.
Qed.

Lemma print_jvalue_not_bracket : forall v rest, expect "]" (print_jvalue v ++ rest) = None.
Proof.
  intros v rest. apply print_jvalue_app_not_char.
  intros c s Hp. pose proof (print_jvalue_class_neq v c s Hp) as Hclass.
  intro Hbad. subst c.
  destruct Hclass as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; discriminate.
Qed.

Lemma print_jvalue_not_brace : forall v rest, expect "}" (print_jvalue v ++ rest) = None.
Proof.
  intros v rest. apply print_jvalue_app_not_char.
  intros c s Hp. pose proof (print_jvalue_class_neq v c s Hp) as Hclass.
  intro Hbad. subst c.
  destruct Hclass as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; discriminate.
Qed.

Lemma print_jvalue_not_comma2 : forall v rest, expect "," (print_jvalue v ++ rest) = None.
Proof.
  intros v rest. apply print_jvalue_app_not_char.
  intros c s Hp. pose proof (print_jvalue_class_neq v c s Hp) as Hclass.
  intro Hbad. subst c.
  destruct Hclass as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; discriminate.
Qed.

Lemma skip_ws_noop_print : forall v rest, skip_ws (print_jvalue v ++ rest) = print_jvalue v ++ rest.
Proof.
  intros v rest.
  destruct (print_jvalue_first_char v) as (c & s & Hp & _).
  rewrite Hp. simpl.
  apply skip_ws_noop.
  simpl.
  apply (print_jvalue_not_ws v rest c (s ++ rest)).
  rewrite Hp. reflexivity.
Qed.

Lemma print_parse_jarray_singleton :
  forall v,
    (forall fuel0, (jvalue_fuel v <= fuel0)%nat -> forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue v ++ rest0) = Some (v, rest0)) ->
    forall fuel, (jvalue_fuel v <= fuel)%nat ->
      forall rest,
        parse_jarray_elems (S fuel) (print_jvalue v ++ "]" ++ rest) = Some ([v], rest).
Proof.
  intros v Hv fuel Hfuel rest.
  rewrite parse_jarray_elems_unfold.
  rewrite skip_ws_noop_print.
  cbv zeta.
  rewrite (print_jvalue_not_bracket v ("]" ++ rest)).
  rewrite (Hv fuel Hfuel ("]" ++ rest) (safe_rest_bracket rest)).
  cbv zeta.
  replace (skip_ws ("]" ++ rest)) with ("]" ++ rest) by (simpl; unfold skip_ws; simpl; reflexivity).
  destruct (expect "," ("]" ++ rest)) eqn:Hcomma.
  - simpl in Hcomma. discriminate.
  - simpl. reflexivity.
Qed.


Fixpoint jvalue_list_fuel (vs : list jvalue) : nat :=
  match vs with
  | [] => O
  | v :: rest => S (Nat.max (jvalue_fuel v) (jvalue_list_fuel rest))
  end.

Lemma jvalue_list_fuel_cons : forall v vs,
  jvalue_list_fuel (v :: vs) = S (Nat.max (jvalue_fuel v) (jvalue_list_fuel vs)).
Proof. reflexivity. Qed.

Lemma jvalue_list_fuel_le_len_fold :
  forall vs, (jvalue_list_fuel vs <= length vs + fold_right (fun v acc => Nat.max (jvalue_fuel v) acc) O vs)%nat.
Proof.
  induction vs as [| v vs' IH]; simpl.
  - lia.
  - apply le_n_S.
    rewrite <- Nat.add_max_distr_l.
    apply Nat.max_le_compat; [lia | exact IH].
Qed.

Lemma print_parse_jarray_roundtrip :
  forall v vs',
    (forall fuel0, (jvalue_fuel v <= fuel0)%nat -> forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue v ++ rest0) = Some (v, rest0)) ->
    Forall (fun v0 => forall fuel0, (jvalue_fuel v0 <= fuel0)%nat -> forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue v0 ++ rest0) = Some (v0, rest0)) vs' ->
    forall fuel, (jvalue_list_fuel (v :: vs') <= fuel)%nat ->
      forall rest,
        parse_jarray_elems (S fuel) (print_jvalue_list (v :: vs') ++ "]" ++ rest) = Some (v :: vs', rest).
Proof.
  intros v vs'. revert v.
  induction vs' as [| v2 vs'' IH]; intros v Hv Hall fuel Hfuel rest.
  - (* singleton *)
    rewrite jvalue_list_fuel_cons in Hfuel.
    simpl jvalue_list_fuel in Hfuel.
    assert (Hone : (jvalue_fuel v <= fuel)%nat) by lia.
    simpl print_jvalue_list.
    exact (print_parse_jarray_singleton v Hv fuel Hone rest).
  - (* cons: v :: v2 :: vs'' *)
    rewrite jvalue_list_fuel_cons in Hfuel.
    destruct fuel as [|fuel'].
    + exfalso. lia.
    + assert (Hone : (jvalue_fuel v <= S fuel')%nat) by lia.
      assert (Hfuel' : (jvalue_list_fuel (v2 :: vs'') <= fuel')%nat) by lia.
      inversion Hall as [| x l Hx Hl]; subst.
    rewrite print_jvalue_list_cons2.
    repeat rewrite string_append_assoc.
    rewrite parse_jarray_elems_unfold.
    rewrite skip_ws_noop_print.
    cbv zeta.
    rewrite (print_jvalue_not_bracket v (","%string ++ (print_jvalue_list (v2 :: vs'') ++ "]" ++ rest))).
    rewrite (Hv (S fuel') Hone (","%string ++ (print_jvalue_list (v2 :: vs'') ++ "]" ++ rest)) (safe_rest_comma (print_jvalue_list (v2 :: vs'') ++ "]" ++ rest))).
    cbv zeta.
    replace (skip_ws ("," ++ (print_jvalue_list (v2 :: vs'') ++ "]" ++ rest)))
      with ("," ++ (print_jvalue_list (v2 :: vs'') ++ "]" ++ rest))
      by (simpl; unfold skip_ws; simpl; reflexivity).
    rewrite (expect_app "," (print_jvalue_list (v2 :: vs'') ++ "]" ++ rest)).
    rewrite (skip_ws_noop_print_list v2 vs'' ("]" ++ rest)).
    pose proof (IH v2 Hx Hl fuel' Hfuel' rest) as IH'.
    rewrite IH'.
    reflexivity.
Qed.

Lemma quote_char_not_ws : is_ws quote_char = false.
Proof. reflexivity. Qed.

Lemma quote_text_not_brace : forall k rest, expect "}" (quote_text k ++ rest) = None.
Proof.
  intros k rest. unfold quote_text. simpl. reflexivity.
Qed.

Lemma quote_text_first_char : forall k, exists s, quote_text k = String quote_char s.
Proof. intro k. unfold quote_text. eexists. reflexivity. Qed.

Lemma quote_text_not_ws : forall k rest c s,
  quote_text k ++ rest = String c s -> is_ws c = false.
Proof.
  intros k rest c s Heq.
  destruct (quote_text_first_char k) as (s0 & Hp).
  rewrite Hp in Heq. simpl in Heq. injection Heq as Hc0 _. subst c.
  apply quote_char_not_ws.
Qed.

Lemma skip_ws_noop_quote : forall k rest, skip_ws (quote_text k ++ rest) = quote_text k ++ rest.
Proof.
  intros k rest.
  destruct (quote_text_first_char k) as (s & Hp).
  rewrite Hp. simpl.
  apply skip_ws_noop.
  simpl.
  apply (quote_text_not_ws k rest quote_char (s ++ rest)).
  rewrite Hp. reflexivity.
Qed.

Lemma print_jvalue_fields_first_char : forall k v fs,
  exists s, print_jvalue_fields ((k, v) :: fs) = String quote_char s.
Proof.
  intros k v fs.
  destruct fs as [|kv2 fs2]; simpl; unfold quote_text; simpl; eexists; reflexivity.
Qed.

Lemma print_jvalue_fields_not_ws : forall k v fs rest c s,
  print_jvalue_fields ((k, v) :: fs) ++ rest = String c s -> is_ws c = false.
Proof.
  intros k v fs rest c s Heq.
  destruct (print_jvalue_fields_first_char k v fs) as (s0 & Hp).
  rewrite Hp in Heq. simpl in Heq. injection Heq as Hc0 _. subst c.
  apply quote_char_not_ws.
Qed.

Lemma skip_ws_noop_print_fields : forall k v fs rest,
  skip_ws (print_jvalue_fields ((k, v) :: fs) ++ rest) = print_jvalue_fields ((k, v) :: fs) ++ rest.
Proof.
  intros k v fs rest.
  destruct (print_jvalue_fields_first_char k v fs) as (s & Hp).
  rewrite Hp. simpl.
  apply skip_ws_noop.
  simpl.
  apply (print_jvalue_fields_not_ws k v fs rest quote_char (s ++ rest)).
  rewrite Hp. reflexivity.
Qed.

Lemma print_jvalue_fields_singleton : forall k v,
  print_jvalue_fields [(k, v)] = quote_text k ++ ":" ++ print_jvalue v.
Proof. reflexivity. Qed.

Lemma print_jvalue_fields_cons2 : forall k v k2 v2 fs'',
  print_jvalue_fields ((k, v) :: (k2, v2) :: fs'') =
    quote_text k ++ ":" ++ print_jvalue v ++ "," ++ print_jvalue_fields ((k2, v2) :: fs'').
Proof. reflexivity. Qed.

Lemma parse_jobject_fields_unfold : forall fuel0 s0,
  parse_jobject_fields (S fuel0) s0 =
    let s0 := skip_ws s0 in
    match expect "}" s0 with
    | Some rest0 => Some ([], rest0)
    | None =>
        match parse_qtext s0 with
        | Some (key, rest1) =>
            match expect ":" (skip_ws rest1) with
            | Some rest2 =>
                match parse_jvalue fuel0 (skip_ws rest2) with
                | Some (v, rest3) =>
                    let rest3 := skip_ws rest3 in
                    match expect "," rest3 with
                    | Some rest4 =>
                        match parse_jobject_fields fuel0 (skip_ws rest4) with
                        | Some (fs, rest5) => Some ((key, v) :: fs, rest5)
                        | None => None
                        end
                    | None =>
                        match expect "}" rest3 with
                        | Some rest4 => Some ([(key, v)], rest4)
                        | None => None
                        end
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
    end.
Proof. intros. reflexivity. Qed.

Fixpoint jvalue_fields_fuel (fs : list (string * jvalue)) : nat :=
  match fs with
  | [] => O
  | kv :: rest => S (Nat.max (jvalue_fuel (snd kv)) (jvalue_fields_fuel rest))
  end.

Lemma jvalue_fields_fuel_cons : forall kv fs,
  jvalue_fields_fuel (kv :: fs) = S (Nat.max (jvalue_fuel (snd kv)) (jvalue_fields_fuel fs)).
Proof. reflexivity. Qed.

Lemma jvalue_fields_fuel_le_len_fold :
  forall fs, (jvalue_fields_fuel fs <= length fs + fold_right (fun kv acc => Nat.max (jvalue_fuel (snd kv)) acc) O fs)%nat.
Proof.
  induction fs as [| kv fs' IH]; simpl.
  - lia.
  - apply le_n_S.
    rewrite <- Nat.add_max_distr_l.
    apply Nat.max_le_compat; [lia | exact IH].
Qed.

Lemma print_parse_jobject_singleton :
  forall k v,
    (forall fuel0, (jvalue_fuel v <= fuel0)%nat -> forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue v ++ rest0) = Some (v, rest0)) ->
    forall fuel, (jvalue_fuel v <= fuel)%nat ->
      forall rest,
        parse_jobject_fields (S fuel) (print_jvalue_fields [(k, v)] ++ "}" ++ rest) = Some ([(k, v)], rest).
Proof.
  intros k v Hv fuel Hfuel rest.
  rewrite print_jvalue_fields_singleton.
  repeat rewrite string_append_assoc.
  rewrite parse_jobject_fields_unfold.
  rewrite (skip_ws_noop_quote k (":" ++ (print_jvalue v ++ ("}" ++ rest)))).
  cbv zeta.
  rewrite (quote_text_not_brace k (":" ++ (print_jvalue v ++ ("}" ++ rest)))).
  rewrite (parse_qtext_print k (":" ++ (print_jvalue v ++ ("}" ++ rest)))).
  replace (skip_ws (":" ++ (print_jvalue v ++ ("}" ++ rest))))
    with (":" ++ (print_jvalue v ++ ("}" ++ rest)))
    by (simpl; unfold skip_ws; simpl; reflexivity).
  rewrite (expect_app ":" (print_jvalue v ++ ("}" ++ rest))).
  rewrite skip_ws_noop_print.
  rewrite (Hv fuel Hfuel ("}" ++ rest) (safe_rest_brace rest)).
  replace (skip_ws ("}" ++ rest)) with ("}" ++ rest) by (simpl; unfold skip_ws; simpl; reflexivity).
  destruct (expect "," ("}" ++ rest)) eqn:Hcomma.
  - simpl in Hcomma. discriminate.
  - rewrite (expect_app "}" rest). reflexivity.
Qed.

Lemma print_parse_jobject_roundtrip :
  forall k v fs',
    (forall fuel0, (jvalue_fuel v <= fuel0)%nat -> forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue v ++ rest0) = Some (v, rest0)) ->
    Forall (fun kv => forall fuel0, (jvalue_fuel (snd kv) <= fuel0)%nat -> forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue (snd kv) ++ rest0) = Some (snd kv, rest0)) fs' ->
    forall fuel, (jvalue_fields_fuel ((k, v) :: fs') <= fuel)%nat ->
      forall rest,
        parse_jobject_fields (S fuel) (print_jvalue_fields ((k, v) :: fs') ++ "}" ++ rest) = Some ((k, v) :: fs', rest).
Proof.
  intros k v fs'. revert k v.
  induction fs' as [| kv2 fs'' IH]; intros k v Hv Hall fuel Hfuel rest.
  - (* singleton *)
    rewrite jvalue_fields_fuel_cons in Hfuel.
    simpl in Hfuel.
    assert (Hone : (jvalue_fuel v <= fuel)%nat) by lia.
    rewrite print_jvalue_fields_singleton.
    exact (print_parse_jobject_singleton k v Hv fuel Hone rest).
  - (* cons: (k,v) :: kv2 :: fs'' *)
    rewrite jvalue_fields_fuel_cons in Hfuel.
    destruct kv2 as [k2 v2].
    destruct fuel as [|fuel'].
    + inversion Hfuel.
    + pose proof (le_S_n _ _ Hfuel) as Hfuel2.
      assert (Hone : (jvalue_fuel v <= S fuel')%nat)
        by (apply le_S; eapply Nat.le_trans; [apply Nat.le_max_l | exact Hfuel2]).
      assert (Hfuel' : (jvalue_fields_fuel ((k2, v2) :: fs'') <= fuel')%nat)
        by (eapply Nat.le_trans; [apply Nat.le_max_r | exact Hfuel2]).
      inversion Hall as [| x l Hx Hl]; subst.
    rewrite print_jvalue_fields_cons2.
    repeat rewrite string_append_assoc.
    rewrite parse_jobject_fields_unfold.
    rewrite (skip_ws_noop_quote k (":" ++ (print_jvalue v ++ ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest)))))).
    cbv zeta.
    rewrite (quote_text_not_brace k
               (":" ++ (print_jvalue v ++ ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest)))))).
    rewrite (parse_qtext_print k (":" ++ (print_jvalue v ++ ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest)))))).
    replace (skip_ws (":" ++ (print_jvalue v ++ ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest))))))
      with (":" ++ (print_jvalue v ++ ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest)))))
      by (simpl; unfold skip_ws; simpl; reflexivity).
    rewrite (expect_app ":" (print_jvalue v ++ ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest))))).
    rewrite skip_ws_noop_print.
    rewrite (Hv (S fuel') Hone ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest))) (safe_rest_comma (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest)))).
    replace (skip_ws ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest))))
      with ("," ++ (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest)))
      by (simpl; unfold skip_ws; simpl; reflexivity).
    rewrite (expect_app "," (print_jvalue_fields ((k2, v2) :: fs'') ++ ("}" ++ rest))).
    rewrite (skip_ws_noop_print_fields k2 v2 fs'' ("}" ++ rest)).
    pose proof (IH k2 v2 Hx Hl fuel' Hfuel' rest) as IH'.
    rewrite IH'.
    reflexivity.
Qed.

Lemma parse_jvalue_qtext_eq : forall fuel' s rest,
  parse_jvalue (S fuel') (quote_text s ++ rest) =
    match parse_qtext (quote_text s ++ rest) with
    | Some (str, rest') => Some (JString str, rest')
    | None => None
    end.
Proof. intros. reflexivity. Qed.

Lemma parse_jvalue_true_eq : forall fuel' rest,
  parse_jvalue (S fuel') ("true" ++ rest) =
    match expect "true" ("true" ++ rest) with
    | Some rest' => Some (JBool true, rest')
    | None => None
    end.
Proof. intros. reflexivity. Qed.

Lemma parse_jvalue_false_eq : forall fuel' rest,
  parse_jvalue (S fuel') ("false" ++ rest) =
    match expect "false" ("false" ++ rest) with
    | Some rest' => Some (JBool false, rest')
    | None => None
    end.
Proof. intros. reflexivity. Qed.

Lemma parse_jvalue_null_eq : forall fuel' rest,
  parse_jvalue (S fuel') ("null" ++ rest) =
    match expect "null" ("null" ++ rest) with
    | Some rest' => Some (JNull, rest')
    | None => None
    end.
Proof. intros. reflexivity. Qed.

Lemma parse_jvalue_unfold : forall fuel0 s0,
  parse_jvalue (S fuel0) s0 =
    let s0 := skip_ws s0 in
    match expect "{" s0 with
    | Some rest =>
        match
          (fix parse_members (fuel1 : nat) (s1 : string) : option (list (string * jvalue) * string) :=
             match fuel1 with
             | O => None
             | S fuel1' =>
                 let s1 := skip_ws s1 in
                 match expect "}" s1 with
                 | Some rest0 => Some ([], rest0)
                 | None =>
                     match parse_qtext s1 with
                     | Some (key, rest1) =>
                         match expect ":" (skip_ws rest1) with
                         | Some rest2 =>
                             match parse_jvalue fuel1' (skip_ws rest2) with
                             | Some (v, rest3) =>
                                 let rest3 := skip_ws rest3 in
                                 match expect "," rest3 with
                                 | Some rest4 =>
                                     match parse_members fuel1' (skip_ws rest4) with
                                     | Some (fs, rest5) => Some ((key, v) :: fs, rest5)
                                     | None => None
                                     end
                                 | None =>
                                     match expect "}" rest3 with
                                     | Some rest4 => Some ([(key, v)], rest4)
                                     | None => None
                                     end
                                 end
                             | None => None
                             end
                         | None => None
                         end
                     | None => None
                     end
                 end
             end) fuel0 (skip_ws rest)
        with
        | Some (fs, rest') => Some (JObject fs, rest')
        | None => None
        end
    | None =>
    match expect "[" s0 with
    | Some rest =>
        match
          (fix parse_elems (fuel1 : nat) (s1 : string) : option (list jvalue * string) :=
             match fuel1 with
             | O => None
             | S fuel1' =>
                 let s1 := skip_ws s1 in
                 match expect "]" s1 with
                 | Some rest0 => Some ([], rest0)
                 | None =>
                     match parse_jvalue fuel1' s1 with
                     | Some (v, rest1) =>
                         let rest1 := skip_ws rest1 in
                         match expect "," rest1 with
                         | Some rest2 =>
                             match parse_elems fuel1' (skip_ws rest2) with
                             | Some (vs, rest3) => Some (v :: vs, rest3)
                             | None => None
                             end
                         | None =>
                             match expect "]" rest1 with
                             | Some rest2 => Some ([v], rest2)
                             | None => None
                             end
                         end
                     | None => None
                     end
                 end
             end) fuel0 (skip_ws rest)
        with
        | Some (vs, rest') => Some (JArray vs, rest')
        | None => None
        end
    | None =>
    match s0 with
    | String """"%char _ =>
        match parse_qtext s0 with
        | Some (str, rest) => Some (JString str, rest)
        | None => None
        end
    | _ =>
        match expect "true" s0 with
        | Some rest => Some (JBool true, rest)
        | None =>
        match expect "false" s0 with
        | Some rest => Some (JBool false, rest)
        | None =>
        match expect "null" s0 with
        | Some rest => Some (JNull, rest)
        | None =>
        match parse_number s0 with
        | Some (z, rest) => Some (JNum z, rest)
        | None => None
        end end end end
    end
    end
    end.
Proof. intros. reflexivity. Qed.

Lemma parse_jvalue_num_eq : forall fuel0 z rest,
  parse_jvalue (S fuel0) (z_to_string z ++ rest) =
    match parse_number (z_to_string z ++ rest) with
    | Some (z', rest') => Some (JNum z', rest')
    | None => None
    end.
Proof.
  intros fuel0 z rest.
  destruct (z_to_string_first_char z) as (c & s0 & Heq & Hc).
  rewrite Heq. simpl.
  destruct Hc as [Hd | Hm].
  - unfold is_digit in Hd. apply andb_true_iff in Hd as [H1 H2].
    apply Nat.leb_le in H1. apply Nat.leb_le in H2.
    destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0, b1, b2, b3, b4, b5, b6, b7; compute in H1, H2; try lia; reflexivity.
  - subst c. reflexivity.
Qed.

Theorem jvalue_parse_print_roundtrip :
  forall v,
    forall fuel, (jvalue_fuel v <= fuel)%nat ->
    forall rest, safe_rest rest ->
      parse_jvalue fuel (print_jvalue v ++ rest) = Some (v, rest).
Proof.
  assert (Hstrong : forall n v,
    (jvalue_fuel v <= n)%nat ->
    forall fuel, (jvalue_fuel v <= fuel)%nat ->
    forall rest, safe_rest rest ->
      parse_jvalue fuel (print_jvalue v ++ rest) = Some (v, rest)).
  {
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros v Hn fuel Hfuel rest Hsafe.
  destruct v as [str | b | | z | vs | fs].
  - (* JString str *)
    simpl print_jvalue.
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    rewrite (parse_jvalue_qtext_eq fuel' str rest).
    rewrite (parse_qtext_print str rest).
    reflexivity.
  - (* JBool b *)
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    destruct b; simpl print_jvalue.
    + rewrite (parse_jvalue_true_eq fuel' rest).
      rewrite (expect_app "true" rest). reflexivity.
    + rewrite (parse_jvalue_false_eq fuel' rest).
      rewrite (expect_app "false" rest). reflexivity.
  - (* JNull *)
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl print_jvalue.
    rewrite (parse_jvalue_null_eq fuel' rest).
    rewrite (expect_app "null" rest). reflexivity.
  - (* JNum z *)
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl print_jvalue.
    rewrite (parse_jvalue_num_eq fuel' z rest).
    destruct rest as [|a rest'].
    + rewrite string_append_nil_r. rewrite (parse_number_print_nil z). reflexivity.
    + destruct Hsafe as [Hdig Hmin].
      rewrite (parse_number_print z a rest' Hdig Hmin). reflexivity.
  - (* JArray vs *)
    destruct vs as [|v0 vs'].
    + (* empty array *)
      simpl. simpl in Hfuel.
      destruct fuel as [|fuel1]; [exfalso; lia|].
      destruct fuel1 as [|fuel2]; [exfalso; lia|].
      rewrite (parse_jvalue_array_eq (S fuel2) (String "]"%char rest)).
      rewrite skip_ws_bracket_noop.
      rewrite parse_jarray_elems_unfold.
      rewrite skip_ws_bracket_noop.
      cbv zeta.
      rewrite expect_bracket_eq.
      reflexivity.
    + (* nonempty array *)
      assert (Hlt0 : jvalue_fuel v0 < n)
        by (eapply Nat.lt_le_trans; [apply jvalue_fuel_array_head_lt | exact Hn]).
      pose proof (IHn (jvalue_fuel v0) Hlt0 v0 (le_n _)) as Hv0.
      assert (Hall' : Forall (fun v1 => forall fuel0, (jvalue_fuel v1 <= fuel0)%nat ->
                 forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue v1 ++ rest0) = Some (v1, rest0)) vs').
      { apply Forall_forall. intros v1 Hin.
        assert (Hlt1 : jvalue_fuel v1 < n)
          by (eapply Nat.lt_le_trans; [apply (jvalue_fuel_array_elem_lt v0 vs' v1 Hin) | exact Hn]).
        exact (IHn (jvalue_fuel v1) Hlt1 v1 (le_n _)). }
      simpl in Hfuel.
      destruct fuel as [|fuel1]; [exfalso; lia|].
      destruct fuel1 as [|fuel2].
      * exfalso. simpl in Hfuel.
        exact (Nat.nle_succ_0 _ (le_S_n _ _ Hfuel)).
      * assert (Hlf : (jvalue_list_fuel (v0 :: vs') <= fuel2)%nat).
        { pose proof (jvalue_list_fuel_le_len_fold (v0 :: vs')) as Hb.
          simpl in Hfuel. simpl in Hb.
          eapply Nat.le_trans; [exact Hb | apply (le_S_n _ _ (le_S_n _ _ Hfuel))]. }
        rewrite print_jvalue_array_eq.
      repeat rewrite string_append_assoc.
      rewrite bracket_app.
      rewrite (parse_jvalue_array_eq (S fuel2) (print_jvalue_list (v0 :: vs') ++ "]" ++ rest)).
      rewrite (skip_ws_noop_print_list v0 vs' ("]" ++ rest)).
      rewrite (print_parse_jarray_roundtrip v0 vs' Hv0 Hall' fuel2 Hlf rest).
      reflexivity.
  - (* JObject fs *)
    destruct fs as [|kv0 fs'].
    + (* empty object *)
      simpl. simpl in Hfuel.
      destruct fuel as [|fuel1]; [exfalso; lia|].
      destruct fuel1 as [|fuel2]; [exfalso; lia|].
      rewrite (parse_jvalue_object_eq (S fuel2) (String "}"%char rest)).
      rewrite skip_ws_brace_noop.
      rewrite parse_jobject_fields_unfold.
      rewrite skip_ws_brace_noop.
      cbv zeta.
      rewrite expect_brace_eq.
      reflexivity.
    + (* nonempty object *)
      assert (Hlt0 : jvalue_fuel (snd kv0) < n)
        by (eapply Nat.lt_le_trans; [apply jvalue_fuel_object_head_lt | exact Hn]).
      pose proof (IHn (jvalue_fuel (snd kv0)) Hlt0 (snd kv0) (le_n _)) as Hv0.
      assert (Hall' : Forall (fun kv => forall fuel0, (jvalue_fuel (snd kv) <= fuel0)%nat ->
                 forall rest0, safe_rest rest0 -> parse_jvalue fuel0 (print_jvalue (snd kv) ++ rest0) = Some (snd kv, rest0)) fs').
      { apply Forall_forall. intros kv1 Hin.
        assert (Hlt1 : jvalue_fuel (snd kv1) < n)
          by (eapply Nat.lt_le_trans; [apply (jvalue_fuel_object_elem_lt kv0 fs' kv1 Hin) | exact Hn]).
        exact (IHn (jvalue_fuel (snd kv1)) Hlt1 (snd kv1) (le_n _)). }
      simpl in Hfuel.
      destruct fuel as [|fuel1]; [exfalso; lia|].
      destruct fuel1 as [|fuel2].
      * exfalso. simpl in Hfuel.
        exact (Nat.nle_succ_0 _ (le_S_n _ _ Hfuel)).
      * assert (Hlf : (jvalue_fields_fuel (kv0 :: fs') <= fuel2)%nat).
        { pose proof (jvalue_fields_fuel_le_len_fold (kv0 :: fs')) as Hb.
          simpl in Hfuel. simpl in Hb.
          eapply Nat.le_trans; [exact Hb | apply (le_S_n _ _ (le_S_n _ _ Hfuel))]. }
        rewrite print_jvalue_object_eq.
      repeat rewrite string_append_assoc.
      rewrite brace_app.
      rewrite (parse_jvalue_object_eq (S fuel2) (print_jvalue_fields (kv0 :: fs') ++ "}" ++ rest)).
      destruct kv0 as [k0 v0].
      rewrite (skip_ws_noop_print_fields k0 v0 fs' ("}" ++ rest)).
      rewrite (print_parse_jobject_roundtrip k0 v0 fs' Hv0 Hall' fuel2 Hlf rest).
      reflexivity.
  }
  intros v fuel Hfuel rest Hsafe.
  exact (Hstrong (jvalue_fuel v) v (le_n _) fuel Hfuel rest Hsafe).
Qed.


(* ------------------------------------------------------------------ *)
(** * Small [jvalue] accessors *)

Definition jfield (fields : list (string * jvalue)) (key : string) : option jvalue :=
  (fix go (fs : list (string * jvalue)) : option jvalue :=
     match fs with
     | [] => None
     | (k, v) :: rest => if string_dec k key then Some v else go rest
     end) fields.

Definition jwhat (fields : list (string * jvalue)) : option string :=
  match jfield fields "what" with
  | Some (JString w) => Some w
  | _ => None
  end.

Definition jname (fields : list (string * jvalue)) : option string :=
  match jfield fields "name" with
  | Some (JString w) => Some w
  | _ => None
  end.

(* ------------------------------------------------------------------ *)
(** * Reading a [Z] literal back out of its [Z0]/[Zpos]/[Zneg] +
    [XI]/[XO]/[XH] constructor encoding *)

Fixpoint positive_of_json (fuel : nat) (j : jvalue) : option positive :=
  match fuel with
  | O => None
  | S fuel' =>
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "args" with
      | Some "expr:constructor", Some "XH", Some (JArray []) => Some xH
      | Some "expr:constructor", Some "XO", Some (JArray [p]) =>
          match positive_of_json fuel' p with
          | Some p' => Some (xO p')
          | None => None
          end
      | Some "expr:constructor", Some "XI", Some (JArray [p]) =>
          match positive_of_json fuel' p with
          | Some p' => Some (xI p')
          | None => None
          end
      | _, _, _ => None
      end
  | _ => None
  end
  end.

Definition z_of_json (fuel : nat) (j : jvalue) : option Z :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "args" with
      | Some "expr:constructor", Some "Z0", Some (JArray []) => Some Z0
      | Some "expr:constructor", Some "Zpos", Some (JArray [p]) =>
          match positive_of_json fuel p with
          | Some p' => Some (Zpos p')
          | None => None
          end
      | Some "expr:constructor", Some "Zneg", Some (JArray [p]) =>
          match positive_of_json fuel p with
          | Some p' => Some (Zneg p')
          | None => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(** A Coquelicot-adjacent [R] literal always extracts as [iZR] applied
    to a [Z] numeral (confirmed directly against the real [quad]
    probe, `coq/RealIR.v`'s own header) -- [float_of_Z] turns that
    numeral directly into the [PrimFloat.float] [RFLit] needs, via the
    same exact [spec_float] construction `coq/RealIR.v`'s probe already
    confirmed normalizes correctly ([SF2Prim]'s own job, not re-done
    here). Exact as long as [z] actually fits a double's 53-bit
    mantissa -- the same honestly-documented limitation this project
    already accepts for [Z] extracting to a native (not arbitrary-
    precision) [int] (`docs/roadmap.md`); not reconstructing it from
    nested [Zpos]/[XI]/[XO]/[XH] the way [RZLit]'s own [Z] literals are
    confirmed-exact for is a parsing-time convenience, not a new
    correctness claim -- this whole file, per its own header, is
    checked by running it on real JSON, not by a soundness proof. *)
Definition float_of_Z (z : Z) : PrimFloat.float :=
  match z with
  | Z0 => 0%float
  | Zpos p => SF2Prim (S754_finite false p 0)
  | Zneg p => SF2Prim (S754_finite true p 0)
  end.

(** A *decimal* [R] literal (e.g. [3.14]), unlike an integer one, does
    *not* extract as [iZR] -- confirmed directly against a fresh probe
    ([Definition decimal_lit (x : R) : R := x + 3.14.]): it extracts as
    [q2R (Qmake num den)], [QArith]'s own rational-to-real coercion
    applied to a [Q] ([num : Z] over [den : positive]) built the exact
    same [Zpos]/[Zneg]/[Z0]/[XI]/[XO]/[XH] way an ordinary [Z]/
    [positive] literal already is (confirmed directly: two ordinary
    integer literals/nested constructors, nothing new to parse at
    that level). [num / den] is in general *not* exactly representable
    in binary64 ([3.14 = 314/100], and [100] is not a power of two) --
    but that is not a new problem introduced here: it is exactly the
    same rounding every real decimal literal already undergoes the
    moment a human writes it down for a binary floating-point target,
    Python included (confirmed directly: Python's own literal [3.14]
    is already the nearest binary64 double, not the exact rational).
    So [PrimFloat.div (float_of_Z num) (float_of_Z (Zpos den))] --
    the correctly-rounded quotient, computed once at parse time, not
    reconstructed bit-for-bit -- is not an approximation *this project*
    introduces; it is the same, single rounding step any
    decimal-to-float literal already needs, computed through the one
    already-trusted primitive ([PrimFloat.div]) that performs it
    correctly, not a new one. *)
Definition rational_of_json (fuel : nat) (j : jvalue) : option PrimFloat.float :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "args" with
      | Some "expr:constructor", Some "Qmake", Some (JArray [numj; denj]) =>
          match z_of_json fuel numj, positive_of_json fuel denj with
          | Some num, Some den => Some (PrimFloat.div (float_of_Z num) (float_of_Z (Zpos den)))
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(* ------------------------------------------------------------------ *)
(** * Intrinsic name disambiguation (the "add0" problem)

    Confirmed directly (`RealIR.v`'s own header already names this):
    Coq's extraction gives an unqualified name to every declaration in
    one extraction unit, and resolves a collision by appending a
    disambiguating digit suffix to *whichever* of the colliding names
    was declared later -- not deterministically to the one this
    project cares about. A genuinely minimal probe confirms it both
    ways: a module needing only [ZArith] extracted [Z.add] (via plain
    [+]) as the *bare* name ["add"] in one run, but as ["add0"] in
    another otherwise-identical run that also defined a [Fixpoint]
    with a [nat] argument -- [positive]'s own internal [add] helper
    (always transitively pulled in by any real use of [Z]'s own
    arithmetic) claimed the bare name first in the second case, purely
    because of declaration order, not anything about [Z.add] itself.
    A hardcoded [string_dec fname "add"] is therefore only reliable by
    accident; this is the fix.

    The two colliding declarations are never the same Gallina
    function, so they are never the same *type*: [Z.add : Z -> Z ->
    Z], [positive]'s own internal [add] : [positive -> positive ->
    positive] -- confirmed directly in the probe above (the module's
    own ["add0"]/["add"] declarations carry exactly these two
    distinct, ground types, not something requiring guesswork). So
    the fix is not "try every digit suffix" (arbitrary, and still
    just guessing which of several same-named candidates is the right
    one) -- it is: strip a real call's name of any trailing digit
    suffix, and accept that candidate as the known intrinsic ["add"]
    only if *this module's own* declaration for that exact name has
    [Z.add]'s expected ground type. The resolved, *canonical* name
    (["add"], not ["add0"]) is substituted in before [RApp1]/[RApp2]
    is ever built, so [RealIR.v]'s own [real_eval]/[real_to_expr] --
    which only ever compare against the bare, canonical names -- need
    no change at all to benefit from this. *)
Fixpoint strip_trailing_digits_aux (s : string) : bool * string :=
  match s with
  | EmptyString => (true, EmptyString)
  | String c rest =>
      match strip_trailing_digits_aux rest with
      | (true, _) => if is_digit c then (true, EmptyString) else (false, String c EmptyString)
      | (false, rest') => (false, String c rest')
      end
  end.

Definition strip_trailing_digits (s : string) : string :=
  snd (strip_trailing_digits_aux s).

(** The handful of ground ["type:glob"] names this project's
    recognized fragment's intrinsics are typed over -- [z]/[bool] for
    the [Z.v]/[Bool.v] ops, [r] for the Coquelicot-adjacent float ops
    (`RealIR.v`'s own header). *)
Definition jtype_is_glob (name : string) (t : jvalue) : bool :=
  match t with
  | JObject fs =>
      match jwhat fs, jname fs with
      | Some "type:glob", Some n => if string_dec n name then true else false
      | _, _ => false
      end
  | _ => false
  end.

Definition jtype_is_unop (argty retty : string) (t : jvalue) : bool :=
  match t with
  | JObject fs =>
      match jwhat fs, jfield fs "left", jfield fs "right" with
      | Some "type:arrow", Some l, Some r =>
          andb (jtype_is_glob argty l) (jtype_is_glob retty r)
      | _, _, _ => false
      end
  | _ => false
  end.

Definition jtype_is_binop (argty retty : string) (t : jvalue) : bool :=
  match t with
  | JObject fs =>
      match jwhat fs, jfield fs "left", jfield fs "right" with
      | Some "type:arrow", Some l, Some (JObject rfs) =>
          match jwhat rfs, jfield rfs "left", jfield rfs "right" with
          | Some "type:arrow", Some l2, Some r2 =>
              andb (jtype_is_glob argty l) (andb (jtype_is_glob argty l2) (jtype_is_glob retty r2))
          | _, _, _ => false
          end
      | _, _, _ => false
      end
  | _ => false
  end.

(** Every top-level [decl:term]'s own name/type, and every
    [decl:fixgroup]'s *each* [fixgroup:item]'s own name/type --
    exactly the two places a declaration (and so a disambiguating
    digit suffix) can originate, the same two shapes
    [find_decl_by_name] already knows to look inside. *)
Definition module_decl_types (decls : list jvalue) : list (string * jvalue) :=
  (fix go (ds : list jvalue) : list (string * jvalue) :=
     match ds with
     | [] => []
     | JObject fs :: rest =>
         match jwhat fs with
         | Some "decl:term" =>
             match jname fs, jfield fs "type" with
             | Some n, Some t => (n, t) :: go rest
             | _, _ => go rest
             end
         | Some "decl:fixgroup" =>
             match jfield fs "fixlist" with
             | Some (JArray items) =>
                 ((fix go_items (its : list jvalue) : list (string * jvalue) :=
                     match its with
                     | [] => []
                     | JObject ifs :: rest' =>
                         match jname ifs, jfield ifs "type" with
                         | Some n, Some t => (n, t) :: go_items rest'
                         | _, _ => go_items rest'
                         end
                     | _ :: rest' => go_items rest'
                     end) items ++ go rest)%list
             | _ => go rest
             end
         | _ => go rest
         end
     | _ :: rest => go rest
     end) decls.

Definition lookup_decl_type (types : list (string * jvalue)) (n : string) : option jvalue :=
  (fix go (ts : list (string * jvalue)) : option jvalue :=
     match ts with
     | [] => None
     | (n', t) :: rest => if string_dec n n' then Some t else go rest
     end) types.

(** Resolve a real call's own name against the module's declaration
    table: if, after stripping any trailing digit suffix, it matches
    one of this project's known intrinsic base names *and* this exact
    (unstripped) name's own declared type in the module matches that
    intrinsic's expected ground type, substitute the canonical,
    unsuffixed name; otherwise leave [fname] untouched (the same
    "unrecognized name" fallback [RApp1]/[RApp2]/[real_eval]/
    [real_to_expr] already give any name this project doesn't know,
    not a new kind of failure). Deliberately covers only the
    arithmetic/comparison/boolean-connective/Coquelicot-float base
    names actually confirmed subject to this collision -- not
    ["fst"]/["snd"] (polymorphic over the pair's own element types, no
    single ground type to check against, and never observed to
    collide) or [RSelf]/[RCall]'s own names (resolved separately, via
    [self]/[siblings], not this table). *)
Definition resolve_intrinsic_name (types : list (string * jvalue)) (fname : string) : string :=
  let base := strip_trailing_digits fname in
  let try (expect_base : string) (check : jvalue -> bool) : option string :=
    if string_dec base expect_base then
      match lookup_decl_type types fname with
      | Some t => if check t then Some expect_base else None
      | None => None
      end
    else None
  in
  match try "add" (jtype_is_binop "z" "z") with Some b => b | None =>
  match try "sub" (jtype_is_binop "z" "z") with Some b => b | None =>
  match try "mul" (jtype_is_binop "z" "z") with Some b => b | None =>
  match try "ltb" (jtype_is_binop "z" "bool") with Some b => b | None =>
  match try "leb" (jtype_is_binop "z" "bool") with Some b => b | None =>
  match try "eqb" (jtype_is_binop "z" "bool") with Some b => b | None =>
  match try "andb" (jtype_is_binop "bool" "bool") with Some b => b | None =>
  match try "orb" (jtype_is_binop "bool" "bool") with Some b => b | None =>
  match try "negb" (jtype_is_unop "bool" "bool") with Some b => b | None =>
  match try "ropp" (jtype_is_unop "r" "r") with Some b => b | None =>
  match try "rabs" (jtype_is_unop "r" "r") with Some b => b | None =>
  match try "sqrt" (jtype_is_unop "r" "r") with Some b => b | None =>
  match try "rplus" (jtype_is_binop "r" "r") with Some b => b | None =>
  match try "rmult" (jtype_is_binop "r" "r") with Some b => b | None =>
  match try "rminus" (jtype_is_binop "r" "r") with Some b => b | None =>
  match try "rdiv" (jtype_is_binop "r" "r") with Some b => b | None =>
  fname
  end end end end end end end end end end end end end end end end.

(** [self] names the enclosing [fixgroup:item] (if any): a real,
    self-recursive call extracts as an ordinary [expr:apply] whose
    [func] is an [expr:global] naming *itself* (confirmed directly --
    not an [expr:rel], since the function is not a local binder from
    the body's own point of view), recognized here as [RSelf] only
    when that name matches [self]. *)
(** [find_record_field_name]: scans a [pat:constructor]'s raw
    [argnames] list (as [jvalue]s, expected all [JString]) for the
    *one* non-["_"] entry, requiring every other entry to be ["_"] --
    the general, any-length version of the fixed-arity ["_"]/[x]
    shapes [real_case_of_json]'s own 2- and 3-field patterns already
    match literally. Returns the field's own name, its 0-indexed
    position ([nskip], directly usable by [RProjN]), and whether it
    is the list's *last* entry. [None] if the list isn't shaped this
    way at all (no non-["_"] entry, more than one, or a non-[JString]
    member). *)
Fixpoint all_underscore (js : list jvalue) : bool :=
  match js with
  | [] => true
  | JString "_" :: rest => all_underscore rest
  | _ => false
  end.

Fixpoint find_record_field_name (idx : nat) (js : list jvalue) : option (string * nat * bool) :=
  match js with
  | [] => None
  | JString "_" :: rest => find_record_field_name (S idx) rest
  | JString y :: rest =>
      if all_underscore rest
      then Some (y, idx, match rest with [] => true | _ => false end)
      else None
  | _ => None
  end.

Definition is_rel_named (bodyj : jvalue) (x : string) : bool :=
  match bodyj with
  | JObject fs =>
      match jwhat fs, jname fs with
      | Some "expr:rel", Some y => if string_dec x y then true else false
      | _, _ => false
      end
  | _ => false
  end.

Fixpoint real_expr_of_json (self : option var) (siblings : list var) (types : list (string * jvalue)) (fuel : nat) (j : jvalue) {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  match j with
  | JObject fs =>
      match jwhat fs with
      | Some "expr:rel" =>
          match jname fs with
          | Some x => Some (RRel x)
          | None => None
          end
      | Some "expr:global" =>
          None (* a bare intrinsic reference with no arguments is not
                  a recognized real_expr shape on its own -- see this
                  file's header on eta-reduced definitions *)
      | Some "expr:constructor" =>
          match z_of_json fuel' j with
          | Some z => Some (RZLit z)
          | None =>
          match jname fs, jfield fs "args" with
          | Some "True", Some (JArray []) => Some (RBoolLit true)
          | Some "False", Some (JArray []) => Some (RBoolLit false)
          | Some "Nil", Some (JArray []) => Some RNil
          | Some "Cons", Some (JArray [h; t]) =>
              match real_expr_of_json self siblings types fuel' h, real_expr_of_json self siblings types fuel' t with
              | Some h', Some t' => Some (RCons h' t')
              | _, _ => None
              end
          | Some "Pair", Some (JArray [a; b]) =>
              match real_expr_of_json self siblings types fuel' a, real_expr_of_json self siblings types fuel' b with
              | Some a', Some b' => Some (RPair a' b')
              | _, _ => None
              end
          | Some "None", Some (JArray []) => Some RNone
          | Some "Some", Some (JArray [a]) =>
              match real_expr_of_json self siblings types fuel' a with
              | Some a' => Some (RSome a')
              | None => None
              end
          | _, Some (JArray (a :: b :: rest)) =>
              (* a genuinely N-ary record constructor (N >= 2 fields),
                 any name not already recognized above -- RRecordN,
                 the general replacement for the old "exactly 3"
                 RRecord3 fallback, which *also* fixes a real gap the
                 2-arg case above had: a real 2-field [Record]'s own
                 constructor is *not* named "Pair" the way a genuine
                 tuple's is (confirmed directly -- a real [Record
                 point := mkpoint { px py : Z }.] extracts its
                 constructor literally named ["Mkpoint"]), so before
                 this fallback existed, any 2-field [Record] whose
                 constructor happened not to be named "Pair" was
                 silently unrecognized. *)
              match real_expr_of_json self siblings types fuel' a,
                    real_expr_of_json self siblings types fuel' b,
                    (fix go (js : list jvalue) : option (list real_expr) :=
                       match js with
                       | [] => Some []
                       | j' :: rest' =>
                           match real_expr_of_json self siblings types fuel' j', go rest' with
                           | Some e', Some es' => Some (e' :: es')
                           | _, _ => None
                           end
                       end) rest
              with
              | Some a', Some b', Some rest' => Some (RRecordN (a' :: b' :: rest'))
              | _, _, _ => None
              end
          | _, _ => None
          end
          end
      | Some "expr:apply" =>
          match jfield fs "func", jfield fs "args" with
          | Some (JObject ffs), Some (JArray args) =>
              match jwhat ffs, jname ffs with
              | Some "expr:global", Some fname =>
                  match self with
                  | Some sname =>
                      if string_dec fname sname then
                        match args with
                        | [a] =>
                            match real_expr_of_json self siblings types fuel' a with
                            | Some a' => Some (RSelf a')
                            | None => None
                            end
                        | [] => None
                        | _ =>
                            (* more than one argument: a real
                               multi-argument self-call, confirmed by
                               probe (RealIR.v's header) to be one
                               [expr:apply] with a flat [args] list,
                               not curried. *)
                            match (fix parse_args (js : list jvalue) : option (list real_expr) :=
                                     match js with
                                     | [] => Some []
                                     | j :: rest =>
                                         match real_expr_of_json self siblings types fuel' j, parse_args rest with
                                         | Some e', Some es' => Some (e' :: es')
                                         | _, _ => None
                                         end
                                     end) args
                            with
                            | Some args' => Some (RSelfN args')
                            | None => None
                            end
                        end
                      else real_call_or_app self siblings types fuel' fname args
                  | None => real_call_or_app self siblings types fuel' fname args
                  end
              | _, _ => None
              end
          | _, _ => None
          end
      | Some "expr:case" =>
          match jfield fs "expr", jfield fs "cases" with
          | Some scrutinee_j, Some (JArray cases) =>
              match real_expr_of_json self siblings types fuel' scrutinee_j with
              | Some scrutinee =>
                  real_case_of_json self siblings types fuel' scrutinee cases
              | None => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | _ => None
  end
  end

(** Dispatch an [expr:apply] whose [func] is a plain [expr:global] and
    isn't [self]: a call to a *sibling* in the enclosing N-way
    mutually-recursive fixgroup (recognized as [RCall], by membership
    in [siblings] -- the whole group's own declared names, known to
    the caller before any member's body is parsed, since [coqc]'s own
    [decl:fixgroup] lists every member up front) takes priority over
    an ordinary intrinsic call, the same way a [self]-call already
    does. *)
with real_call_or_app (self : option var) (siblings : list var) (types : list (string * jvalue)) (fuel : nat) (fname : string) (args : list jvalue)
    {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  if List.existsb (fun s => if string_dec fname s then true else false) siblings then
    match args with
    | [a] =>
        match real_expr_of_json self siblings types fuel' a with
        | Some a' => Some (RCall fname a')
        | None => None
        end
    | [] => None
    | _ =>
        match (fix parse_args (js : list jvalue) : option (list real_expr) :=
                 match js with
                 | [] => Some []
                 | j :: rest =>
                     match real_expr_of_json self siblings types fuel' j, parse_args rest with
                     | Some e', Some es' => Some (e' :: es')
                     | _, _ => None
                     end
                 end) args
        with
        | Some args' => Some (RCallN fname args')
        | None => None
        end
    end
  else real_app_of_json self siblings types fuel' fname args
  end

(** Dispatch an [expr:apply] whose [func] is a plain [expr:global] --
    an intrinsic call ([RApp1]/[RApp2]), arity read off [args]'s own
    length, never guessed. *)
with real_app_of_json (self : option var) (siblings : list var) (types : list (string * jvalue)) (fuel : nat) (fname : string) (args : list jvalue)
    {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  match args with
  | [a] =>
      if string_dec fname "iZR" then
        match z_of_json fuel' a with
        | Some z => Some (RFLit (float_of_Z z))
        | None => None
        end
      else if string_dec fname "q2R" then
        match rational_of_json fuel' a with
        | Some f => Some (RFLit f)
        | None => None
        end
      else
        match real_expr_of_json self siblings types fuel' a with
        | Some a' => Some (RApp1 (resolve_intrinsic_name types fname) a')
        | None => None
        end
  | [a; b] =>
      match real_expr_of_json self siblings types fuel' a, real_expr_of_json self siblings types fuel' b with
      | Some a', Some b' => Some (RApp2 (resolve_intrinsic_name types fname) a' b')
      | _, _ => None
      end
  | _ => None
  end
  end

(** Dispatch an [expr:case]'s [cases] list: a 2-way [True]/[False]
    dispatch is [RIfBool]; a 2-way [Inl]/[Inr] dispatch (each binding
    exactly one name) is [RCase]; a single-case [pat:constructor] that
    binds exactly one non-wildcard name among 2 or 3 fields (the rest
    named ["_"], confirmed directly as the real shape a record field
    projection extracts to) is [RProj1]/[RProj2]/[RProj3_1]/
    [RProj3_2]/[RProj3_3]; a single-case, 2-name [Cons]/[Nil] pair is
    [RListMatch]. *)
with real_case_of_json (self : option var) (siblings : list var) (types : list (string * jvalue)) (fuel : nat) (scrutinee : real_expr) (cases : list jvalue)
    {struct fuel} : option real_expr :=
  match fuel with
  | O => None
  | S fuel' =>
  match cases with
  | [c1] =>
      match c1 with
      | JObject c1fs =>
          match jfield c1fs "pat", jfield c1fs "body" with
          | Some (JObject patfs), Some bodyj =>
              match jname patfs, jfield patfs "argnames" with
              | Some _, Some (JArray [JString "_"; JString x]) =>
                  (* 2-field record, want 2nd *)
                  if is_rel_named bodyj x
                  then Some (RProj2 scrutinee) else None
              | Some _, Some (JArray [JString x; JString "_"]) =>
                  if is_rel_named bodyj x
                  then Some (RProj1 scrutinee) else None
              | Some _, Some (JArray [JString x; JString "_"; JString "_"]) =>
                  if is_rel_named bodyj x then Some (RProj3_1 scrutinee) else None
              | Some _, Some (JArray [JString "_"; JString x; JString "_"]) =>
                  if is_rel_named bodyj x then Some (RProj3_2 scrutinee) else None
              | Some _, Some (JArray [JString "_"; JString "_"; JString x]) =>
                  if is_rel_named bodyj x then Some (RProj3_3 scrutinee) else None
              | Some _, Some (JArray args) =>
                  (* genuinely N-ary field access (N >= 2, any field
                     position), any name not already matched by the
                     fixed-arity cases above -- RProjN, the general
                     replacement for RProj1/RProj2/RProj3_1/RProj3_2/
                     RProj3_3's own one-arity-at-a-time pattern. *)
                  match find_record_field_name 0 args with
                  | Some (x, nskip, last) =>
                      if is_rel_named bodyj x then Some (RProjN nskip last scrutinee) else None
                  | None => None
                  end
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  | [c1; c2] =>
      match c1, c2 with
      | JObject c1fs, JObject c2fs =>
          match jfield c1fs "pat", jfield c1fs "body", jfield c2fs "pat", jfield c2fs "body" with
          | Some (JObject p1), Some b1, Some (JObject p2), Some b2 =>
              match jname p1, jfield p1 "argnames", jname p2, jfield p2 "argnames" with
              | Some "True", Some (JArray []), Some "False", Some (JArray []) =>
                  match real_expr_of_json self siblings types fuel' b1, real_expr_of_json self siblings types fuel' b2 with
                  | Some t, Some e => Some (RIfBool scrutinee t e)
                  | _, _ => None
                  end
              | Some "Inl", Some (JArray [JString x1]), Some "Inr", Some (JArray [JString x2]) =>
                  match real_expr_of_json self siblings types fuel' b1, real_expr_of_json self siblings types fuel' b2 with
                  | Some c1', Some c2' => Some (RCase scrutinee x1 c1' x2 c2')
                  | _, _ => None
                  end
              | Some "Some", Some (JArray [JString x]), Some "None", Some (JArray []) =>
                  (* [option]'s own declaration order in Coq's stdlib
                     ([Some] before [None]) -- confirmed directly to be
                     the order a real match extracts in, even when the
                     source [match] was written [None | Some]. *)
                  match real_expr_of_json self siblings types fuel' b2, real_expr_of_json self siblings types fuel' b1 with
                  | Some nonec, Some somec => Some (ROptionMatch scrutinee nonec x somec)
                  | _, _ => None
                  end
              | Some "None", Some (JArray []), Some "Some", Some (JArray [JString x]) =>
                  match real_expr_of_json self siblings types fuel' b1, real_expr_of_json self siblings types fuel' b2 with
                  | Some nonec, Some somec => Some (ROptionMatch scrutinee nonec x somec)
                  | _, _ => None
                  end
              | Some "Nil", Some (JArray []), Some "Cons", Some (JArray [JString h; JString t]) =>
                  match real_expr_of_json self siblings types fuel' b1, real_expr_of_json self siblings types fuel' b2 with
                  | Some nilc, Some consc => Some (RListMatch scrutinee nilc h t consc)
                  | _, _ => None
                  end
              | Some "Cons", Some (JArray [JString h; JString t]), Some "Nil", Some (JArray []) =>
                  match real_expr_of_json self siblings types fuel' b2, real_expr_of_json self siblings types fuel' b1 with
                  | Some nilc, Some consc => Some (RListMatch scrutinee nilc h t consc)
                  | _, _ => None
                  end
              | _, _, _, _ => None
              end
          | _, _, _, _ => None
          end
      | _, _ => None
      end
  | _ => None
  end
  end.

(* ------------------------------------------------------------------ *)
(** * [jvalue] -> [real_decl] / [real_fix_decl], and finding a
    declaration by name inside a whole extracted module

    A real [coqc] extraction unit is a [module] wrapping a
    [declarations] array that also carries every transitively-needed
    standard-library declaration (confirmed directly, see this file's
    header and [RealIR.v]'s) -- so ingestion always means "parse the
    whole module, then find *this* declaration by name", never "parse
    just one declaration's own text". *)

Definition jstrings_of_json (xs : list jvalue) : option (list var) :=
  (fix go (xs0 : list jvalue) : option (list var) :=
     match xs0 with
     | [] => Some []
     | JString x :: rest =>
         match go rest with
         | Some r => Some (x :: r)
         | None => None
         end
     | _ => None
     end) xs.

Definition real_decl_of_json (types : list (string * jvalue)) (fuel : nat) (argnames : list jvalue) (bodyj : jvalue) : option real_decl :=
  match jstrings_of_json argnames with
  | Some ns =>
      match real_expr_of_json None [] types fuel bodyj with
      | Some body => Some (mk_real_decl ns body)
      | None => None
      end
  | None => None
  end.

(** A [decl:term] node, as it appears directly inside [declarations]. *)
Definition decl_term_of_json (types : list (string * jvalue)) (fuel : nat) (j : jvalue) : option real_decl :=
  match j with
  | JObject fs =>
      match jwhat fs, jfield fs "value" with
      | Some "decl:term", Some (JObject vfs) =>
          match jwhat vfs, jfield vfs "argnames", jfield vfs "body" with
          | Some "expr:lambda", Some (JArray argnames), Some bodyj =>
              real_decl_of_json types fuel argnames bodyj
          | _, _, _ => None
          end
      | _, _ => None
      end
  | _ => None
  end.

(** A [fixgroup:item] node, as it appears inside a [decl:fixgroup]'s
    own [fixlist] -- a single-argument self-recursive [Fixpoint]
    only, [self]-recognized exactly as before ([siblings := []]). For
    the general N-way case, see [decl_fixgroup_of_json] below. *)
Definition decl_fixgroup_item_of_json (types : list (string * jvalue)) (fuel : nat) (j : jvalue) : option real_fix_decl :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "value" with
      | Some "fixgroup:item", Some fname, Some (JObject vfs) =>
          match jwhat vfs, jfield vfs "argnames", jfield vfs "body" with
          | Some "expr:lambda", Some (JArray [JString param]), Some bodyj =>
              match real_expr_of_json (Some fname) [] types fuel bodyj with
              | Some body => Some (mk_real_fix_decl fname param body)
              | None => None
              end
          | _, _, _ => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(** A [fixgroup:item] node with *more than one* [argnames] entry --
    [RealIR.v]'s [real_fix_decl_multi]/[RSelfN] (its header has the
    confirmed-by-probe design). Reads the whole [argnames] list via
    [jstrings_of_json] (already generic, reused unchanged from
    [real_decl_of_json]), rather than requiring exactly one the way
    [decl_fixgroup_item_of_json] does -- that function is left
    untouched for the one-argument case, this is its additive
    sibling. *)
Definition decl_fixgroup_item_multi_of_json (types : list (string * jvalue)) (fuel : nat) (j : jvalue) : option real_fix_decl_multi :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "value" with
      | Some "fixgroup:item", Some fname, Some (JObject vfs) =>
          match jwhat vfs, jfield vfs "argnames", jfield vfs "body" with
          | Some "expr:lambda", Some (JArray argnames), Some bodyj =>
              match jstrings_of_json argnames with
              | Some params =>
                  match real_expr_of_json (Some fname) [] types fuel bodyj with
                  | Some body => Some (mk_real_fix_decl_multi fname params body)
                  | None => None
                  end
              | None => None
              end
          | _, _, _ => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(** A single [fixgroup:item] node, parsed as *one member* of a general
    N-way group: [self := None] ([RealIR.v]'s [real_fix_group_decl]
    deliberately never produces [RSelf] -- see its own comment), and
    [siblings] is the *whole* group's names, known up front from
    [names] (every [fixgroup:item] in a [decl:fixgroup]'s [fixlist]
    is visible before any one member's own body is parsed, so this
    is never a chicken-and-egg problem). *)
Definition fixgroup_item_of_json (siblings : list var) (types : list (string * jvalue)) (fuel : nat) (j : jvalue)
    : option (var * var * real_expr) :=
  match j with
  | JObject fs =>
      match jwhat fs, jname fs, jfield fs "value" with
      | Some "fixgroup:item", Some fname, Some (JObject vfs) =>
          match jwhat vfs, jfield vfs "argnames", jfield vfs "body" with
          | Some "expr:lambda", Some (JArray [JString param]), Some bodyj =>
              match real_expr_of_json None siblings types fuel bodyj with
              | Some body => Some (fname, param, body)
              | None => None
              end
          | _, _, _ => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

(** A [decl:fixgroup] node, as it appears directly inside
    [declarations]: every member's own name is read off [fixlist]
    first ([jname], not re-derived), *then* each member's body is
    parsed against that whole list as [siblings] -- confirmed
    directly against a real extracted [Fixpoint is_even (n : nat) :
    bool := ... with is_odd (n : nat) : bool := ...]: [fixlist] is a
    flat [JArray] of [fixgroup:item]s, group order preserved, no
    separate "names" field to read instead. *)
Definition decl_fixgroup_of_json (types : list (string * jvalue)) (fuel : nat) (j : jvalue) : option real_fix_group_decl :=
  match j with
  | JObject fs =>
      match jwhat fs, jfield fs "fixlist" with
      | Some "decl:fixgroup", Some (JArray items) =>
          match
            (fix names_of (its : list jvalue) : option (list var) :=
               match its with
               | [] => Some []
               | JObject ifs :: rest =>
                   match jname ifs with
                   | Some n => match names_of rest with
                               | Some ns => Some (n :: ns)
                               | None => None
                               end
                   | None => None
                   end
               | _ :: _ => None
               end) items
          with
          | Some siblings =>
              match
                (fix go (its : list jvalue) : option (list (var * var * real_expr)) :=
                   match its with
                   | [] => Some []
                   | it :: rest =>
                       match fixgroup_item_of_json siblings types fuel it, go rest with
                       | Some m, Some ms => Some (m :: ms)
                       | _, _ => None
                       end
                   end) items
              with
              | Some fns => Some (mk_real_fix_group_decl fns)
              | None => None
              end
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.

(** Search a module's [declarations] array for the node named
    [target] -- either a top-level [decl:term], or a [fixgroup:item]
    buried inside some [decl:fixgroup]'s [fixlist] -- returning that
    node itself (not yet interpreted: the caller picks
    [decl_term_of_json] or [decl_fixgroup_item_of_json] depending on
    which shape it expects). *)
Definition find_decl_by_name (decls : list jvalue) (target : string) : option jvalue :=
  (fix go (ds : list jvalue) : option jvalue :=
     match ds with
     | [] => None
     | JObject fs :: rest =>
         match jwhat fs with
         | Some "decl:term" =>
             match jname fs with
             | Some n => if string_dec n target then Some (JObject fs) else go rest
             | None => go rest
             end
         | Some "decl:fixgroup" =>
             match jfield fs "fixlist" with
             | Some (JArray items) =>
                 match
                   (fix find_item (its : list jvalue) : option jvalue :=
                      match its with
                      | [] => None
                      | JObject ifs :: rest' =>
                          match jname ifs with
                          | Some n => if string_dec n target then Some (JObject ifs) else find_item rest'
                          | None => find_item rest'
                          end
                      | _ :: rest' => find_item rest'
                      end) items
                 with
                 | Some it => Some it
                 | None => go rest
                 end
             | _ => go rest
             end
         | _ => go rest
         end
     | _ :: rest => go rest
     end) decls.

(** Like [find_decl_by_name], but for the N-way case: returns the
    *whole* [decl:fixgroup] node containing a member named [target],
    not that member's own [fixgroup:item] -- [decl_fixgroup_of_json]
    needs every member, not just the one the caller happens to ask
    for by name, to resolve any member's calls to any other. A real
    [decl:fixgroup]'s own ["name"] field is [null] for a genuine
    multi-member group (confirmed directly against the [is_even]/
    [is_odd] probe), so group identity is only ever "which members'
    names does it declare", never a name of its own. *)
Definition find_fixgroup_by_member_name (decls : list jvalue) (target : string) : option jvalue :=
  (fix go (ds : list jvalue) : option jvalue :=
     match ds with
     | [] => None
     | JObject fs :: rest =>
         match jwhat fs with
         | Some "decl:fixgroup" =>
             match jfield fs "fixlist" with
             | Some (JArray items) =>
                 if (fix any_named (its : list jvalue) : bool :=
                       match its with
                       | [] => false
                       | JObject ifs :: rest' =>
                           match jname ifs with
                           | Some n => if string_dec n target then true else any_named rest'
                           | None => any_named rest'
                           end
                       | _ :: rest' => any_named rest'
                       end) items
                 then Some (JObject fs)
                 else go rest
             | _ => go rest
             end
         | _ => go rest
         end
     | _ :: rest => go rest
     end) decls.

Definition module_declarations (s : string) : option (list jvalue) :=
  match parse_json s with
  | Some (JObject mfs) =>
      match jwhat mfs, jfield mfs "declarations" with
      | Some "module", Some (JArray decls) => Some decls
      | _, _ => None
      end
  | _ => None
  end.

(** The two top-level entry points: parse a whole real [coqc]
    [Extraction Language JSON] module ([s]) and pull out one
    non-recursive ([real_decl_of_module_json]) or self-recursive
    ([real_fix_decl_of_module_json]) declaration by name. *)
Definition real_decl_of_module_json (s target : string) : option real_decl :=
  match module_declarations s with
  | Some decls =>
      match find_decl_by_name decls target with
      | Some declj => decl_term_of_json (module_decl_types decls) (S (String.length s)) declj
      | None => None
      end
  | None => None
  end.

Definition real_fix_decl_of_module_json (s target : string) : option real_fix_decl :=
  match module_declarations s with
  | Some decls =>
      match find_decl_by_name decls target with
      | Some declj => decl_fixgroup_item_of_json (module_decl_types decls) (S (String.length s)) declj
      | None => None
      end
  | None => None
  end.

(** Like [real_fix_decl_of_module_json], but for a self-recursive
    [Fixpoint] of *more than one* argument. *)
Definition real_fix_decl_multi_of_module_json (s target : string) : option real_fix_decl_multi :=
  match module_declarations s with
  | Some decls =>
      match find_decl_by_name decls target with
      | Some declj => decl_fixgroup_item_multi_of_json (module_decl_types decls) (S (String.length s)) declj
      | None => None
      end
  | None => None
  end.

(** A third entry point, for a general N-way mutually-recursive
    [decl:fixgroup]: [target] names any *one* member (the caller's
    point of entry), but the result carries the *whole* group. *)
Definition real_fix_group_decl_of_module_json (s target : string) : option real_fix_group_decl :=
  match module_declarations s with
  | Some decls =>
      match find_fixgroup_by_member_name decls target with
      | Some declj => decl_fixgroup_of_json (module_decl_types decls) (S (String.length s)) declj
      | None => None
      end
  | None => None
  end.
