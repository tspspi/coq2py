(** * A first, explicit step toward Coquelicot support: a computable
    real-number model with a stated (not silently assumed) correspondence
    to Coq's classical [R].

    [docs/roadmap.md]'s Coquelicot section names the prerequisite this file
    addresses: before [RealIR.v] can recognize any Coquelicot-adjacent
    source code, something has to say what a recognized real-valued
    expression actually *means* computationally, since [R] itself has none
    -- it's Dedekind-cut/Cauchy-style and axiomatic. This was confirmed
    directly, not just argued: extracting a genuine, Coquelicot-proven
    `R -> R` function (`quad x := x * x + 1`, with `is_derive quad x (2*x)`
    proved via Coquelicot's [auto_derive]) pulls in a 350KB JSON blob of
    [ClassicalDedekindReals]'s own internal cut representation and an
    axiom-to-realize ([sig_forall_dec]) -- versus a few bytes for the
    equivalent [Z] function. [R]'s *own* operations ([Rplus]/[Rmult]/...)
    have no extractable body; only the *call sites* of a handful of
    well-known names (confirmed in the same probe: the extracted body of
    `quad` itself is a clean `rplus (rmult x x) (iZR 1)`, exactly the
    [RApp2]-shaped intrinsic-call pattern [RealIR.v] already recognizes for
    [Z.add]/[Z.ltb]) are usable at all -- the same "ignore the extracted
    body of a well-known primitive" move this project's [RealIR.v] already
    makes for [Z], just confirmed to hold for [R] too.

    This project already has a genuinely computable real-number stand-in:
    [PrimFloat.float]/[Lang.v]'s [VFloat]. The model chosen here is
    [R_of_float] : the real number a finite float's own [Prim2SF]
    decomposition exactly denotes ([(-1)^sign * mantissa * 2^exponent],
    [Json.v]'s own convention, reused verbatim). This is a genuine
    [Definition], not an axiom -- interpreting a float's bit pattern as a
    real number is exact arithmetic, nothing to assume.

    What IS assumed, explicitly, below: whether [PrimFloat]'s [+]/[*]
    *compute* the correctly-rounded result of real [+]/[*] under this
    correspondence. For the rounding-free operations ([-]/[abs], a sign-bit
    flip/clear in IEEE-754) this is proved outright, no axiom, directly
    from the stdlib's own [opp_spec]/[abs_spec]. For [+]/[*], real rounding
    is unavoidably involved; proving the standard relative-error bound from
    [SpecFloat]'s own rounding definitions is exactly what Flocq exists to
    do, and re-deriving Flocq-scale numerical-analysis machinery here would
    be a new, nontrivial dependency this project's policy
    ([docs/roadmap.md]'s [Z]/[PrimFloat] sections) deliberately avoids. So
    [R_of_float_add_rounded]/[R_of_float_mul_rounded] state the standard
    IEEE-754 binary64 round-to-nearest relative-error bound (unit roundoff
    [2^-53]) as explicit [Axiom]s -- assumed, not proved, and named so a
    reader can see exactly where the unproved step is, the same trust-
    boundary category [docs/duality.md] already uses for "does
    [PrimFloat.float] arithmetic actually match IEEE-754" and for
    [SF2Prim_Prim2SF] itself.

    [Print Assumptions] on the two proved lemmas below shows only
    already-existing axioms: [PrimFloat]'s own primitives (opaque, the same
    set [Extract.v]'s header already documents), and [R]'s inherent
    classical axioms ([ClassicalDedekindReals.sig_forall_dec],
    [FunctionalExtensionality.functional_extensionality_dep]) -- these are
    not new; any use of Coq's [Reals] library at all carries them, since
    [R] is built classically. Nothing new is silently introduced here.

    Not yet done (tracked in [docs/roadmap.md]): actually extending
    [RealIR.v]'s recognizer to use this bridge and recognize a real
    Coquelicot-adjacent [real_expr] fragment ([R] literals, [Rplus]/
    [Rmult]/[Rminus]/[Ropp] by intrinsic name, translating into [EFConst]/
    [EFAdd]/[EFMul]/... via [R_of_float]) -- this file only lays the
    foundation the roadmap says has to exist first. *)

From Coq Require Import Floats.PrimFloat Floats.FloatOps Floats.SpecFloat Floats.FloatAxioms.
From Coq Require Import Reals.
From Coq Require Import Lia Lra.
Open Scope R_scope.

(** Whether a float's own [spec_float] decomposition is neither [nan] nor
    an infinity -- the side condition every lemma/axiom below that talks
    about a float's *real value* is stated under. ([zero] counts as
    finite: it has an exact, well-defined real value, [0].) *)
Definition is_finite_sf (sf : spec_float) : bool :=
  match sf with
  | S754_nan | S754_infinity _ => false
  | _ => true
  end.

Definition is_finite (x : PrimFloat.float) : bool := is_finite_sf (Prim2SF x).

(** The real value a [spec_float] decomposition exactly denotes, per
    [Json.v]'s own convention. [infinity]/[nan] have no real value; mapped
    to [0] here purely so the function is total -- every fact below that
    needs this to mean something is stated under an explicit [is_finite]
    hypothesis, so this choice is never actually relied on. *)
Definition R_of_spec_float (sf : spec_float) : R :=
  match sf with
  | S754_zero _ => 0
  | S754_infinity _ => 0
  | S754_nan => 0
  | S754_finite sign mantissa exponent =>
      let v := IZR (Zpos mantissa) * powerRZ 2 exponent in
      if sign then (- v) else v
  end.

(** The real value a finite [PrimFloat.float] exactly denotes. *)
Definition R_of_float (x : PrimFloat.float) : R :=
  R_of_spec_float (Prim2SF x).

Lemma R_of_float_zero : R_of_float 0%float = 0.
Proof. reflexivity. Qed.

(** Negation is a sign-bit flip in IEEE-754 -- exact, no rounding, no
    axiom needed: this follows directly from the stdlib's own [opp_spec]. *)
Lemma R_of_float_opp : forall x : PrimFloat.float,
  R_of_float (- x)%float = (- R_of_float x).
Proof.
  intro x.
  unfold R_of_float.
  rewrite opp_spec.
  destruct (Prim2SF x) as [s|s| |s m e]; simpl; try ring.
  destruct s; simpl; ring.
Qed.

(** Absolute value is a sign-bit clear in IEEE-754 -- exact, no rounding,
    no axiom needed: this follows directly from the stdlib's own
    [abs_spec]. *)
Lemma R_of_float_abs : forall x : PrimFloat.float,
  R_of_float (PrimFloat.abs x) = Rabs (R_of_float x).
Proof.
  intro x.
  unfold R_of_float.
  rewrite abs_spec.
  destruct (Prim2SF x) as [s|s| |s m e]; simpl.
  - rewrite Rabs_R0. reflexivity.
  - rewrite Rabs_R0. reflexivity.
  - rewrite Rabs_R0. reflexivity.
  - destruct s; simpl.
    + rewrite Rabs_Ropp, Rabs_right; [reflexivity | apply Rle_ge].
      apply Rmult_le_pos; [apply IZR_le; lia | apply powerRZ_le; lra].
    + rewrite Rabs_right; [reflexivity | apply Rle_ge].
      apply Rmult_le_pos; [apply IZR_le; lia | apply powerRZ_le; lra].
Qed.

(** Binary64's unit roundoff (53-bit significand): the standard IEEE-754
    round-to-nearest relative-error bound. *)
Definition ulp53 : R := / (powerRZ 2 53).

(** Assumed, not proved (see the file header): the standard fact that
    [PrimFloat]'s [+] computes the correctly-rounded result of real [+]
    under [R_of_float], i.e. [fl(x+y) = (x+y)(1+delta)] with
    [|delta| <= ulp53] -- the textbook IEEE-754 round-to-nearest model.
    Proving this from [SpecFloat]'s own rounding definitions is exactly
    what Flocq exists to do; not re-derived here, per this project's
    dependency policy. *)
Axiom R_of_float_add_rounded :
  forall x y : PrimFloat.float,
    is_finite x = true -> is_finite y = true -> is_finite (x + y)%float = true ->
    exists delta : R,
      Rabs delta <= ulp53 /\
      R_of_float (x + y)%float = (R_of_float x + R_of_float y) * (1 + delta).

(** Same as [R_of_float_add_rounded], for [*]. *)
Axiom R_of_float_mul_rounded :
  forall x y : PrimFloat.float,
    is_finite x = true -> is_finite y = true -> is_finite (x * y)%float = true ->
    exists delta : R,
      Rabs delta <= ulp53 /\
      R_of_float (x * y)%float = (R_of_float x * R_of_float y) * (1 + delta).
