(** Minkowski.v

    Minkowski spacetime and the group of linear transformations preserving
    its bilinear form (the Lorentz group), as linear algebra over the
    standard library's [R] (`Coq.Reals`, already part of `coq-stdlib`,
    not a new dependency). First module of a larger worked example
    (symmetry -> Maxwell's equations -> the electromagnetic wave equation
    -> a discretized, extracted, visualized simulator); see
    docs/roadmap.md.

    4-vectors and 4x4 matrices are represented directly as records of
    four components / four row-vectors rather than via a general matrix
    library, since the fixed dimension (4) makes every operation a
    concrete, finite expansion: every lemma below reduces, after peeling
    the record constructors with [f_equal], to a handful of goals over
    [R] closed by [ring] (or [nra] where the Lorentz boost's defining
    constraint is needed). None of this module uses any axiom beyond
    `coq-stdlib`'s own axiomatization of the real numbers. *)

From Coq Require Import Reals Lra.
Open Scope R_scope.

Record vec4 := mkvec4 { v0 : R; v1 : R; v2 : R; v3 : R }.

Record mat4 := mkmat4 { r0 : vec4; r1 : vec4; r2 : vec4; r3 : vec4 }.

Definition dot (a b : vec4) : R :=
  v0 a * v0 b + v1 a * v1 b + v2 a * v2 b + v3 a * v3 b.

Definition mtranspose (M : mat4) : mat4 :=
  mkmat4 (mkvec4 (v0 (r0 M)) (v0 (r1 M)) (v0 (r2 M)) (v0 (r3 M)))
         (mkvec4 (v1 (r0 M)) (v1 (r1 M)) (v1 (r2 M)) (v1 (r3 M)))
         (mkvec4 (v2 (r0 M)) (v2 (r1 M)) (v2 (r2 M)) (v2 (r3 M)))
         (mkvec4 (v3 (r0 M)) (v3 (r1 M)) (v3 (r2 M)) (v3 (r3 M))).

Definition mmul (A B : mat4) : mat4 :=
  let Bt := mtranspose B in
  mkmat4 (mkvec4 (dot (r0 A) (r0 Bt)) (dot (r0 A) (r1 Bt)) (dot (r0 A) (r2 Bt)) (dot (r0 A) (r3 Bt)))
         (mkvec4 (dot (r1 A) (r0 Bt)) (dot (r1 A) (r1 Bt)) (dot (r1 A) (r2 Bt)) (dot (r1 A) (r3 Bt)))
         (mkvec4 (dot (r2 A) (r0 Bt)) (dot (r2 A) (r1 Bt)) (dot (r2 A) (r2 Bt)) (dot (r2 A) (r3 Bt)))
         (mkvec4 (dot (r3 A) (r0 Bt)) (dot (r3 A) (r1 Bt)) (dot (r3 A) (r2 Bt)) (dot (r3 A) (r3 Bt))).

Definition mscale (c : R) (A : mat4) : mat4 :=
  mkmat4 (mkvec4 (c * v0 (r0 A)) (c * v1 (r0 A)) (c * v2 (r0 A)) (c * v3 (r0 A)))
         (mkvec4 (c * v0 (r1 A)) (c * v1 (r1 A)) (c * v2 (r1 A)) (c * v3 (r1 A)))
         (mkvec4 (c * v0 (r2 A)) (c * v1 (r2 A)) (c * v2 (r2 A)) (c * v3 (r2 A)))
         (mkvec4 (c * v0 (r3 A)) (c * v1 (r3 A)) (c * v2 (r3 A)) (c * v3 (r3 A))).

Definition mneg (A : mat4) : mat4 := mscale (-1) A.

Definition identity4 : mat4 :=
  mkmat4 (mkvec4 1 0 0 0) (mkvec4 0 1 0 0) (mkvec4 0 0 1 0) (mkvec4 0 0 0 1).

(* ----------------------------------------------------------------- *)
(** * General matrix algebra facts, reused throughout the proofs below *)

Lemma mtranspose_mmul : forall A B, mtranspose (mmul A B) = mmul (mtranspose B) (mtranspose A).
Proof. intros A B. unfold mtranspose, mmul, dot; simpl. f_equal; f_equal; ring. Qed.

Lemma mtranspose_involutive : forall A, mtranspose (mtranspose A) = A.
Proof.
  intro A. unfold mtranspose.
  destruct A as [[a0 a1 a2 a3] [b0 b1 b2 b3] [c0 c1 c2 c3] [d0 d1 d2 d3]]; reflexivity.
Qed.

Lemma mmul_assoc : forall A B C, mmul (mmul A B) C = mmul A (mmul B C).
Proof. intros A B C. unfold mmul, mtranspose, dot; simpl. f_equal; f_equal; ring. Qed.

Lemma mmul_identity_l : forall A, mmul identity4 A = A.
Proof.
  intro A. unfold mmul, mtranspose, dot, identity4; simpl.
  destruct A as [[a0 a1 a2 a3] [b0 b1 b2 b3] [c0 c1 c2 c3] [d0 d1 d2 d3]]; simpl.
  f_equal; f_equal; ring.
Qed.

Lemma mmul_identity_r : forall A, mmul A identity4 = A.
Proof.
  intro A. unfold mmul, mtranspose, dot, identity4; simpl.
  destruct A as [[a0 a1 a2 a3] [b0 b1 b2 b3] [c0 c1 c2 c3] [d0 d1 d2 d3]]; simpl.
  f_equal; f_equal; ring.
Qed.

Lemma mtranspose_identity : mtranspose identity4 = identity4.
Proof. reflexivity. Qed.

Lemma mtranspose_mscale : forall c A, mtranspose (mscale c A) = mscale c (mtranspose A).
Proof.
  intros c A. unfold mtranspose, mscale.
  destruct A as [[a0 a1 a2 a3] [b0 b1 b2 b3] [c0 c1 c2 c3] [d0 d1 d2 d3]]; reflexivity.
Qed.

Lemma mmul_mscale_r : forall A c B, mmul A (mscale c B) = mscale c (mmul A B).
Proof. intros A c B. unfold mmul, mtranspose, mscale, dot; simpl. f_equal; f_equal; ring. Qed.

Lemma mmul_mscale_l : forall c A B, mmul (mscale c A) B = mscale c (mmul A B).
Proof. intros c A B. unfold mmul, mtranspose, mscale, dot; simpl. f_equal; f_equal; ring. Qed.

(* ----------------------------------------------------------------- *)
(** * The Minkowski metric and the Lorentz group *)

(** Signature (+,-,-,-), units where c = 1. *)
Definition eta : mat4 :=
  mkmat4 (mkvec4 1 0 0 0) (mkvec4 0 (-1) 0 0) (mkvec4 0 0 (-1) 0) (mkvec4 0 0 0 (-1)).

(** A matrix preserves the Minkowski bilinear form: [Lambda^T eta Lambda = eta].
    The Lorentz group is exactly the set of matrices satisfying this. *)
Definition preserves_eta (M : mat4) : Prop :=
  mmul (mmul (mtranspose M) eta) M = eta.

Theorem identity_preserves_eta : preserves_eta identity4.
Proof.
  unfold preserves_eta.
  rewrite mtranspose_identity, mmul_identity_l, mmul_identity_r.
  reflexivity.
Qed.

(** The set of metric-preserving matrices is closed under composition --
    the defining closure property of a group, here for the specific
    operation ([mmul]) and predicate ([preserves_eta]) at hand. *)
Theorem lorentz_closed :
  forall A B, preserves_eta A -> preserves_eta B -> preserves_eta (mmul A B).
Proof.
  intros A B HA HB.
  unfold preserves_eta in *.
  rewrite mtranspose_mmul.
  rewrite mmul_assoc.
  rewrite mmul_assoc.
  rewrite <- (mmul_assoc (mtranspose A) eta (mmul A B)).
  rewrite <- (mmul_assoc (mmul (mtranspose A) eta) A B).
  rewrite HA.
  rewrite <- mmul_assoc.
  exact HB.
Qed.

(* ----------------------------------------------------------------- *)
(** * Action on antisymmetric rank-2 tensors *)

(** The electromagnetic field tensor is antisymmetric: [F^T = -F]. This
    predicate does not depend on any particular choice of E/B components
    -- that correspondence belongs to a later module, once a calculus
    layer exists to index components meaningfully. *)
Definition antisymmetric (F : mat4) : Prop := mtranspose F = mneg F.

(** The group action on a rank-2 tensor, [Lambda F Lambda^T], preserves
    antisymmetry: a Lorentz-transformed field tensor is again a valid
    field tensor. *)
Theorem lorentz_preserves_antisymmetry :
  forall Lambda F, antisymmetric F -> antisymmetric (mmul (mmul Lambda F) (mtranspose Lambda)).
Proof.
  intros Lambda F HF.
  unfold antisymmetric in *.
  rewrite mtranspose_mmul.
  rewrite mtranspose_involutive.
  rewrite mtranspose_mmul.
  rewrite HF.
  unfold mneg.
  rewrite mmul_mscale_l.
  rewrite mmul_mscale_r.
  rewrite <- mmul_assoc.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** * A concrete Lorentz transformation: the boost along x *)

(** Parametrized directly by [gamma]/[beta] subject to their defining
    relation [gamma^2 (1 - beta^2) = 1], rather than deriving [gamma]
    from a velocity via [sqrt] -- the relation is exactly what the proof
    below needs, and avoids pulling in `Coq.Reals.R_sqrt`'s lemmas for no
    further benefit here. *)
Definition boost_x (gamma beta : R) : mat4 :=
  mkmat4 (mkvec4 gamma (- gamma * beta) 0 0)
         (mkvec4 (- gamma * beta) gamma 0 0)
         (mkvec4 0 0 1 0)
         (mkvec4 0 0 0 1).

Theorem boost_x_preserves_eta :
  forall gamma beta, gamma * gamma * (1 - beta * beta) = 1 -> preserves_eta (boost_x gamma beta).
Proof.
  intros gamma beta Hc.
  unfold preserves_eta, boost_x, mtranspose, mmul, dot, eta; simpl.
  f_equal; f_equal; nra.
Qed.
