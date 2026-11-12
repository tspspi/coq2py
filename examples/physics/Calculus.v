(** Calculus.v

    A symbolic (syntactic) multivariable calculus layer for spacetime
    fields -- second module of a larger worked example built on
    Minkowski.v (see docs/roadmap.md).

    A [field] is a small expression language over named base quantities
    ("atoms", e.g. a component of the electric field), closed under +, -,
    *, negation, and partial differentiation with respect to each of the
    four spacetime coordinates. Partial differentiation acts on an atom
    by recording, in its multi-index, how many times it has been
    differentiated with respect to each coordinate; it acts on compound
    expressions by the usual linearity and product rules, built directly
    into its definition rather than proved as separate lemmas (there is
    nothing to prove: the recursive cases of [pderiv] *are* those rules).

    The one genuinely nontrivial fact proved here is commutativity of
    mixed partial derivatives ([pderiv_comm], the symbolic counterpart of
    Schwarz's theorem). Unlike a limit-based definition of the derivative
    (for which this would be a real theorem about smooth functions,
    itself requiring a substantial piece of real analysis to prove), it
    is simply true by construction here: differentiating twice updates
    two independent components of a multi-index record, in either order,
    to the same result -- [bump_comm] closes by case analysis alone, no
    induction, no analysis.

    [field] values are given meaning by [feval], an interpretation
    relative to an arbitrary assignment of real numbers to each
    (atom name, multi-index) pair. Every theorem below is stated as an
    equation between the [feval] of two field expressions, not as
    equality of the expressions themselves (which in general differ as
    syntax trees even when they denote the same value -- e.g. [FAdd a b]
    and [FAdd b a]). This is the same deep-embedding pattern used
    throughout the rest of this repository: encode syntax, prove
    properties of its denotation.

    The explicit, accepted correspondence this module does not prove --
    structurally the same kind of boundary documented for the main
    extraction pipeline in docs/duality.md -- is that [feval] under some
    assignment faithfully represents a genuine smooth real-valued
    function of (t, x, y, z) and its actual partial derivatives at a
    point. Nothing here is axiomatized to make that true; it is simply
    the intended reading of the symbols, stated once, here, rather than
    threaded as a hypothesis through every lemma. *)

From Coq Require Import Reals String.
Open Scope R_scope.

Inductive coord := CT | CX | CY | CZ.

Record multideg := mkdeg { dt : nat; dxd : nat; dyd : nat; dzd : nat }.

Inductive field : Type :=
  | FConst (c : R)
  | FAtom (name : string) (deg : multideg)
  | FAdd (a b : field)
  | FSub (a b : field)
  | FMul (a b : field)
  | FOpp (a : field).

Definition bump (c : coord) (d : multideg) : multideg :=
  match c with
  | CT => mkdeg (S (dt d)) (dxd d) (dyd d) (dzd d)
  | CX => mkdeg (dt d) (S (dxd d)) (dyd d) (dzd d)
  | CY => mkdeg (dt d) (dxd d) (S (dyd d)) (dzd d)
  | CZ => mkdeg (dt d) (dxd d) (dyd d) (S (dzd d))
  end.

Lemma bump_comm : forall c1 c2 d, bump c1 (bump c2 d) = bump c2 (bump c1 d).
Proof. intros c1 c2 d; destruct c1, c2, d; reflexivity. Qed.

Fixpoint pderiv (c : coord) (f : field) : field :=
  match f with
  | FConst _ => FConst 0
  | FAtom name deg => FAtom name (bump c deg)
  | FAdd a b => FAdd (pderiv c a) (pderiv c b)
  | FSub a b => FSub (pderiv c a) (pderiv c b)
  | FMul a b => FAdd (FMul (pderiv c a) b) (FMul a (pderiv c b))
  | FOpp a => FOpp (pderiv c a)
  end.

Definition assign_t := string -> multideg -> R.

Fixpoint feval (assign : assign_t) (f : field) : R :=
  match f with
  | FConst c => c
  | FAtom name deg => assign name deg
  | FAdd a b => feval assign a + feval assign b
  | FSub a b => feval assign a - feval assign b
  | FMul a b => feval assign a * feval assign b
  | FOpp a => - feval assign a
  end.

Theorem pderiv_comm :
  forall c1 c2 assign f, feval assign (pderiv c1 (pderiv c2 f)) = feval assign (pderiv c2 (pderiv c1 f)).
Proof.
  intros c1 c2 assign f.
  induction f as [c | name deg | a IHa b IHb | a IHa b IHb | a IHa b IHb | a IHa]; simpl.
  - reflexivity.
  - rewrite bump_comm. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. ring.
  - rewrite IHa. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** * Vector calculus over the three spatial coordinates *)

Record vfield := mkvfield { fx : field; fy : field; fz : field }.

Definition vadd (A B : vfield) : vfield :=
  mkvfield (FAdd (fx A) (fx B)) (FAdd (fy A) (fy B)) (FAdd (fz A) (fz B)).

Definition vsub (A B : vfield) : vfield :=
  mkvfield (FSub (fx A) (fx B)) (FSub (fy A) (fy B)) (FSub (fz A) (fz B)).

Definition vscale (c : R) (A : vfield) : vfield :=
  mkvfield (FMul (FConst c) (fx A)) (FMul (FConst c) (fy A)) (FMul (FConst c) (fz A)).

(** Derivative with respect to any one of the four spacetime coordinates
    (including time, [CT]), applied component-wise. *)
Definition vderiv (c : coord) (V : vfield) : vfield :=
  mkvfield (pderiv c (fx V)) (pderiv c (fy V)) (pderiv c (fz V)).

Definition div (V : vfield) : field :=
  FAdd (FAdd (pderiv CX (fx V)) (pderiv CY (fy V))) (pderiv CZ (fz V)).

Definition curl (V : vfield) : vfield :=
  mkvfield (FSub (pderiv CY (fz V)) (pderiv CZ (fy V)))
           (FSub (pderiv CZ (fx V)) (pderiv CX (fz V)))
           (FSub (pderiv CX (fy V)) (pderiv CY (fx V))).

Definition grad (f : field) : vfield :=
  mkvfield (pderiv CX f) (pderiv CY f) (pderiv CZ f).

Definition laplacian (f : field) : field :=
  FAdd (FAdd (pderiv CX (pderiv CX f)) (pderiv CY (pderiv CY f))) (pderiv CZ (pderiv CZ f)).

Definition vlaplacian (V : vfield) : vfield :=
  mkvfield (laplacian (fx V)) (laplacian (fy V)) (laplacian (fz V)).

(** Component-wise semantic equality of vector fields. *)
Definition veq (assign : assign_t) (A B : vfield) : Prop :=
  feval assign (fx A) = feval assign (fx B) /\
  feval assign (fy A) = feval assign (fy B) /\
  feval assign (fz A) = feval assign (fz B).

(** The two standard "trivial" vector identities: the divergence of a
    curl, and the curl of a gradient, both vanish. Each reduces to one
    application of [pderiv_comm] per component. *)
Theorem div_curl_zero : forall assign V, feval assign (div (curl V)) = 0.
Proof.
  intros assign V. unfold div, curl; simpl.
  rewrite (pderiv_comm CX CY assign (fz V)).
  rewrite (pderiv_comm CY CZ assign (fx V)).
  rewrite (pderiv_comm CZ CX assign (fy V)).
  ring.
Qed.

Theorem curl_grad_zero : forall assign f, veq assign (curl (grad f)) (mkvfield (FConst 0) (FConst 0) (FConst 0)).
Proof.
  intros assign f. unfold veq, curl, grad; simpl.
  rewrite (pderiv_comm CY CZ assign f).
  rewrite (pderiv_comm CZ CX assign f).
  rewrite (pderiv_comm CX CY assign f).
  repeat split; ring.
Qed.

(** The double-curl ("BAC-CAB") identity: [curl (curl V) = grad (div V) - laplacian V].
    This is the one piece of vector calculus the wave-equation derivation
    (Maxwell.v) actually needs. *)
Theorem curl_curl :
  forall assign V, veq assign (curl (curl V)) (vsub (grad (div V)) (vlaplacian V)).
Proof.
  intros assign V. unfold veq, curl, grad, div, laplacian; simpl.
  repeat split.
  - rewrite (pderiv_comm CX CY assign (fy V)).
    rewrite (pderiv_comm CZ CX assign (fz V)).
    ring.
  - rewrite (pderiv_comm CY CZ assign (fz V)).
    rewrite (pderiv_comm CX CY assign (fx V)).
    ring.
  - rewrite (pderiv_comm CZ CX assign (fx V)).
    rewrite (pderiv_comm CY CZ assign (fy V)).
    ring.
Qed.
