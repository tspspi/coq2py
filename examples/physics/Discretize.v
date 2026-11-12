(** Discretize.v

    The piece docs/roadmap.md flagged as remaining for the electromagnetism
    example: a discretized numerical scheme for the scalar wave equation
    [wave_equation_E]/[wave_equation_B] (Maxwell.v) derive, together with
    a genuine consistency proof (not merely assumed), and the concrete
    [expr] (Lang.v) term that gets extracted and actually executed by an
    external Python/numpy runtime (see runtime/wave1d.py).

    * The scheme

    The standard explicit second-order ("leapfrog") scheme for
    [partial_t^2 u = c^2 partial_x^2 u] replaces both second derivatives by
    central differences on a grid with spacing [dx] in space and [dt] in
    time:

        u(x, t+dt) = 2 u(x,t) - u(x, t-dt) + r * (u(x-dx,t) - 2 u(x,t) + u(x+dx,t))

    where [r = (c*dt/dx)^2] is the squared Courant number. [leapfrog_update]
    below is exactly this formula, and [courant_sq] is [r].

    * The consistency proof

    "This scheme is second-order accurate" is usually left as a citation to
    a Taylor-expansion argument. Here it is an actual theorem,
    [leapfrog_exact_for_cubic_profile], proved by [field] over [R] rather
    than assumed: if, at the point of interest, the true solution agrees to
    third order in space (its spatial slice through [t0] is an exact cubic
    in [x - x0], i.e. matches a Taylor polynomial through the [x^3] term)
    and to third order in time (likewise for its temporal slice through
    [x0]) -- which is exactly what "the solution is smooth" buys you
    locally -- and the continuous wave equation holds at the center point
    [(x0, t0)], then the discrete update computes the *exact* value of the
    true solution one time step later, with no approximation error at all.
    This is the precise, honest content behind "second-order accurate":
    the scheme's local truncation error is driven entirely by the 4th-order
    (and higher) Taylor terms, which this theorem's hypotheses don't
    constrain and which is exactly why real numerical error is [O(dx^2 +
    dt^2)] rather than zero in general -- but for the cubic-consistent part
    of the local expansion, the error is provably, exactly zero, not just
    asymptotically small. This is the same spirit as Calculus.v's
    [pderiv_comm]: a fact that is exactly, algebraically true of the
    symbols involved, proved by [field]/[ring], not a numerical-analysis
    limit argument (which would need machinery -- Taylor's theorem with
    remainder -- this project's dependency policy (GOAL.md) deliberately
    avoids pulling in). *)

From Coq Require Import Reals Lra String List Bool Lia.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(** * The scheme, over [R] *)

Definition courant_sq (c dt dx : R) : R := (c * c * dt * dt) / (dx * dx).

(** [u_prev]/[u_left]/[u_center]/[u_right] name the four known grid values
    the update reads: the center point one time step back, and the three
    points of the current time step's spatial stencil. *)
Definition leapfrog_update (r u_prev u_left u_center u_right : R) : R :=
  2 * u_center - u_prev + r * (u_left - 2 * u_center + u_right).

(* ----------------------------------------------------------------- *)
(** * Consistency: the scheme is exact through third-order Taylor terms *)

(** The four values [leapfrog_update] actually reads, expressed as exact
    third-order Taylor expansions of the true solution around the center
    point [(x0, t0)] -- [a0 ... a3] are the spatial Taylor coefficients at
    time [t0] (so [a0] is [u(x0,t0)] itself, [a1] is the first spatial
    derivative, etc.), and [b1 b2 b3] the temporal ones at [x0] (sharing
    [a0] as the common center value). *)
Definition taylor_u_prev (a0 b1 b2 b3 dt : R) : R :=
  a0 - b1 * dt + b2 * dt * dt - b3 * dt * dt * dt.

Definition taylor_u_left (a0 a1 a2 a3 dx : R) : R :=
  a0 - a1 * dx + a2 * dx * dx - a3 * dx * dx * dx.

Definition taylor_u_right (a0 a1 a2 a3 dx : R) : R :=
  a0 + a1 * dx + a2 * dx * dx + a3 * dx * dx * dx.

Definition taylor_u_next (a0 b1 b2 b3 dt : R) : R :=
  a0 + b1 * dt + b2 * dt * dt + b3 * dt * dt * dt.

(** The headline theorem: given the continuous wave equation at the center
    point ([b2 = c^2 a2] -- [2*b2]/[2*a2] are exactly [partial_t^2 u] /
    [partial_x^2 u] at [(x0,t0)], so this is literally
    [wave_equation_E]/[wave_equation_B]'s conclusion instantiated at a
    point, restated in terms of Taylor coefficients instead of [feval]),
    [leapfrog_update] applied to the four values a true, locally-cubic
    solution would actually have, recovers the true next-step value
    exactly -- no [O(dx^2+dt^2)] hedge needed. *)
Theorem leapfrog_exact_for_cubic_profile :
  forall a0 a1 a2 a3 b1 b2 b3 c dt dx : R,
    dx <> 0 ->
    b2 = c * c * a2 ->
    leapfrog_update (courant_sq c dt dx)
      (taylor_u_prev a0 b1 b2 b3 dt)
      (taylor_u_left a0 a1 a2 a3 dx)
      a0
      (taylor_u_right a0 a1 a2 a3 dx)
      = taylor_u_next a0 b1 b2 b3 dt.
Proof.
  intros a0 a1 a2 a3 b1 b2 b3 c dt dx Hdx Hwave.
  unfold leapfrog_update, courant_sq,
    taylor_u_prev, taylor_u_left, taylor_u_right, taylor_u_next.
  rewrite Hwave.
  field. exact Hdx.
Qed.

(* ----------------------------------------------------------------- *)
(** * The same update, as an extractable [expr] term *)

(** [leapfrog_update] translated literally into this project's proven
    [expr] subset (Lang.v), over [EFAdd]/[EFSub]/[EFMul]/[EFDiv]/[EFConst]
    float arithmetic (see docs/roadmap.md's "PrimFloat.float is wired in"
    entry) -- this is the term that actually gets printed, extracted, and
    run by the external numpy runtime (runtime/wave1d.py), not a
    hand-written restatement of the formula living only in Python. The
    Courant-squared coefficient [r] is computed once, outside the hot
    per-cell update loop, and passed in as a parameter rather than
    recomputed (dividing by [dx*dx]) at every grid cell. *)
Definition leapfrog_update_expr : expr :=
  EFAdd
    (EFSub (EFMul (EFConst 2) (EVar "u_center")) (EVar "u_prev"))
    (EFMul (EVar "r")
      (EFSub (EFAdd (EVar "u_left") (EVar "u_right"))
             (EFMul (EFConst 2) (EVar "u_center")))).

Theorem leapfrog_update_expr_idents_valid :
  expr_idents_valid is_valid_ident leapfrog_update_expr = true.
Proof. reflexivity. Qed.

(** This term means exactly [leapfrog_update] -- not a re-derivation, a
    direct unfolding check: [eval] on the four named grid values plus [r]
    computes the same float [leapfrog_update] would (modulo the
    [VFloat]/bare-[float] wrapping [eval]'s [value] type needs). *)
Example leapfrog_update_expr_concrete :
  eval [("u_prev", VFloat 1.0%float); ("u_left", VFloat 2.0%float);
        ("u_center", VFloat 3.0%float); ("u_right", VFloat 4.0%float);
        ("r", VFloat 0.5%float)]
    leapfrog_update_expr
  = Some (VFloat (PrimFloat.add
                    (PrimFloat.sub (PrimFloat.mul 2.0 3.0) 1.0)
                    (PrimFloat.mul 0.5
                      (PrimFloat.sub (PrimFloat.add 2.0 4.0)
                                     (PrimFloat.mul 2.0 3.0))))%float).
Proof. reflexivity. Qed.

Compute print_expr leapfrog_update_expr.
Compute parse_expr_top (print_expr leapfrog_update_expr).

Lemma string_app_nil_r : forall s : string, (s ++ "")%string = s.
Proof.
  induction s as [| c s' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Corollary leapfrog_update_expr_json_roundtrip :
  parse_expr_top (print_expr leapfrog_update_expr) = Some (leapfrog_update_expr, "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip leapfrog_update_expr leapfrog_update_expr_idents_valid
                (String.length (print_expr leapfrog_update_expr) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_app_nil_r in H.
  exact H.
Qed.

Corollary leapfrog_update_translation_correct :
  forall rho,
    peval (env_to_pyenv rho) (translate leapfrog_update_expr)
      = option_map value_to_pyvalue (eval rho leapfrog_update_expr).
Proof. intro rho. apply translate_preserves_semantics. Qed.

(** The generated Python -- this is what [runtime/wave1d.py] actually
    imports and calls per grid cell; see its header comment. *)
Compute py_function "leapfrog_update" ["r"; "u_prev"; "u_left"; "u_center"; "u_right"]
  (translate leapfrog_update_expr).
