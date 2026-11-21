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
    avoids pulling in).

    * What this theorem does *not* cover: stability

    [leapfrog_exact_for_cubic_profile] is a statement about *one* step.
    It says nothing about what happens after many steps -- in particular,
    it does not require (or even mention) the classical Courant-Friedrichs-
    Lewy condition [c * dt / dx <= 1], which is what actually keeps
    repeated application of this scheme bounded rather than blowing up.
    That's a textbook numerical-analysis fact (via a von Neumann/Fourier
    stability analysis), not proved anywhere in this file or this project
    -- an honestly-scoped gap, not an oversight. [runtime/wave1d.py]'s
    [validate_parameters] is where this project draws the line between
    "proved" and "merely checked at the boundary": it can't prove
    stability, so it *validates* the CFL condition (and [dx > 0]/[c > 0])
    as explicit runtime preconditions before running the simulation,
    rather than silently producing numerically meaningless output if
    they're violated. See that function's comment for the precise mapping
    from each check back to the hypothesis or assumption it encodes.

    * The whole-grid loop, also now a proven [expr] term

    Everything above is the *per-point* update rule. This file's final
    section ([compute_interior_expr]/[one_pass_expr]/[wave_sim_expr])
    goes one step further: a genuine, proven whole-grid stencil-plus-
    time-loop simulator, built entirely from constructs [Lang.v]
    already had (lists, self-recursive closures, [ERepeat]) -- closing
    docs/roadmap.md's own "arrays/loops aren't in [expr] yet" gap for a
    list-based (not numpy-array-based) simulator. See that section's
    own header comment for the full account, including exactly what
    this does and does not claim relative to [runtime/wave1d.py]'s own,
    separately-maintained numpy fast path. *)

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
  eval 10 [("u_prev", VFloat 1.0%float); ("u_left", VFloat 2.0%float);
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
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate leapfrog_update_expr)
      = option_map value_to_pyvalue (eval fuel rho leapfrog_update_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python -- this is what [runtime/wave1d.py] actually
    imports and calls per grid cell; see its header comment. *)
Compute py_function "leapfrog_update" ["r"; "u_prev"; "u_left"; "u_center"; "u_right"]
  (translate leapfrog_update_expr).

(* ----------------------------------------------------------------- *)
(** * The whole-grid loop, as a real [expr] term -- not just the per-point update *)

(** Everything above this point proves the *per-point* update rule
    correct and extracts it; the grid allocation, boundary conditions,
    and time-stepping loop that actually run it (`runtime/wave1d.py`)
    were deliberately left as hand-written, unproven glue (see that
    module's own docstring, and `docs/roadmap.md`'s "arrays/loops
    aren't in `expr`/`pyexpr` yet" gap). This section closes that gap
    -- for a genuine, if list-based rather than numpy-array-based,
    whole-grid simulator -- using *zero* new [Lang.v]/[PyLang.v]/
    [Translate.v]/[Json.v]/[PyPrint.v]/[PyRename.v] constructors:
    [Lang.v]'s own [VList (list value)] (already backing [ENil]/
    [ECons]/[EListMatch]), [ERec]/[ELam]/[EApp] (self-recursive
    closures), [EPair]/[EFst]/[ESnd], [ELet], and [ERepeat] (bounded
    iteration) are already enough to express "apply a 3-point stencil
    across a whole list, fixing both ends, for [nt] time steps" --
    this is purely a matter of *composing* already-proven pieces, not
    inventing a new one.

    [compute_interior_expr] walks two lists in lockstep -- [cs], the
    current time step's grid (shrinking one element per step), and
    [ps], the previous time step's grid (shrinking the same way, its
    own *second* element -- [ps]'s first is the stencil's left
    neighbor's own prev value, not needed for the point currently
    being computed -- aligned with [cs]'s third): at each step the
    first three elements of [cs] are exactly one point's full 3-point
    spatial stencil, and [apply_leapfrog_update] rebinds them (plus
    the matching prev value) to the names [leapfrog_update_expr] above
    already expects, so the *exact*, already-proven update formula
    runs unmodified -- not a re-derivation, a direct reuse. Recursion
    stops (fixing the trailing boundary to [0]) once fewer than 3
    elements remain, the same "stuck once the shape runs out, not
    guessed" partiality this project's other recursive constructs
    already have. [one_pass_expr] is one whole-grid time step: fix the
    leading boundary to [0], then [compute_interior_expr] builds the
    rest. [wave_sim_expr nt] is [nt] such steps chained by [ERepeat],
    carrying [(prev, curr)] as its own loop state -- the exact
    "u_prev, u_curr = u_curr, u_next" swap `runtime/wave1d.py` already
    does, now inside the proven fragment instead of outside it. *)
Definition apply_leapfrog_update : expr :=
  ELet "u_prev" (EVar "p1") (
   ELet "u_left" (EVar "c0") (
    ELet "u_center" (EVar "c1") (
     ELet "u_right" (EVar "c2") (
      leapfrog_update_expr
     )))).

Definition compute_interior_expr : expr :=
  ERec "ci" "cs" (ELam "ps" (
    EListMatch (EVar "cs")
      (ECons (EFConst 0) ENil)
      "c0" "cs_rest1" (
        EListMatch (EVar "cs_rest1")
          (ECons (EFConst 0) ENil)
          "c1" "cs_rest2" (
            EListMatch (EVar "cs_rest2")
              (ECons (EFConst 0) ENil)
              "c2" "cs_rest3" (
                EListMatch (EVar "ps")
                  (ECons (EFConst 0) ENil)
                  "p0" "ps_rest1" (
                    EListMatch (EVar "ps_rest1")
                      (ECons (EFConst 0) ENil)
                      "p1" "ps_rest2" (
                        ECons
                          apply_leapfrog_update
                          (EApp (EApp (EVar "ci")
                                      (ECons (EVar "c1") (ECons (EVar "c2") (EVar "cs_rest3"))))
                                (ECons (EVar "p1") (EVar "ps_rest2")))
                      )
                  )
              )
          )
      )
  )).

Definition one_pass_expr : expr :=
  ELam "r" (ELam "curr" (ELam "prev" (
    ECons (EFConst 0)
      (EApp (EApp compute_interior_expr (EVar "curr")) (EVar "prev"))
  ))).

Definition wave_sim_expr (nt : nat) : expr :=
  ELam "r" (ELam "init" (
    ERepeat nt "state"
      (ELet "prev" (EFst (EVar "state"))
        (ELet "curr" (ESnd (EVar "state"))
          (EPair (EVar "curr")
                 (EApp (EApp (EApp one_pass_expr (EVar "r")) (EVar "curr")) (EVar "prev")))))
      (EVar "init")
  )).

Theorem one_pass_expr_idents_valid :
  expr_idents_valid is_valid_ident
    (EApp (EApp (EApp one_pass_expr (EVar "r")) (EVar "curr")) (EVar "prev")) = true.
Proof. reflexivity. Qed.

Theorem wave_sim_expr_idents_valid :
  forall nt, expr_idents_valid is_valid_ident (wave_sim_expr nt) = true.
Proof. intro nt. destruct nt; reflexivity. Qed.

(** The strongest check: *fully symbolic* in every grid value (not one
    concrete numeric instance) for a fixed 7-point grid -- [eval]
    unfolds [compute_interior_expr]'s own recursion down to a
    closed-form [PrimFloat] expression in the abstract bound variables
    regardless of what they denote, confirming the whole stencil-over-
    a-list machinery (not just the already-proven per-point formula in
    isolation) genuinely computes the intended thing for *any* 7-point
    grid, not merely one hand-picked example. This is a *fixed-size*
    universally-quantified theorem, not an arbitrary-length one -- the
    same "enough fuel/structure for this particular shape, not a
    general induction" standard this project's other [ERec]-based
    examples already use (`RealIR.v`'s header on [real_fix_decl]; see
    `examples/NaturalCoq.v`'s [any_true_expr_matches_real_definition]),
    since [compute_interior_expr]'s own recursion depth is the grid's
    length, not a static property of the term. *)
Example one_pass_symbolic_7point :
  forall g0 g1 g2 g3 g4 g5 g6 h0 h1 h2 h3 h4 h5 h6 r : PrimFloat.float,
    eval 80
      [("g0", VFloat g0); ("g1", VFloat g1); ("g2", VFloat g2); ("g3", VFloat g3);
       ("g4", VFloat g4); ("g5", VFloat g5); ("g6", VFloat g6);
       ("h0", VFloat h0); ("h1", VFloat h1); ("h2", VFloat h2); ("h3", VFloat h3);
       ("h4", VFloat h4); ("h5", VFloat h5); ("h6", VFloat h6);
       ("r", VFloat r)]
      (EApp (EApp (EApp one_pass_expr (EVar "r"))
               (ECons (EVar "g0") (ECons (EVar "g1") (ECons (EVar "g2") (ECons (EVar "g3")
                 (ECons (EVar "g4") (ECons (EVar "g5") (ECons (EVar "g6") ENil))))))))
               (ECons (EVar "h0") (ECons (EVar "h1") (ECons (EVar "h2") (ECons (EVar "h3")
                 (ECons (EVar "h4") (ECons (EVar "h5") (ECons (EVar "h6") ENil))))))))
    = Some (VList
        [VFloat 0;
         VFloat (PrimFloat.add (PrimFloat.sub (PrimFloat.mul 2 g1) h1)
                   (PrimFloat.mul r (PrimFloat.sub (PrimFloat.add g0 g2) (PrimFloat.mul 2 g1))));
         VFloat (PrimFloat.add (PrimFloat.sub (PrimFloat.mul 2 g2) h2)
                   (PrimFloat.mul r (PrimFloat.sub (PrimFloat.add g1 g3) (PrimFloat.mul 2 g2))));
         VFloat (PrimFloat.add (PrimFloat.sub (PrimFloat.mul 2 g3) h3)
                   (PrimFloat.mul r (PrimFloat.sub (PrimFloat.add g2 g4) (PrimFloat.mul 2 g3))));
         VFloat (PrimFloat.add (PrimFloat.sub (PrimFloat.mul 2 g4) h4)
                   (PrimFloat.mul r (PrimFloat.sub (PrimFloat.add g3 g5) (PrimFloat.mul 2 g4))));
         VFloat (PrimFloat.add (PrimFloat.sub (PrimFloat.mul 2 g5) h5)
                   (PrimFloat.mul r (PrimFloat.sub (PrimFloat.add g4 g6) (PrimFloat.mul 2 g5))));
         VFloat 0]).
Proof. intros. reflexivity. Qed.

(** A genuine multi-step run of the *whole simulator* -- not just one
    pass -- on a 7-point grid, unit pulse at the center, zero initial
    velocity (prev = curr, matching `runtime/wave1d.py`'s own
    convention), Courant number [r = 1] (the simplest CFL-satisfying
    choice: [c = dt = dx = 1]), for 3 time steps. Cross-checked against
    an independent, from-scratch Python computation of the same scheme
    (not derived from this expression) before trusting it:

    [[
    >>> def leapfrog(r, up, ul, uc, ur): return 2*uc - up + r*(ul - 2*uc + ur)
    >>> def one_pass(r, curr, prev):
    ...     n = len(curr); out = [0.0]*n
    ...     for i in range(1, n-1): out[i] = leapfrog(r, prev[i], curr[i-1], curr[i], curr[i+1])
    ...     return out
    >>> r = 1.0; curr = [0,0,0,1,0,0,0]; prev = curr[:]
    >>> for _ in range(3): prev, curr = curr, one_pass(r, curr, prev)
    >>> curr
    [0.0, -1.0, 1.0, -1.0, 1.0, -1.0, 0.0]
    >>> prev
    [0.0, 1.0, -1.0, 1.0, -1.0, 1.0, 0.0]
    ]]

    -- exactly the pair [wave_sim_expr 3] below computes. *)
Example wave_sim_3steps_7point :
  eval 500 []
    (EApp (EApp (wave_sim_expr 3) (EFConst 1))
       (EPair
          (ECons (EFConst 0) (ECons (EFConst 0) (ECons (EFConst 0) (ECons (EFConst 1)
            (ECons (EFConst 0) (ECons (EFConst 0) (ECons (EFConst 0) ENil)))))))
          (ECons (EFConst 0) (ECons (EFConst 0) (ECons (EFConst 0) (ECons (EFConst 1)
            (ECons (EFConst 0) (ECons (EFConst 0) (ECons (EFConst 0) ENil)))))))))
  = Some (VPair
            (VList [VFloat 0; VFloat 1; VFloat (-1); VFloat 1; VFloat (-1); VFloat 1; VFloat 0])
            (VList [VFloat 0; VFloat (-1); VFloat 1; VFloat (-1); VFloat 1; VFloat (-1); VFloat 0])).
Proof. reflexivity. Qed.

Corollary one_pass_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho)
      (translate (EApp (EApp (EApp one_pass_expr (EVar "r")) (EVar "curr")) (EVar "prev")))
      = option_map value_to_pyvalue
          (eval fuel rho (EApp (EApp (EApp one_pass_expr (EVar "r")) (EVar "curr")) (EVar "prev"))).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

Corollary wave_sim_translation_correct :
  forall nt fuel rho,
    peval fuel (env_to_pyenv rho) (translate (wave_sim_expr nt))
      = option_map value_to_pyvalue (eval fuel rho (wave_sim_expr nt)).
Proof. intros nt fuel rho. apply translate_preserves_semantics. Qed.

Compute print_expr (wave_sim_expr 3).

Corollary wave_sim_3_json_roundtrip :
  parse_expr_top (print_expr (wave_sim_expr 3)) = Some (wave_sim_expr 3, "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip (wave_sim_expr 3) (wave_sim_expr_idents_valid 3)
                (String.length (print_expr (wave_sim_expr 3)) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_app_nil_r in H.
  exact H.
Qed.

(** The generated Python: a list-of-nested-tuples simulator (the same
    representation every other list in this project already renders
    as -- not a numpy array the way `runtime/wave1d.py`'s own,
    separately-maintained fast path uses), confirmed to run and
    produce the exact pair above under actual Python, not just
    checked in Coq. This is a second, slower-but-proven way to run
    the simulator end to end, not a replacement for
    `runtime/wave1d.py`'s numpy-based one: see this file's header and
    `docs/roadmap.md`'s own entry on this for what remains genuinely
    unformalized (numpy's own array semantics specifically). *)
Compute py_function "wave_sim3" ["r"; "init"]
  (translate (EApp (EApp (wave_sim_expr 3) (EVar "r")) (EVar "init"))).
