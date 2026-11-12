(** Kinematics.v

    The running example for coq2py: a single semi-implicit ("symplectic")
    Euler integration step,

        v' = v + a*dt
        x' = x + v'*dt

    returning the pair (x', v') -- exercising pairs/tuples -- plus a
    second example, [landed_expr], exercising general comparisons and
    booleans: "has the projectile reached or passed ground level while
    still moving downward?" -- two more, [euler_step_float_expr] and
    [landed_float_expr], the same integration step and landing check
    again but over real [PrimFloat.float] state instead of [Z] -- a
    fifth, [euler_multi_step_expr], chaining [n] Euler steps into a
    whole trajectory via bounded iteration ([ERepeat]) -- a sixth,
    [time_to_stop_expr], a simple division with a precondition ([d <>
    0]) proved to matter and shown to need no separate runtime check:
    Python's own [//] already enforces it -- and a seventh,
    [fall_until_landed_expr], the data-dependent cousin of Example 5:
    run the same step function (via genuine recursion, [ERec], not
    [ERepeat]) until [landed_expr] actually holds, however many steps
    that takes -- not knowable at "compile time" the way Example 5's
    fixed [n] was -- an eighth, [total_distance_expr], summing
    [v * dt] over a genuine list of velocity samples ([ENil]/[ECons]/
    [EListMatch]): a Riemann sum over data of whatever length it
    happens to have, not a single step or a fixed count of them -- and
    a ninth, [euler_step_record_expr], Example 1's step again but
    returning a 2-field named record ([ERecord]/[EField]) instead of a
    positional pair, so the generated Python looks state up by name
    ([state["x"]]) instead of by position ([state[0]]) -- a tenth,
    [bounce_expr], an elastic bounce via [ERecMut]: two functions,
    ["fall"] and ["rise"], defined together so each can call the
    other, not just [ERec]'s single self-call -- an eleventh,
    [safe_time_to_stop_expr]/[stop_time_or_minus_one_expr], Example 6's
    division precondition reflected as a genuine value ([EInl]/[EInr]/
    [ECase]) instead of [eval] simply getting stuck -- a twelfth,
    [motion_phase_expr], a real string value ([EStrConst]/[EStrEq])
    labelling the same state Example 2's [landed_expr] already tests --
    a thirteenth, [euler_step_full_state_expr], Example 9's named
    record again but with *four* fields at once ([ERecordN]/[EFieldN]),
    genuinely beyond [ERecord]'s 2-field cap rather than nesting it --
    a fourteenth, [motion_report_expr], Example 12's label again
    but as a general string literal (a space, an embedded quote mark)
    rather than the identifier-shaped text [EStrConst] was first
    restricted to -- and a fifteenth, [bounce3_expr], Example 10's
    bounce again but with a *third* mutually-recursive member added
    to the same group ([ERecGroup], genuinely beyond [ERecMut]'s
    2-function cap), exercising a real three-way cross-call.

    All fifteen are expressed as terms of our supported [expr] subset
    (Lang.v), then run through every stage of the pipeline this repository
    actually proves: JSON round-trip (Json.v), translation to the
    Python-subset AST (Translate.v), and rendering as Python source
    (PyPrint.v). Everything marked [Compute] below is meant to be
    evaluated with [coqc]/[coqtop] and its real output captured into
    docs/examples.md -- nothing in that doc is hand-written/fabricated.
    [eval]/[peval] (and so [translate_preserves_semantics]) now take an
    explicit fuel argument (see Lang.v's header for why [EApp] forces
    this) -- every [eval _ rho e] call below just picks a fuel generous
    enough that none of these small, terminating terms ever run out.

    This is also the first concrete instance of the project's stated goal
    (GOAL.md): "express physics in Coq, extract a Python simulator proven
    correct". Examples 1 and 2 are deliberately tiny instances -- integers
    standing in for what would eventually be a floating-point/numpy state
    vector -- chosen to stay inside the subset that's actually proven
    today rather than gesture at scope the proofs don't yet cover. Examples
    3 and 4 close that gap for a single step (real float arithmetic and
    comparisons, proven the same way); Example 5 closes it for a whole
    multi-step trajectory, computed *inside* the proven subset (no
    external loop); Example 7 closes it again for a trajectory whose
    length genuinely depends on the data, not on anything fixed in
    advance -- see docs/roadmap.md for what's still missing before a
    genuine numpy-shaped simulator (arrays). *)

From Coq Require Import ZArith String List Bool Lia.
From Coq Require Import Floats.PrimFloat.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Open Scope Z_scope.
Open Scope string_scope.

Lemma string_app_nil_r : forall s : string, s ++ "" = s.
Proof.
  induction s as [| c s' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** A reusable tactic, applied below to each (concrete) example term:
    valid identifiers plus the general theorems already proved in Json.v
    and Translate.v are enough to get the JSON round-trip "for free", with
    no new proof obligations. (Kept as a tactic rather than a lemma
    because the fuel side-condition is discharged by [vm_compute], which
    needs the term concrete -- it doesn't go through for an arbitrary
    [e].) *)
Ltac json_roundtrip_corollary e Hvalid :=
  unfold parse_expr_top;
  let H := fresh "H" in
  pose proof (parse_print_roundtrip e Hvalid
                (String.length (print_expr e) + 1)
                ltac:(vm_compute; lia) "") as H;
  rewrite string_app_nil_r in H;
  exact H.

(* ----------------------------------------------------------------- *)
(** * Example 1: one Euler step, returning the pair (x', v') *)

Definition euler_step_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (EPair (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))) (EVar "v2")).

(** This term is within the provably-covered subset: all its identifiers
    are valid, so [parse_print_roundtrip] and [translate_preserves_semantics]
    both apply to it unconditionally. *)
Theorem euler_step_idents_valid :
  expr_idents_valid is_valid_ident euler_step_expr = true.
Proof. reflexivity. Qed.

(** A concrete run: starting at rest (x=0, v=0) with acceleration a=2 for
    one step of dt=1, the new state is (x'=2, v'=2). Fuel [10] is already
    far more than this tiny, non-recursive term could ever need -- there
    is no meaningful "right" fuel bound here, just "enough". *)
Example euler_step_concrete :
  eval 10 [("x", VZ 0); ("v", VZ 0); ("a", VZ 2); ("dt", VZ 1)] euler_step_expr
    = Some (VPair (VZ 2) (VZ 2)).
Proof. reflexivity. Qed.

(** The JSON encoding of the example term. *)
Compute print_expr euler_step_expr.

(** Parsing that text back recovers the exact same term (and consumes
    all of it, leaving nothing unparsed) -- an instance of
    [parse_print_roundtrip], not a new proof. *)
Compute parse_expr_top (print_expr euler_step_expr).

Corollary euler_step_json_roundtrip :
  parse_expr_top (print_expr euler_step_expr) = Some (euler_step_expr, "").
Proof. json_roundtrip_corollary euler_step_expr euler_step_idents_valid. Qed.

(** The translated Python-subset AST, evaluated under the formal [peval]
    semantics, agrees with [eval] on the source term (up to the
    value<->pyvalue correspondence) -- an instance of
    [translate_preserves_semantics], not a new proof. *)
Corollary euler_step_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate euler_step_expr)
      = option_map value_to_pyvalue (eval fuel rho euler_step_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The actual generated Python source. *)
Compute py_function "euler_step" ["x"; "v"; "a"; "dt"] (translate euler_step_expr).

(* ----------------------------------------------------------------- *)
(** * Example 2: general comparisons and booleans *)

(** Has the projectile reached or passed ground level while still moving
    downward? (Checking the direction of motion too avoids reporting
    "landed" for a projectile that started on or below the ground and is
    still rising.) *)
Definition landed_expr : expr :=
  EAnd (ELe (EVar "x") (EConst 0)) (ELt (EVar "v") (EConst 0)).

Theorem landed_idents_valid :
  expr_idents_valid is_valid_ident landed_expr = true.
Proof. reflexivity. Qed.

Example landed_concrete_true :
  eval 10 [("x", VZ (-1)); ("v", VZ (-3))] landed_expr = Some (VBool true).
Proof. reflexivity. Qed.

Example landed_concrete_false_still_above_ground :
  eval 10 [("x", VZ 5); ("v", VZ (-3))] landed_expr = Some (VBool false).
Proof. reflexivity. Qed.

Example landed_concrete_false_rising :
  eval 10 [("x", VZ (-1)); ("v", VZ 3)] landed_expr = Some (VBool false).
Proof. reflexivity. Qed.

Compute print_expr landed_expr.
Compute parse_expr_top (print_expr landed_expr).

Corollary landed_json_roundtrip :
  parse_expr_top (print_expr landed_expr) = Some (landed_expr, "").
Proof. json_roundtrip_corollary landed_expr landed_idents_valid. Qed.

Corollary landed_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate landed_expr)
      = option_map value_to_pyvalue (eval fuel rho landed_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

Compute py_function "landed" ["x"; "v"] (translate landed_expr).

(* ----------------------------------------------------------------- *)
(** * Example 3: the same Euler step, in real floats *)

(** Identical in shape to [euler_step_expr] above, but over
    [PrimFloat.float] state and [EFAdd]/[EFMul] arithmetic instead of
    [Z]/[EAdd]/[EMul] -- the same machine-checked preservation and
    JSON-round-trip theorems apply unconditionally here too, with no
    separate float-specific argument needed. *)
Definition euler_step_float_expr : expr :=
  ELet "v2" (EFAdd (EVar "v") (EFMul (EVar "a") (EVar "dt")))
    (EPair (EFAdd (EVar "x") (EFMul (EVar "v2") (EVar "dt"))) (EVar "v2")).

Theorem euler_step_float_idents_valid :
  expr_idents_valid is_valid_ident euler_step_float_expr = true.
Proof. reflexivity. Qed.

(** Starting at rest (x=0.0, v=0.0) with acceleration a=2.0 for one step
    of dt=1.0, the new state is (x'=2.0, v'=2.0) -- the same answer as
    [euler_step_concrete] above, now computed in real [float]
    arithmetic rather than standing in via [Z]. *)
Example euler_step_float_concrete :
  eval 10 [("x", VFloat 0.0%float); ("v", VFloat 0.0%float);
        ("a", VFloat 2.0%float); ("dt", VFloat 1.0%float)]
    euler_step_float_expr
    = Some (VPair (VFloat 2.0%float) (VFloat 2.0%float)).
Proof. reflexivity. Qed.

Compute print_expr euler_step_float_expr.
Compute parse_expr_top (print_expr euler_step_float_expr).

Corollary euler_step_float_json_roundtrip :
  parse_expr_top (print_expr euler_step_float_expr) = Some (euler_step_float_expr, "").
Proof. json_roundtrip_corollary euler_step_float_expr euler_step_float_idents_valid. Qed.

Corollary euler_step_float_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate euler_step_float_expr)
      = option_map value_to_pyvalue (eval fuel rho euler_step_float_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: exact, via the [mantissa * (2.0 ** exponent)]
    encoding described in PyPrint.v -- not the shortest decimal a human
    would write, but bit-for-bit the same value as the source float. *)
Compute py_function "euler_step_float" ["x"; "v"; "a"; "dt"] (translate euler_step_float_expr).

(* ----------------------------------------------------------------- *)
(** * Example 4: [landed_expr], over real floats *)

(** [landed_expr] (Example 2) restated with [EFLe]/[EFLt] over real
    [float] position/velocity instead of [ELe]/[ELt] over [Z] -- the
    comparison counterpart to Example 3's arithmetic one. *)
Definition landed_float_expr : expr :=
  EAnd (EFLe (EVar "x") (EFConst 0)) (EFLt (EVar "v") (EFConst 0)).

Theorem landed_float_idents_valid :
  expr_idents_valid is_valid_ident landed_float_expr = true.
Proof. reflexivity. Qed.

Example landed_float_concrete_true :
  eval 10 [("x", VFloat (-1)%float); ("v", VFloat (-3)%float)] landed_float_expr
    = Some (VBool true).
Proof. reflexivity. Qed.

Example landed_float_concrete_false_still_above_ground :
  eval 10 [("x", VFloat 5%float); ("v", VFloat (-3)%float)] landed_float_expr
    = Some (VBool false).
Proof. reflexivity. Qed.

Compute py_function "landed_float" ["x"; "v"] (translate landed_float_expr).

(* ----------------------------------------------------------------- *)
(** * Example 5: a multi-step trajectory, via bounded iteration *)

(** [euler_step_expr] (Example 1) applied [n] times in a row by
    [ERepeat], the whole trajectory computed *inside* the proven subset
    -- no external loop needed, unlike the wave simulator
    (examples/physics/Discretize.v), which has to reach for one because
    its state is a whole numpy array, not a small pair like here. The
    loop variable ["state"] carries [(x, v)] across iterations; [a] and
    [dt] stay constant, read from the outer environment every step. *)
Definition euler_multi_step_body : expr :=
  ELet "x" (EFst (EVar "state"))
  (ELet "v" (ESnd (EVar "state"))
    (ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
      (EPair (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))) (EVar "v2")))).

Definition euler_multi_step_expr (n : nat) : expr :=
  ERepeat n "state" euler_multi_step_body (EPair (EVar "x0") (EVar "v0")).

(** Identifier validity doesn't depend on the iteration count at all
    (see [expr_idents_valid]'s [ERepeat] case), so this holds for every
    [n] at once, not just the one instance used below. *)
Theorem euler_multi_step_idents_valid :
  forall n, expr_idents_valid is_valid_ident (euler_multi_step_expr n) = true.
Proof. intro n. reflexivity. Qed.

(** Three steps of the same constant-acceleration motion as Example 1,
    starting at rest: (x,v) = (0,0) -> (2,2) -> (6,4) -> (12,6). *)
Example euler_multi_step_concrete :
  eval 10 [("x0", VZ 0); ("v0", VZ 0); ("a", VZ 2); ("dt", VZ 1)]
    (euler_multi_step_expr 3)
    = Some (VPair (VZ 12) (VZ 6)).
Proof. reflexivity. Qed.

Corollary euler_multi_step_json_roundtrip :
  parse_expr_top (print_expr (euler_multi_step_expr 3))
    = Some (euler_multi_step_expr 3, "").
Proof.
  json_roundtrip_corollary (euler_multi_step_expr 3) (euler_multi_step_idents_valid 3).
Qed.

Corollary euler_multi_step_translation_correct :
  forall fuel n rho,
    peval fuel (env_to_pyenv rho) (translate (euler_multi_step_expr n))
      = option_map value_to_pyvalue (eval fuel rho (euler_multi_step_expr n)).
Proof. intros fuel n rho. apply translate_preserves_semantics. Qed.

(** The generated Python literally unrolls the 3 steps -- see PyPrint.v's
    comment on [PRepeat] for why that's the right call for a bounded,
    compile-time-known count. *)
Compute py_function "euler_trajectory_3" ["x0"; "v0"; "a"; "dt"]
  (translate (euler_multi_step_expr 3)).

(* ----------------------------------------------------------------- *)
(** * Example 6: a precondition, proved and reflected in Python *)

(** Time for a decelerating object (deceleration magnitude [d], moving
    at speed [v]) to stop: [t = v / d]. This is only *meaningful* for
    [d <> 0] -- a deceleration of zero never stops anything -- and
    [EDiv] only *produces an answer* for [d <> 0] too ([eval] gets
    stuck on a zero divisor; see Lang.v's comment). [eval_div_correct]
    is the proof that, given that precondition, this computes exactly
    [Z.div v d], nothing more. *)
Definition time_to_stop_expr : expr := EDiv (EVar "v") (EVar "d").

Theorem time_to_stop_idents_valid :
  expr_idents_valid is_valid_ident time_to_stop_expr = true.
Proof. reflexivity. Qed.

(** At 20 (distance units)/(time unit), decelerating by 4 per step,
    it takes 5 steps to stop. *)
Example time_to_stop_concrete : eval 10 [("v", VZ 20); ("d", VZ 4)] time_to_stop_expr = Some (VZ 5).
Proof. reflexivity. Qed.

(** And the precondition's failure case: zero deceleration means
    [eval] is honestly undefined here, not "0" or some other
    plausible-looking placeholder. *)
Example time_to_stop_zero_deceleration : eval 10 [("v", VZ 20); ("d", VZ 0)] time_to_stop_expr = None.
Proof. reflexivity. Qed.

Compute py_function "time_to_stop" ["v"; "d"] (translate time_to_stop_expr).

(** No validation code needed in the generated function at all: Python's
    own [//] already raises [ZeroDivisionError] on a zero divisor,
    exactly matching [eval]'s own notion of "undefined here" -- the
    precondition [eval_div_correct] needs is enforced by the target
    language for free, not by anything this project had to add. Run for
    real:

    [[
    >>> time_to_stop(20, 4)
    5
    >>> time_to_stop(20, 0)
    ZeroDivisionError: integer division or modulo by zero
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * Example 7: run until it actually lands, via real recursion *)

(** Example 5 chained a *fixed* number of Euler steps. Here, the number
    of steps genuinely depends on the data (when does [landed_expr]
    first become true?), which [ERepeat] -- a compile-time-known count
    -- cannot express at all. [ERec] can: [fall_until_landed_expr] is a
    self-referential function, ["simulate"], that checks the landing
    condition and either returns the current state or calls itself again
    on one more Euler step -- reusing both [euler_multi_step_body]
    (Example 5's step function) and [landed_expr]'s condition shape
    (Example 2) unchanged. *)
Definition fall_until_landed_expr : expr :=
  ERec "simulate" "state"
    (EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
         (EVar "state")
         (EApp (EVar "simulate") euler_multi_step_body)).

Theorem fall_until_landed_idents_valid :
  expr_idents_valid is_valid_ident fall_until_landed_expr = true.
Proof. reflexivity. Qed.

(** Dropped from height 45 with "gravity" [a = -10] and [dt = 1]:
    (45,0) -> (35,-10) -> (15,-20) -> (-15,-30), landing on the third
    step (x <= 0 and still moving down). Fuel [100] is nowhere near
    tight -- there is no proof obligation to pick a *minimal* fuel, only
    "enough for this particular run to actually finish". *)
Example fall_until_landed_concrete :
  eval 100 [("a", VZ (-10)); ("dt", VZ 1)]
    (EApp fall_until_landed_expr (EPair (EConst 45) (EConst 0)))
    = Some (VPair (VZ (-15)) (VZ (-30))).
Proof. reflexivity. Qed.

(** Too little fuel and this honestly-recursive term simply doesn't
    finish in the fuel given -- [eval] is stuck the same way it would be
    on an unbound variable, not wrong. *)
Example fall_until_landed_out_of_fuel :
  eval 3 [("a", VZ (-10)); ("dt", VZ 1)]
    (EApp fall_until_landed_expr (EPair (EConst 45) (EConst 0)))
    = None.
Proof. reflexivity. Qed.

Compute print_expr (EApp fall_until_landed_expr (EPair (EConst 45) (EConst 0))).

Corollary fall_until_landed_json_roundtrip :
  parse_expr_top (print_expr (EApp fall_until_landed_expr (EPair (EConst 45) (EConst 0))))
    = Some (EApp fall_until_landed_expr (EPair (EConst 45) (EConst 0)), "").
Proof.
  json_roundtrip_corollary
    (EApp fall_until_landed_expr (EPair (EConst 45) (EConst 0)))
    fall_until_landed_idents_valid.
Qed.

Corollary fall_until_landed_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate fall_until_landed_expr)
      = option_map value_to_pyvalue (eval fuel rho fall_until_landed_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: a genuinely recursive closure, via the
    walrus-self-reference trick described in PyPrint.v's comment on
    [PRec] -- not unrolled, since (unlike Example 5's [ERepeat]) there
    is no fixed count to unroll by. *)
Compute py_function "fall_until_landed" ["a"; "dt"] (translate fall_until_landed_expr).

(** Run for real -- [fall_until_landed(-10, 1)] builds the recursive
    closure once; calling it on the initial state runs exactly as many
    steps as it takes to land, matching the proof above exactly:

    [[
    >>> f = fall_until_landed(-10, 1)
    >>> f((45, 0))
    (-15, -30)
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * Example 8: a Riemann sum over a genuine list *)

(** Total distance travelled, given a list of velocity samples taken
    every [dt]: [sum (v_i * dt)] over the whole list, via [ERec] (the
    recursion) walking an [EListMatch] (the list). Unlike every earlier
    example, the input isn't a fixed-shape value at all -- a list can be
    any length, known only at run time, exactly the point of adding
    [ENil]/[ECons]/[EListMatch] to this subset. *)
Definition total_distance_expr : expr :=
  ERec "total" "vs"
    (EListMatch (EVar "vs") (EConst 0) "v" "rest"
       (EAdd (EMul (EVar "v") (EVar "dt")) (EApp (EVar "total") (EVar "rest")))).

Theorem total_distance_idents_valid :
  expr_idents_valid is_valid_ident total_distance_expr = true.
Proof. reflexivity. Qed.

(** Three velocity samples 2, 4, 6 over unit time steps: total distance
    2*1 + 4*1 + 6*1 = 12. *)
Example total_distance_concrete :
  eval 100 [("dt", VZ 1)]
    (EApp total_distance_expr (ECons (EConst 2) (ECons (EConst 4) (ECons (EConst 6) ENil))))
    = Some (VZ 12).
Proof. reflexivity. Qed.

Corollary total_distance_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate total_distance_expr)
      = option_map value_to_pyvalue (eval fuel rho total_distance_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: lists render as nested tuples ([Nil] as [()],
    [Cons h t] as [(h, t)]) -- see PyPrint.v's comment on [PListMatch]
    for why that, not Python's native mutable [list], is the right
    match for this subset's cons-list values. *)
Compute py_function "total_distance" ["dt"] (translate total_distance_expr).

(** Run for real:

    [[
    >>> f = total_distance(1)
    >>> f((2, (4, (6, ()))))
    12
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * Example 9: the same Euler step, returning a named record *)

(** [euler_step_expr] (Example 1) again, but returning the new state as
    a 2-field named record {"x": x', "v": v'} instead of a positional
    pair -- exercising [ERecord]/[EField]. Unlike [EFst]/[EPair], a
    record's fields carry their own names all the way through to the
    generated Python, where they can be looked up by name instead of by
    position. *)
Definition euler_step_record_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (ERecord "x" (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))) "v" (EVar "v2")).

Theorem euler_step_record_idents_valid :
  expr_idents_valid is_valid_ident euler_step_record_expr = true.
Proof. reflexivity. Qed.

(** Same motion as [euler_step_concrete] (Example 1): starting at rest
    with acceleration 2 for one step of dt=1, the new state is
    {"x": 2, "v": 2}. *)
Example euler_step_record_concrete :
  eval 10 [("x", VZ 0); ("v", VZ 0); ("a", VZ 2); ("dt", VZ 1)] euler_step_record_expr
    = Some (VRecord "x" (VZ 2) "v" (VZ 2)).
Proof. reflexivity. Qed.

Compute print_expr euler_step_record_expr.
Compute parse_expr_top (print_expr euler_step_record_expr).

Corollary euler_step_record_json_roundtrip :
  parse_expr_top (print_expr euler_step_record_expr) = Some (euler_step_record_expr, "").
Proof. json_roundtrip_corollary euler_step_record_expr euler_step_record_idents_valid. Qed.

Corollary euler_step_record_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate euler_step_record_expr)
      = option_map value_to_pyvalue (eval fuel rho euler_step_record_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: a dict literal with the same two field names,
    looked up by name ([state["x"]]) rather than by position
    ([state[0]]) -- see PyPrint.v's [PRecord]/[PField] cases. *)
Compute py_function "euler_step_record" ["x"; "v"; "a"; "dt"] (translate euler_step_record_expr).

(* ----------------------------------------------------------------- *)
(** * Example 10: an elastic bounce, via mutual recursion *)

(** [ERec] (Example 7) only lets a function call *itself*. [ERecMut]
    lifts that to two functions that may each call either of
    themselves: ["fall"] runs Euler steps (reusing
    [euler_multi_step_body], Example 5) until the projectile would go
    through the ground, then hands off to ["rise"], which reflects the
    velocity (a perfectly elastic bounce, no energy lost) and returns
    -- a genuine cross-call between the two functions defined together,
    not just [ERec]'s single self-call. [ERecMut] evaluates to a pair
    of the two closures, [EFst]/[ESnd] picking out whichever one is
    wanted (here, ["fall"], the entry point). *)
Definition bounce_fall_body : expr :=
  EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
      (EApp (EVar "rise") (EVar "state"))
      (EApp (EVar "fall") euler_multi_step_body).

Definition bounce_rise_body : expr :=
  EPair (EFst (EVar "state")) (ESub (EConst 0) (ESnd (EVar "state"))).

Definition bounce_expr : expr :=
  ERecMut "fall" "state" bounce_fall_body "rise" "state" bounce_rise_body.

Theorem bounce_idents_valid :
  expr_idents_valid is_valid_ident bounce_expr = true.
Proof. reflexivity. Qed.

(** Same drop as Example 7 (height 45, "gravity" [a = -10], [dt = 1]):
    three Euler steps land at [(-15, -30)], at which point ["fall"]
    hands off to ["rise"], which reflects the velocity to [30] -- the
    projectile bounces back upward at the same speed it landed with. *)
Example bounce_concrete :
  eval 100 [("a", VZ (-10)); ("dt", VZ 1)]
    (EApp (EFst bounce_expr) (EPair (EConst 45) (EConst 0)))
    = Some (VPair (VZ (-15)) (VZ 30)).
Proof. reflexivity. Qed.

Compute print_expr (EApp (EFst bounce_expr) (EPair (EConst 45) (EConst 0))).

Corollary bounce_json_roundtrip :
  parse_expr_top (print_expr (EApp (EFst bounce_expr) (EPair (EConst 45) (EConst 0))))
    = Some (EApp (EFst bounce_expr) (EPair (EConst 45) (EConst 0)), "").
Proof.
  json_roundtrip_corollary
    (EApp (EFst bounce_expr) (EPair (EConst 45) (EConst 0)))
    bounce_idents_valid.
Qed.

Corollary bounce_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate bounce_expr)
      = option_map value_to_pyvalue (eval fuel rho bounce_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: both closures are built together, via two
    chained walrus assignments (the same self-reference trick [PRec]
    already uses, extended to two names instead of one -- see
    PyPrint.v's comment on [PRecMut]), then returned as a pair. *)
Compute py_function "bounce" ["a"; "dt"] (translate bounce_expr).

(** Run for real:

    [[
    >>> fall, rise = bounce(-10, 1)
    >>> fall((45, 0))
    (-15, 30)
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * Example 11: a precondition reflected as a value, via a sum type *)

(** Example 6's [time_to_stop_expr] reflects its precondition ([d <>
    0]) by getting *stuck* ([None]) when it fails -- an honest, but
    silent, way to be partial. [EInl]/[EInr]/[ECase] let the same
    precondition be reflected as an ordinary *value* instead:
    [safe_time_to_stop_expr] returns [EInl time] when [d <> 0], or
    [EInr v] (the velocity, which will now never reach zero) when
    [d = 0] -- a *total* function whose result says, at the type level,
    which of the two cases happened, rather than a partial one that
    simply fails to answer. [ECase] is the eliminator: given either
    outcome, substitute a concrete reading (the real stopping time, or
    [-1] standing for "never stops"). *)
Definition safe_time_to_stop_expr : expr :=
  EIf (EEq (EVar "d") (EConst 0))
      (EInr (EVar "v"))
      (EInl (EDiv (EVar "v") (EVar "d"))).

Definition stop_time_or_minus_one_expr : expr :=
  ECase safe_time_to_stop_expr "t" (EVar "t") "_" (ESub (EConst 0) (EConst 1)).

Theorem stop_time_or_minus_one_idents_valid :
  expr_idents_valid is_valid_ident stop_time_or_minus_one_expr = true.
Proof. reflexivity. Qed.

(** Same numbers as Example 6: decelerating by 4 per step from speed
    20 takes 5 steps to stop -- now a genuine [VInl], not a [Some]
    wrapping a bare number. *)
Example safe_time_to_stop_concrete :
  eval 10 [("v", VZ 20); ("d", VZ 4)] safe_time_to_stop_expr = Some (VInl (VZ 5)).
Proof. reflexivity. Qed.

(** And the zero-deceleration case Example 6 could only express as
    "stuck" is now a real, distinguishable value: [VInr 20], not [None]. *)
Example safe_time_to_stop_zero_deceleration :
  eval 10 [("v", VZ 20); ("d", VZ 0)] safe_time_to_stop_expr = Some (VInr (VZ 20)).
Proof. reflexivity. Qed.

(** [ECase] then turns either outcome into one concrete number: *)
Example stop_time_or_minus_one_concrete :
  eval 10 [("v", VZ 20); ("d", VZ 4)] stop_time_or_minus_one_expr = Some (VZ 5).
Proof. reflexivity. Qed.

Example stop_time_or_minus_one_never_stops :
  eval 10 [("v", VZ 20); ("d", VZ 0)] stop_time_or_minus_one_expr = Some (VZ (-1)).
Proof. reflexivity. Qed.

Compute print_expr stop_time_or_minus_one_expr.

Corollary stop_time_or_minus_one_json_roundtrip :
  parse_expr_top (print_expr stop_time_or_minus_one_expr) = Some (stop_time_or_minus_one_expr, "").
Proof.
  json_roundtrip_corollary stop_time_or_minus_one_expr stop_time_or_minus_one_idents_valid.
Qed.

Corollary stop_time_or_minus_one_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate stop_time_or_minus_one_expr)
      = option_map value_to_pyvalue (eval fuel rho stop_time_or_minus_one_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: [EInl]/[EInr] render as a tagged 2-tuple
    ([("inl", v)]/[("inr", v)] -- see PyPrint.v's comment on [PInl]/
    [PInr]/[PCase]), and [ECase] as a conditional on that tag, binding
    the payload with the same walrus trick [PListMatch] already uses. *)
Compute py_function "stop_time_or_minus_one" ["v"; "d"] (translate stop_time_or_minus_one_expr).

(** Run for real:

    [[
    >>> stop_time_or_minus_one(20, 4)
    5
    >>> stop_time_or_minus_one(20, 0)
    -1
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * Example 12: a genuine string value, labelling a motion phase *)

(** [EStrConst]/[EStrConcat]/[EStrEq] add a fifth scalar value, [VStr]
    -- real strings, not just the identifiers [var] was already used
    for everywhere else. [motion_phase_expr] reuses [landed_expr]'s
    condition (Example 2) to label a state [(x, v)] with a word
    instead of just a bool -- the same state tested, but communicated
    as text: *)
Definition motion_phase_expr : expr :=
  EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
      (EStrConst "landed")
      (EStrConst "falling").

Definition is_landed_label_expr : expr :=
  EStrEq motion_phase_expr (EStrConst "landed").

Theorem is_landed_label_idents_valid :
  expr_idents_valid is_valid_ident is_landed_label_expr = true.
Proof. reflexivity. Qed.

(** The same two states Example 10's bounce distinguishes by position
    -- [(-15, -30)] (landed) and [(35, -10)] (still falling, partway
    through Example 7's trajectory) -- now distinguished by a real
    string, compared with [EStrEq]: *)
Example motion_phase_landed :
  eval 10 [("state", VPair (VZ (-15)) (VZ (-30)))] motion_phase_expr = Some (VStr "landed").
Proof. reflexivity. Qed.

Example motion_phase_falling :
  eval 10 [("state", VPair (VZ 35) (VZ (-10)))] motion_phase_expr = Some (VStr "falling").
Proof. reflexivity. Qed.

Example is_landed_label_concrete :
  eval 10 [("state", VPair (VZ (-15)) (VZ (-30)))] is_landed_label_expr = Some (VBool true).
Proof. reflexivity. Qed.

Compute print_expr is_landed_label_expr.

Corollary is_landed_label_json_roundtrip :
  parse_expr_top (print_expr is_landed_label_expr) = Some (is_landed_label_expr, "").
Proof. json_roundtrip_corollary is_landed_label_expr is_landed_label_idents_valid. Qed.

Corollary is_landed_label_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate is_landed_label_expr)
      = option_map value_to_pyvalue (eval fuel rho is_landed_label_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: a plain string literal and [==], nothing
    exotic -- see PyPrint.v's comment on [PStrConst]'s honest
    restriction to identifier-shaped text. *)
Compute py_function "is_landed_label" ["state"] (translate is_landed_label_expr).

(** Run for real:

    [[
    >>> is_landed_label((-15, -30))
    True
    >>> is_landed_label((35, -10))
    False
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * Example 13: a genuinely N-ary state record *)

(** [euler_step_record_expr] (Example 9) stayed inside [ERecord]'s
    2-field cap. [euler_step_full_state_expr] is the same Euler step,
    but threads *four* named fields through at once -- position,
    velocity, the (unchanged) acceleration, and an elapsed-time clock
    -- exercising [ERecordN]/[EFieldN] genuinely, not by nesting
    [ERecord]. Lifting the cap needed a different induction technique
    (strong induction on a fuel measure, not more constructors) before
    this was even provable -- see docs/roadmap.md. *)
Definition euler_step_full_state_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (ERecordN [
       ("x", EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt")));
       ("v", EVar "v2");
       ("a", EVar "a");
       ("t", EAdd (EVar "t") (EVar "dt"))
     ]).

Theorem euler_step_full_state_idents_valid :
  expr_idents_valid is_valid_ident euler_step_full_state_expr = true.
Proof. reflexivity. Qed.

(** Same motion as [euler_step_concrete] (Example 1), now also
    carrying a clock: starting at rest with acceleration 2, one step
    of dt=1 from t=0 reaches {"x": 2, "v": 2, "a": 2, "t": 1}. *)
Example euler_step_full_state_concrete :
  eval 10 [("x", VZ 0); ("v", VZ 0); ("a", VZ 2); ("dt", VZ 1); ("t", VZ 0)]
    euler_step_full_state_expr
    = Some (VRecordN [("x", VZ 2); ("v", VZ 2); ("a", VZ 2); ("t", VZ 1)]).
Proof. reflexivity. Qed.

(** [EFieldN] reads a field back out by name, the same way [EField]
    already does for the 2-field form: *)
Definition elapsed_time_expr : expr := EFieldN "t" euler_step_full_state_expr.

Theorem elapsed_time_idents_valid :
  expr_idents_valid is_valid_ident elapsed_time_expr = true.
Proof. reflexivity. Qed.

Example elapsed_time_concrete :
  eval 10 [("x", VZ 0); ("v", VZ 0); ("a", VZ 2); ("dt", VZ 1); ("t", VZ 0)]
    elapsed_time_expr = Some (VZ 1).
Proof. reflexivity. Qed.

Compute print_expr euler_step_full_state_expr.

Corollary euler_step_full_state_json_roundtrip :
  parse_expr_top (print_expr euler_step_full_state_expr)
    = Some (euler_step_full_state_expr, "").
Proof.
  json_roundtrip_corollary euler_step_full_state_expr euler_step_full_state_idents_valid.
Qed.

Corollary euler_step_full_state_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate euler_step_full_state_expr)
      = option_map value_to_pyvalue (eval fuel rho euler_step_full_state_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: a dict literal with all four field names,
    built by [PyPrint.v]'s [PRecordN] case walking the field list. *)
Compute py_function "euler_step_full_state" ["x"; "v"; "a"; "dt"; "t"]
  (translate euler_step_full_state_expr).

(* ----------------------------------------------------------------- *)
(** * Example 14: a general string literal, no longer identifier-shaped *)

(** [motion_phase_expr] (Example 12) could only ever produce
    identifier-shaped labels (["landed"]/["falling"]) -- [EStrConst]'s
    payload was checked by [is_valid_ident], the same restriction
    [EVar]'s own name has. That restriction is lifted now (see Lang.v's
    header and Json.v's [quote_text]/[parse_qtext]): a label can be an
    ordinary human phrase, including a space and an embedded quote
    mark that JSON's own quoting would otherwise make ambiguous. *)
Definition motion_report_expr : expr :=
  EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
      (EStrConst "status: ""landed""")
      (EStrConst "status: still falling").

Theorem motion_report_idents_valid :
  expr_idents_valid is_valid_ident motion_report_expr = true.
Proof. reflexivity. Qed.

(** The same two states Example 12 already distinguishes: *)
Example motion_report_landed :
  eval 10 [("state", VPair (VZ (-15)) (VZ (-30)))] motion_report_expr
    = Some (VStr "status: ""landed""").
Proof. reflexivity. Qed.

Example motion_report_falling :
  eval 10 [("state", VPair (VZ 35) (VZ (-10)))] motion_report_expr
    = Some (VStr "status: still falling").
Proof. reflexivity. Qed.

(** The embedded quote mark is escaped in the JSON wire encoding
    ([quote_text]), not left bare -- visible directly below. *)
Compute print_expr motion_report_expr.

Corollary motion_report_json_roundtrip :
  parse_expr_top (print_expr motion_report_expr) = Some (motion_report_expr, "").
Proof. json_roundtrip_corollary motion_report_expr motion_report_idents_valid. Qed.

Corollary motion_report_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate motion_report_expr)
      = option_map value_to_pyvalue (eval fuel rho motion_report_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: a real string literal, with the embedded
    quote escaped the way Python's own double-quoted syntax needs
    ([PyPrint.v]'s [py_escape_text]), not the bare, unescaped wrap
    [EField]'s/[ERecord]'s identifier-only keys still use. *)
Compute py_function "motion_report" ["state"] (translate motion_report_expr).

(** Run for real:

    [[
    >>> motion_report((-15, -30))
    'status: "landed"'
    >>> motion_report((35, -10))
    'status: still falling'
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * Example 15: a genuinely N-way mutually-recursive group *)

(** [ERecMut] (Example 10) only lets exactly two functions call each
    other. [ERecGroup] lifts that to an arbitrary number: [bounce3_expr]
    is Example 10's own bounce, with a *third* member, ["report"],
    added to the same group -- so ["fall"] still hands off to
    ["rise"] once it lands, but ["rise"] now hands off again, to
    ["report"], which packages the final state as a named record
    (Example 9's [ERecordN]) instead of returning the bare pair. A
    genuine three-way chain (["fall"] calls ["rise"] calls ["report"]),
    not two independent pairs -- exercising the actual cross-call
    mechanics a 2-way [ERecMut] can't exhibit. [ERecGroup] evaluates to
    a [VRecordN] of closures (Lang.v's own comment), so a member is
    picked out with [EFieldN] -- the *same* accessor a plain
    [ERecordN] field already uses, not a new one. *)
Definition bounce3_fall_body : expr :=
  EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
      (EApp (EVar "rise") (EVar "state"))
      (EApp (EVar "fall") euler_multi_step_body).

Definition bounce3_rise_body : expr :=
  EApp (EVar "report") (EPair (EFst (EVar "state")) (ESub (EConst 0) (ESnd (EVar "state")))).

Definition bounce3_report_body : expr :=
  ERecordN [("x", EFst (EVar "state")); ("v", ESnd (EVar "state"))].

Definition bounce3_expr : expr :=
  ERecGroup [
    ("fall", "state", bounce3_fall_body);
    ("rise", "state", bounce3_rise_body);
    ("report", "state", bounce3_report_body)
  ].

Theorem bounce3_idents_valid :
  expr_idents_valid is_valid_ident bounce3_expr = true.
Proof. reflexivity. Qed.

(** Same drop as Example 10 (height 45, "gravity" [a = -10], [dt = 1]):
    lands at [(-15, -30)], ["rise"] reflects the velocity to [30], and
    ["report"] -- the new third member -- wraps the result as
    [{"x": -15, "v": 30}] instead of a bare pair. *)
Example bounce3_concrete :
  eval 100 [("a", VZ (-10)); ("dt", VZ 1)]
    (EApp (EFieldN "fall" bounce3_expr) (EPair (EConst 45) (EConst 0)))
    = Some (VRecordN [("x", VZ (-15)); ("v", VZ 30)]).
Proof. reflexivity. Qed.

Compute print_expr (EApp (EFieldN "fall" bounce3_expr) (EPair (EConst 45) (EConst 0))).

Corollary bounce3_json_roundtrip :
  parse_expr_top (print_expr (EApp (EFieldN "fall" bounce3_expr) (EPair (EConst 45) (EConst 0))))
    = Some (EApp (EFieldN "fall" bounce3_expr) (EPair (EConst 45) (EConst 0)), "").
Proof.
  json_roundtrip_corollary
    (EApp (EFieldN "fall" bounce3_expr) (EPair (EConst 45) (EConst 0)))
    bounce3_idents_valid.
Qed.

Corollary bounce3_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate bounce3_expr)
      = option_map value_to_pyvalue (eval fuel rho bounce3_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: all three closures are built together, via
    three chained walrus assignments ending in a [dict] instead of
    [ERecMut]'s own pair (PyPrint.v's comment on [PRecGroup]) -- a
    member is called by reading it back out of that [dict] by name. *)
Compute py_function "bounce3" ["a"; "dt"] (translate bounce3_expr).

(** Run for real:

    [[
    >>> bounce3(-10, 1)["fall"]((45, 0))
    {'x': -15, 'v': 30}
    ]]
*)
