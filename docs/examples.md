# Walkthrough: a Coq proof to a running Python function

This walks through [`examples/Kinematics.v`](../examples/Kinematics.v) end
to end. Every piece of output below is real — copy-pasted from actually
running `coqc`, `dune exec`, and `python3` on this repository, not
hand-written to illustrate the idea. See [duality.md](duality.md) for the
theory this is an instance of.

## Example 1: one Euler step, returning a pair

The example is one step of semi-implicit ("symplectic") Euler integration
— update velocity first, then use the *new* velocity to update position,
returning both:

$$
v' = v + a \cdot \Delta t, \qquad x' = x + v' \cdot \Delta t, \qquad \text{result} = (x', v')
$$

expressed as a value of this project's supported `expr` subset
(`Lang.v`):

```coq
Definition euler_step_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (EPair (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))) (EVar "v2")).
```

This stays inside the subset the proofs in this repository actually cover
today (integer/boolean/float arithmetic, variables, pairs, a
let-binding) — see [roadmap.md](roadmap.md) for what isn't covered yet
(numpy-shaped arrays and bounded iteration/loops, a broader Gallina
surface).

### Step 1 — it means what it should

```coq
Example euler_step_concrete :
  eval [("x", VZ 0); ("v", VZ 0); ("a", VZ 2); ("dt", VZ 1)] euler_step_expr
    = Some (VPair (VZ 2) (VZ 2)).
Proof. reflexivity. Qed.
```

Starting at rest with acceleration 2 for one unit step, the new state
`(x', v')` is `(2, 2)` — checked by Coq's own kernel via `reflexivity`,
not asserted. (`eval` returns a `value` — `VZ`/`VBool`/`VPair` — not a
bare integer, since the language now has booleans and pairs too; see
[duality.md](duality.md).)

### Step 2 — JSON encoding

```coq
Compute print_expr euler_step_expr.
```

```
= "{""tag"":""let"",""name"":""v2"",""value"":{""tag"":""add"",""lhs"":{""tag"":""var"",""name"":""v""},""rhs"":{""tag"":""mul"",""lhs"":{""tag"":""var"",""name"":""a""},""rhs"":{""tag"":""var"",""name"":""dt""}}},""body"":{""tag"":""pair"",""fst"":{""tag"":""add"",""lhs"":{""tag"":""var"",""name"":""x""},""rhs"":{""tag"":""mul"",""lhs"":{""tag"":""var"",""name"":""v2""},""rhs"":{""tag"":""var"",""name"":""dt""}}},""snd"":{""tag"":""var"",""name"":""v2""}}}"
     : string
```

(The doubled `""` is Coq's own string-literal escaping for a literal `"`
character in the *source* of the `Compute` command — the actual string
value contains ordinary single quotes, as the parse step below confirms.)

### Step 3 — the parser really does invert the printer

```coq
Compute parse_expr_top (print_expr euler_step_expr).
```

```
= Some
    (ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
       (EPair (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt")))
          (EVar "v2")), "")
     : option (expr * string)
```

The exact original term comes back, paired with an empty leftover string
(nothing left unparsed). This isn't a coincidence specific to this term —
it's `Json.parse_print_roundtrip` (proved for *every* `expr` with valid
identifiers) instantiated here, stated in the example file as a corollary
rather than a new proof:

```coq
Corollary euler_step_json_roundtrip :
  parse_expr_top (print_expr euler_step_expr) = Some (euler_step_expr, "").
```

### Step 4 — translation to the Python-subset AST, and why it's trustworthy

```coq
Compute py_function "euler_step" ["x"; "v"; "a"; "dt"] (translate euler_step_expr).
```

```
= "def euler_step(x, v, a, dt):
    return ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1]
"
     : string
```

That this generated code *behaves* like `euler_step_expr` isn't something
to take on faith from reading it — it's `Translate.translate_preserves_semantics`,
again stated as a corollary rather than reproved (the `env_to_pyenv` /
`option_map value_to_pyvalue` plumbing is exactly the "translate the
environment and the result value the same structural way" bookkeeping
this needs now that values are more than bare integers):

```coq
Corollary euler_step_translation_correct :
  forall rho,
    peval (env_to_pyenv rho) (translate euler_step_expr)
      = option_map value_to_pyvalue (eval rho euler_step_expr).
```

(The walrus-operator rendering of the `let`, and the plain Python tuple
for the pair, are the one part of this whole pipeline that is *not*
proved — see [duality.md](duality.md)'s discussion of `PyPrint.v`. Both
are standard, valid Python, just not the most idiomatic hand-written
style.)

### Step 5 — the actual, standalone tool, and it actually runs

```
$ echo -n '{"tag":"let","name":"v2","value":{"tag":"add","lhs":{"tag":"var","name":"v"},"rhs":{"tag":"mul","lhs":{"tag":"var","name":"a"},"rhs":{"tag":"var","name":"dt"}}},"body":{"tag":"pair","fst":{"tag":"add","lhs":{"tag":"var","name":"x"},"rhs":{"tag":"mul","lhs":{"tag":"var","name":"v2"},"rhs":{"tag":"var","name":"dt"}}},"snd":{"tag":"var","name":"v2"}}}' \
  | dune exec driver/main.exe -- euler_step x,v,a,dt
def euler_step(x, v, a, dt):
    return ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1]
```

Byte-for-byte the same output as the in-Coq `Compute` above, as it should
be — the CLI just drives the extracted version of the same proven
functions. And it runs:

```
$ python3 -c "
def euler_step(x, v, a, dt):
    return ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1]
print(euler_step(0, 0, 2, 1))
"
(2, 2)
```

Matching the `(2, 2)` proved in step 1 — not just structurally
translated, but numerically correct when actually executed.

## Example 2: general comparisons and booleans

A second term exercises `<`/`<=`/`=`-style comparisons and boolean
connectives directly (not the old "test equals zero" hack this subset
used to be limited to): "has the projectile reached or passed ground
level while still moving downward?"

```coq
Definition landed_expr : expr :=
  EAnd (ELe (EVar "x") (EConst 0)) (ELt (EVar "v") (EConst 0)).
```

Three concrete checks (landed; still above ground; on/below ground but
rising) are each proved by `reflexivity`:

```coq
Example landed_concrete_true :
  eval [("x", VZ (-1)); ("v", VZ (-3))] landed_expr = Some (VBool true).
Example landed_concrete_false_still_above_ground :
  eval [("x", VZ 5); ("v", VZ (-3))] landed_expr = Some (VBool false).
Example landed_concrete_false_rising :
  eval [("x", VZ (-1)); ("v", VZ 3)] landed_expr = Some (VBool false).
```

Generated Python:

```coq
Compute py_function "landed" ["x"; "v"] (translate landed_expr).
```

```
= "def landed(x, v):
    return ((x <= 0) and (v < 0))
"
     : string
```

And, run for real against the same three cases as the proofs above:

```
$ python3 -c "
def landed(x, v):
    return ((x <= 0) and (v < 0))
print(landed(-1, -3), landed(5, -3), landed(-1, 3))
"
True False False
```

Matching `true`, `false`, `false` exactly as proved.

## Example 3: the same Euler step, in real floats

The exact same integration step as Example 1, but over `PrimFloat.float`
state (`EFAdd`/`EFMul` instead of `EAdd`/`EMul`) rather than `Z` standing
in for it:

```coq
Definition euler_step_float_expr : expr :=
  ELet "v2" (EFAdd (EVar "v") (EFMul (EVar "a") (EVar "dt")))
    (EPair (EFAdd (EVar "x") (EFMul (EVar "v2") (EVar "dt"))) (EVar "v2")).
```

No separate proof effort was needed for any of this — `translate_preserves_semantics`
and `parse_print_roundtrip` already hold for every `expr`, float
constructors included, so the same `reflexivity`-proved concrete check,
JSON round-trip corollary, and translation-correctness corollary from
Example 1 carry over directly:

```coq
Example euler_step_float_concrete :
  eval [("x", VFloat 0.0); ("v", VFloat 0.0); ("a", VFloat 2.0); ("dt", VFloat 1.0)]
    euler_step_float_expr
    = Some (VPair (VFloat 2.0) (VFloat 2.0)).
Proof. reflexivity. Qed.
```

JSON encoding:

```
= "{""tag"":""let"",""name"":""v2"",""value"":{""tag"":""fadd"",""lhs"":{""tag"":""var"",""name"":""v""},""rhs"":{""tag"":""fmul"",""lhs"":{""tag"":""var"",""name"":""a""},""rhs"":{""tag"":""var"",""name"":""dt""}}},""body"":{""tag"":""pair"",""fst"":{""tag"":""fadd"",""lhs"":{""tag"":""var"",""name"":""x""},""rhs"":{""tag"":""fmul"",""lhs"":{""tag"":""var"",""name"":""v2""},""rhs"":{""tag"":""var"",""name"":""dt""}}},""snd"":{""tag"":""var"",""name"":""v2""}}}"
     : string
```

Generated Python (same walrus-operator rendering as Example 1 — these
variables stay symbolic, so there's no float literal to render here):

```
= "def euler_step_float(x, v, a, dt):
    return ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1]
"
     : string
```

Run for real:

```
$ echo -n '{"tag":"let","name":"v2","value":{"tag":"fadd","lhs":{"tag":"var","name":"v"},"rhs":{"tag":"fmul","lhs":{"tag":"var","name":"a"},"rhs":{"tag":"var","name":"dt"}}},"body":{"tag":"pair","fst":{"tag":"fadd","lhs":{"tag":"var","name":"x"},"rhs":{"tag":"fmul","lhs":{"tag":"var","name":"v2"},"rhs":{"tag":"var","name":"dt"}}},"snd":{"tag":"var","name":"v2"}}}' \
  | dune exec driver/main.exe -- euler_step_float x,v,a,dt
def euler_step_float(x, v, a, dt):
    return ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1]
$ python3 -c "
def euler_step_float(x, v, a, dt):
    return ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1]
print(euler_step_float(0.0, 0.0, 2.0, 1.0))
"
(2.0, 2.0)
```

When an `EFConst` literal *does* appear directly in a term (rather than
coming in as a function argument, as `x`/`v`/`a`/`dt` do above),
`py_function`'s renderer emits it as an exact `mantissa * (2.0 **
exponent)` expression rather than a decimal literal — e.g. `EFConst 1.5`
prints as `(6755399441055744 * (2.0 ** -52))`, which Python evaluates
back to exactly `1.5`, bit for bit. See `PyPrint.v`'s comment for why
that's the easy, exact choice here, where a decimal pretty-printer would
be the genuinely hard one.

`EFEq`/`EFLt`/`EFLe` give floats the same comparisons integers already
had. `landed_float_expr` is `landed_expr` (Example 2) with `EFLe`/`EFLt`
in place of `ELe`/`ELt`:

```
def landed_float(x, v):
    return ((x <= 0.0) and (v < 0.0))
```

## Example 5: a multi-step trajectory, via bounded iteration

`ERepeat n x body init` applies `body` to `init` `n` times in a row —
`n` a compile-time `nat`, not a runtime value. `euler_multi_step_expr`
chains `euler_step_expr` (Example 1) this way, computing a whole
trajectory *inside* the proven subset, with no external loop:

```coq
Definition euler_multi_step_expr (n : nat) : expr :=
  ERepeat n "state" euler_multi_step_body (EPair (EVar "x0") (EVar "v0")).
```

Three steps from rest with acceleration 2: `(0,0) -> (2,2) -> (6,4) -> (12,6)`,
checked the same `reflexivity` way as every earlier example. The
generated Python literally unrolls the loop (see `PyPrint.v`'s `PRepeat`
comment for why that's correct and not just a size hack):

```
def euler_trajectory_3(x0, v0, a, dt):
    return ((state := (x0, v0)), (state := ((x := (state)[0]), ((v := (state)[1]), ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1])[1])[1]), (state := ((x := (state)[0]), ((v := (state)[1]), ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1])[1])[1]), (state := ((x := (state)[0]), ((v := (state)[1]), ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1])[1])[1]), state)[-1]
```

Run for real: `euler_trajectory_3(0, 0, 2, 1)` gives `(12, 6)`, matching
the proof.

## Example 6: a precondition, proved and reflected in Python

Time to stop, decelerating at rate `d` from speed `v`: `t = v / d`,
meaningful only for `d <> 0`. `EDiv` is built the same way — `eval` gets
*stuck* (not some default answer) on a zero divisor:

```coq
Definition time_to_stop_expr : expr := EDiv (EVar "v") (EVar "d").

Example time_to_stop_concrete : eval [("v", VZ 20); ("d", VZ 4)] time_to_stop_expr = Some (VZ 5).
Example time_to_stop_zero_deceleration : eval [("v", VZ 20); ("d", VZ 0)] time_to_stop_expr = None.
```

`eval_div_correct` (Lang.v) is the proof that, given the precondition
`d <> 0`, this computes exactly `Z.div v d`. The generated Python needs
no extra validation code for that precondition at all:

```
def time_to_stop(v, d):
    return (v // d)
```

```
>>> time_to_stop(20, 4)
5
>>> time_to_stop(20, 0)
ZeroDivisionError: integer division or modulo by zero
```

Python's own `//` already raises on a zero divisor — the same
undefined case `eval` already refuses to answer, enforced by the target
language for free. (Compare Example 13's wave simulator: there, the CFL
precondition *isn't* automatically enforced by anything, so
`wave1d.py` has to check it explicitly — the two examples are opposite
ends of the same idea.)

## Example 7: run until it actually lands, via real recursion

Example 5 chained a *fixed* number of Euler steps (`ERepeat`). Here, the
step count depends on the data — when does the object actually land? —
which needs real recursion, `ERec`, reusing the step function and
landing condition from Examples 5 and 2 unchanged:

```coq
Definition fall_until_landed_expr : expr :=
  ERec "simulate" "state"
    (EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
         (EVar "state")
         (EApp (EVar "simulate") euler_multi_step_body)).
```

Dropped from height 45 under `a = -10`, `dt = 1`: `(45,0) -> (35,-10) ->
(15,-20) -> (-15,-30)`, landing on step 3 — checked with generous fuel
(`eval 100 ...`), and shown to genuinely need *some* fuel (`eval 3 ...`
runs out and gets stuck, same as an unbound variable would). The
generated Python is a real recursive closure (see `PyPrint.v`'s `PRec`
comment for the walrus-self-reference trick that makes this work with
no textual substitution):

```
def fall_until_landed(a, dt):
    return ((simulate := (lambda state: (state if (((state)[0] <= 0) and ((state)[1] < 0)) else (simulate(((x := (state)[0]), ((v := (state)[1]), ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1])[1])[1]))))), simulate)[-1]
```

```
>>> f = fall_until_landed(-10, 1)
>>> f((45, 0))
(-15, -30)
```

## Example 8: a Riemann sum over a genuine list

`ENil`/`ECons`/`EListMatch` add lists — the first value shape here whose
size isn't fixed by the term's own syntax. `total_distance_expr` sums
`v * dt` over a list of velocity samples of whatever length it has,
via `ERec` walking an `EListMatch`:

```coq
Definition total_distance_expr : expr :=
  ERec "total" "vs"
    (EListMatch (EVar "vs") (EConst 0) "v" "rest"
       (EAdd (EMul (EVar "v") (EVar "dt")) (EApp (EVar "total") (EVar "rest")))).
```

Samples `2, 4, 6` over unit time steps: `2*1 + 4*1 + 6*1 = 12`. Lists
render as nested Python tuples (`()` is `Nil`, `(hd, tl)` is `Cons` —
the same shape pairs already use, not Python's native `list`; see
`PyPrint.v`'s comment on `PListMatch`):

```
def total_distance(dt):
    return ((total := (lambda vs: (0 if (vs) == () else ((v := (vs)[0]), (rest := (vs)[1]), ((v * dt) + (total(rest))))[-1]))), total)[-1]
```

```
>>> f = total_distance(1)
>>> f((2, (4, (6, ()))))
12
```

## Example 9: the same Euler step, returning a named record

`ERecord k1 e1 k2 e2`/`EField name e` add 2-field named records — deliberately
capped at two fields (nesting handles more, the same way `EPair` is
capped at two components; see [roadmap.md](roadmap.md) for why).
`euler_step_record_expr` is Example 1's step again, but returning the
new state as `{"x": ..., "v": ...}` instead of a positional pair:

```coq
Definition euler_step_record_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (ERecord "x" (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))) "v" (EVar "v2")).
```

Same motion as Example 1 — starting at rest with acceleration 2 for one
step of `dt=1`, the new state is `{"x": 2, "v": 2}`:

```coq
Example euler_step_record_concrete :
  eval 10 [("x", VZ 0); ("v", VZ 0); ("a", VZ 2); ("dt", VZ 1)] euler_step_record_expr
    = Some (VRecord "x" (VZ 2) "v" (VZ 2)).
Proof. reflexivity. Qed.
```

A record renders as a Python `dict` literal, looked up by field name
rather than by position:

```
def euler_step_record(x, v, a, dt):
    return ((v2 := (v + (a * dt))), {"x": (x + (v2 * dt)), "v": v2})[1]
```

```
>>> euler_step_record(0, 0, 2, 1)
{'x': 2, 'v': 2}
```

## Example 10: an elastic bounce, via mutual recursion

`ERecMut f1 param1 body1 f2 param2 body2` is `ERec`'s mutual-recursion
cousin — two functions defined *together*, so each may call either of
themselves, not just `ERec`'s single self-call. `bounce_expr` reuses
Example 7's step function: `"fall"` runs Euler steps until the
projectile would go below ground, then hands off to `"rise"`, which
reflects the velocity (a perfectly elastic bounce) and returns:

```coq
Definition bounce_fall_body : expr :=
  EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
      (EApp (EVar "rise") (EVar "state"))
      (EApp (EVar "fall") euler_multi_step_body).

Definition bounce_rise_body : expr :=
  EPair (EFst (EVar "state")) (ESub (EConst 0) (ESnd (EVar "state"))).

Definition bounce_expr : expr :=
  ERecMut "fall" "state" bounce_fall_body "rise" "state" bounce_rise_body.
```

`ERecMut` evaluates to a pair of the two closures (`EFst`/`ESnd` pick
out whichever is wanted — here, `"fall"`, the entry point). Dropped
from the same height as Example 7 (45, "gravity" `a = -10`, `dt = 1`):
three steps land at `(-15, -30)`, at which point `"fall"` hands off to
`"rise"`, which reflects the velocity to `30`:

```coq
Example bounce_concrete :
  eval 100 [("a", VZ (-10)); ("dt", VZ 1)]
    (EApp (EFst bounce_expr) (EPair (EConst 45) (EConst 0)))
    = Some (VPair (VZ (-15)) (VZ 30)).
Proof. reflexivity. Qed.
```

Both python renders both closures together via two chained walrus
assignments — the same self-reference trick `PRec` already uses for a
single function, extended to two names — then returns them as a pair:

```
def bounce(a, dt):
    return ((fall := (lambda state: ((rise(state)) if (((state)[0] <= 0) and ((state)[1] < 0)) else (fall(((x := (state)[0]), ((v := (state)[1]), ((v2 := (v + (a * dt))), ((x + (v2 * dt)), v2))[1])[1])[1]))))), (rise := (lambda state: ((state)[0], (0 - (state)[1])))), (fall, rise))[-1]
```

```
>>> fall, rise = bounce(-10, 1)
>>> fall((45, 0))
(-15, 30)
```

## Example 11: a precondition reflected as a value, via a sum type

Example 6's `time_to_stop_expr` reflects its precondition (`d <> 0`)
by getting *stuck* (`None`) when it fails. `EInl`/`EInr`/`ECase` let
the same precondition be reflected as an ordinary value instead:
`safe_time_to_stop_expr` returns `EInl time` when `d <> 0`, or
`EInr v` (the velocity, which will now never reach zero) when `d = 0`
— a *total* function whose result says, at the type level, which case
happened:

```coq
Definition safe_time_to_stop_expr : expr :=
  EIf (EEq (EVar "d") (EConst 0))
      (EInr (EVar "v"))
      (EInl (EDiv (EVar "v") (EVar "d"))).

Definition stop_time_or_minus_one_expr : expr :=
  ECase safe_time_to_stop_expr "t" (EVar "t") "_" (ESub (EConst 0) (EConst 1)).
```

`ECase` is the eliminator, substituting a concrete reading for either
outcome (the real stopping time, or `-1` for "never stops"). Same
numbers as Example 6 — decelerating by 4 per step from speed 20 takes
5 steps to stop, now a genuine `VInl`, not a `Some` wrapping a bare
number; zero deceleration is a real, distinguishable `VInr`, not `None`:

```coq
Example safe_time_to_stop_concrete :
  eval 10 [("v", VZ 20); ("d", VZ 4)] safe_time_to_stop_expr = Some (VInl (VZ 5)).
Proof. reflexivity. Qed.

Example safe_time_to_stop_zero_deceleration :
  eval 10 [("v", VZ 20); ("d", VZ 0)] safe_time_to_stop_expr = Some (VInr (VZ 20)).
Proof. reflexivity. Qed.
```

A sum value renders as a tagged 2-tuple (`("inl", v)`/`("inr", v)`),
and `ECase` as a conditional on that tag, binding the payload with the
same walrus trick `EListMatch` already uses:

```
def stop_time_or_minus_one(v, d):
    return (((t := ((("inr", v) if (d == 0) else ("inl", (v // d))))[1]), t)[-1] if ((("inr", v) if (d == 0) else ("inl", (v // d))))[0] == "inl" else ((_ := ((("inr", v) if (d == 0) else ("inl", (v // d))))[1]), (0 - 1))[-1])
```

```
>>> stop_time_or_minus_one(20, 4)
5
>>> stop_time_or_minus_one(20, 0)
-1
```

## Example 12: a genuine string value, labelling a motion phase

`EStrConst`/`EStrConcat`/`EStrEq` add a fifth scalar value, `VStr` —
real strings, not just the identifiers `var` was already used for
everywhere else. `motion_phase_expr` reuses `landed_expr`'s condition
(Example 2) to label a state `(x, v)` with a word instead of just a
bool:

```coq
Definition motion_phase_expr : expr :=
  EIf (EAnd (ELe (EFst (EVar "state")) (EConst 0)) (ELt (ESnd (EVar "state")) (EConst 0)))
      (EStrConst "landed")
      (EStrConst "falling").

Definition is_landed_label_expr : expr :=
  EStrEq motion_phase_expr (EStrConst "landed").
```

The same two states Example 10's bounce distinguishes by position —
`(-15, -30)` (landed) and `(35, -10)` (still falling) — are now
distinguished by a real string, compared with `EStrEq`:

```coq
Example motion_phase_landed :
  eval 10 [("state", VPair (VZ (-15)) (VZ (-30)))] motion_phase_expr = Some (VStr "landed").
Proof. reflexivity. Qed.
```

A string value renders as a plain Python string literal, and
`EStrConcat`/`EStrEq` as `+`/`==` — nothing exotic, the same honest
restriction to identifier-shaped text `quote_string`/`parse_qstring`
already have:

```
def is_landed_label(state):
    return (("landed" if ((state)[0] <= 0) and ((state)[1] < 0) else "falling") == "landed")
```

```
>>> is_landed_label((-15, -30))
True
>>> is_landed_label((35, -10))
False
```

## Example 13: a wave simulator, from Maxwell's equations to a running plot

This walks through [`examples/physics/Discretize.v`](../examples/physics/Discretize.v)
and [`runtime/wave1d.py`](../runtime/wave1d.py) — a longer chain than
Examples 1–3, going from [`Maxwell.v`](../examples/physics/Maxwell.v)'s
`wave_equation_E` theorem, through a discretized scheme with its own
consistency proof, through extraction, to an actually-running numpy
simulation with a real plot. See [roadmap.md](roadmap.md)'s
"Electromagnetism example" entry for exactly what is and isn't proved at
each stage.

### The scheme and its consistency proof

The standard explicit ("leapfrog") finite-difference scheme for the
scalar wave equation `u_tt = c^2 u_xx`:

```coq
Definition courant_sq (c dt dx : R) : R := (c * c * dt * dt) / (dx * dx).

Definition leapfrog_update (r u_prev u_left u_center u_right : R) : R :=
  2 * u_center - u_prev + r * (u_left - 2 * u_center + u_right).
```

"This scheme is second-order accurate" is usually a citation to a
Taylor-expansion argument taken on faith. Here it's an actual theorem:
given the continuous wave equation at a point (`b2 = c*c*a2`, i.e.
`wave_equation_E`'s conclusion restated via Taylor coefficients) and that
the true solution matches its own third-order Taylor expansion there —
both in space and in time, exactly what "the solution is smooth" buys
locally — the discrete update recovers the *exact* next-time-step value:

```coq
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
```

Proved by `field` over `R` — the same `Print Assumptions` axioms as every
other `R`-based theorem in this repository (`ClassicalDedekindReals`,
`functional_extensionality_dep`, both from Coq's own `Reals` library, not
introduced by this project):

```
Axioms:
ClassicalDedekindReals.sig_forall_dec : ...
FunctionalExtensionality.functional_extensionality_dep : ...
```

### The same formula, as a proven, extracted `expr` term

```coq
Definition leapfrog_update_expr : expr :=
  EFAdd
    (EFSub (EFMul (EFConst 2) (EVar "u_center")) (EVar "u_prev"))
    (EFMul (EVar "r")
      (EFSub (EFAdd (EVar "u_left") (EVar "u_right"))
             (EFMul (EFConst 2) (EVar "u_center")))).
```

`leapfrog_update_expr_json_roundtrip` and
`leapfrog_update_translation_correct` are corollaries of the same two
general theorems (`parse_print_roundtrip`, `translate_preserves_semantics`)
every other example in this repository uses — no new proof needed for
this term to be trustworthy. Generated Python:

```
def leapfrog_update(r, u_prev, u_left, u_center, u_right):
    return ((((4503599627370496 * (2.0 ** -51)) * u_center) - u_prev) + (r * ((u_left + u_right) - ((4503599627370496 * (2.0 ** -51)) * u_center))))
```

(`4503599627370496 * (2.0 ** -51)` is exactly `2.0` — the exact-float
literal encoding described above, applied to a literal `2` this time
instead of `1.5`.)

### The external runtime, actually running it

```
$ make wave_sim
...
grid points: 400, dt: 0.005, snapshots: 9
sum(u^2) at t=0: 8.86227, at t=8: 8.55961
(a genuine wave equation solution should split the initial pulse into two
counter-propagating humps of about half the original peak height each,
reflecting off the fixed Dirichlet boundaries -- see wave1d.png)
wrote runtime/wave1d.png
```

`runtime/wave1d.py` is hand-written, unproven glue (array allocation,
Dirichlet boundary conditions, the time-stepping loop) — the same trust
category as `ocaml/driver/main.ml` or `PyPrint.v`'s printer — but the
per-point arithmetic it runs, every single step, is the literal function
`make wave_sim` generated above, imported and called unmodified (passing
whole numpy array slices instead of scalars, which works because the
generated body is plain `+`/`-`/`*`/`**`). The resulting plot (not
committed — generated fresh by `make wave_sim` at `runtime/wave1d.png`):

![wave1d.png](../runtime/wave1d.png)

A pulse starting at `x=1` splits into two half-height counter-propagating
waves, each reflects off a fixed (`u=0`) boundary, and — because the
domain length and wave speed were chosen so the round-trip time `2L/c`
is almost exactly `8` time units — the two halves refocus back into
(almost) the original pulse by `t=8`. That refocusing is a real,
independently-checkable physical prediction of the wave equation on a
finite domain with fixed ends, not just "the simulation didn't blow up" —
seeing it land where predicted is a meaningful check that the extracted
formula, the runtime's grid/loop plumbing, and the boundary conditions
are all actually correct together, not just individually plausible.

### What the proof doesn't cover, turned into a runtime check

`leapfrog_exact_for_cubic_profile` has two hypotheses (`dx <> 0`,
`b2 = c*c*a2`) and is silent about a third thing every reader of
numerical PDE code eventually needs: the Courant-Friedrichs-Lewy (CFL)
condition `c*dt/dx <= 1`, required for repeated application of this
scheme to stay bounded rather than blow up — not proved anywhere in this
repository (see `Discretize.v`'s comment on that theorem). Rather than
let a violation silently produce numerically meaningless output,
`wave1d.py`'s `validate_parameters` checks it (and `dx > 0`, `c > 0`)
before running, raising a plain error instead:

```
$ python3 -c "from wave1d import run_simulation; run_simulation(cfl=1.5)"
ValueError: CFL condition violated: c*dt/dx = 1.5 > 1 (leapfrog_exact_for_cubic_profile
says nothing about stability -- see Discretize.v's comment -- so this is not
something a proof catches for you)
```

## Try it yourself

```
make all       # builds the Coq proofs, extracts, builds the OCaml CLI
make test      # runs the CLI against the Kinematics.v examples above
make physics   # checks Minkowski/Calculus/Maxwell/Discretize.v
make wave_sim  # generates + runs the Example 13 wave simulator, plots it
```
