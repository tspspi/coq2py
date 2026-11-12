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
today (integer/boolean arithmetic, variables, pairs, a let-binding) — see
[roadmap.md](roadmap.md) for what isn't covered yet (floats/numpy, arrays
and loops, a broader Gallina surface).

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

## Try it yourself

```
make all   # builds the Coq proofs, extracts, builds the OCaml CLI
make test  # runs the CLI against both examples above
```
