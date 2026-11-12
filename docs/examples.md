# Walkthrough: a Coq proof to a running Python function

This walks through [`examples/Kinematics.v`](../examples/Kinematics.v) end
to end. Every piece of output below is real — copy-pasted from actually
running `coqc`, `dune exec`, and `python3` on this repository, not
hand-written to illustrate the idea. See [duality.md](duality.md) for the
theory this is an instance of.

## The source term

The example is one step of semi-implicit ("symplectic") Euler integration
— update velocity first, then use the *new* velocity to update position:

$$
v' = v + a \cdot \Delta t, \qquad x' = x + v' \cdot \Delta t
$$

expressed as a value of this project's supported `expr` subset
(`Lang.v`):

```coq
Definition euler_step_expr : expr :=
  ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
    (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))).
```

This term is small enough to express the whole physics step, and it stays
inside the subset the proofs in this repository actually cover today
(integer arithmetic, variables, a let-binding) — see
[roadmap.md](roadmap.md) for what isn't covered yet (floats/numpy, richer
control flow, a broader Gallina surface).

## Step 1 — it means what it should

```coq
Example euler_step_concrete :
  eval [("x", 0); ("v", 0); ("a", 2); ("dt", 1)] euler_step_expr = Some 2.
Proof. reflexivity. Qed.
```

Starting at rest with acceleration 2 for one unit step, the new position is
2 — checked by Coq's own kernel via `reflexivity`, not asserted.

## Step 2 — JSON encoding

```coq
Compute print_expr euler_step_expr.
```

```
= "{""tag"":""let"",""name"":""v2"",""value"":{""tag"":""add"",""lhs"":{""tag"":""var"",""name"":""v""},""rhs"":{""tag"":""mul"",""lhs"":{""tag"":""var"",""name"":""a""},""rhs"":{""tag"":""var"",""name"":""dt""}}},""body"":{""tag"":""add"",""lhs"":{""tag"":""var"",""name"":""x""},""rhs"":{""tag"":""mul"",""lhs"":{""tag"":""var"",""name"":""v2""},""rhs"":{""tag"":""var"",""name"":""dt""}}}}"
     : string
```

(The doubled `""` is Coq's own string-literal escaping for a literal `"`
character in the *source* of the `Compute` command — the actual string
value contains ordinary single quotes, as the parse step below confirms.)

## Step 3 — the parser really does invert the printer

```coq
Compute parse_expr_top (print_expr euler_step_expr).
```

```
= Some
    (ELet "v2" (EAdd (EVar "v") (EMul (EVar "a") (EVar "dt")))
       (EAdd (EVar "x") (EMul (EVar "v2") (EVar "dt"))), "")
     : option (expr * string)
```

The exact original term comes back, paired with an empty leftover string
(nothing left unparsed). This isn't a coincidence specific to this term —
it's `Json.parse_print_roundtrip` (proved for *every* `expr` with valid
identifiers) instantiated here, stated in the example file as a one-line
corollary rather than a new proof:

```coq
Corollary euler_step_json_roundtrip :
  parse_expr_top (print_expr euler_step_expr) = Some (euler_step_expr, "").
```

## Step 4 — translation to the Python-subset AST, and why it's trustworthy

```coq
Compute py_function "euler_step" ["x"; "v"; "a"; "dt"] (translate euler_step_expr).
```

```
= "def euler_step(x, v, a, dt):
    return ((v2 := (v + (a * dt))), (x + (v2 * dt)))[1]
"
     : string
```

That this generated code *behaves* like `euler_step_expr` isn't something
to take on faith from reading it — it's `Translate.translate_preserves_semantics`,
again stated as a corollary rather than reproved:

```coq
Corollary euler_step_translation_correct :
  forall rho, peval rho (translate euler_step_expr) = eval rho euler_step_expr.
```

(The walrus-operator rendering of the `let` is the one part of this whole
pipeline that is *not* proved — see [duality.md](duality.md)'s discussion
of `PyPrint.v`. It's standard, valid Python 3.8+, just not the most
idiomatic hand-written style.)

## Step 5 — the actual, standalone tool

Everything above runs inside `coqc`. The same pipeline, extracted to OCaml
(`coq/Extract.v`) and wrapped in a small CLI (`ocaml/driver/main.ml`), is a
real binary that takes the JSON from step 2 on stdin:

```
$ echo -n '{"tag":"let","name":"v2","value":{"tag":"add","lhs":{"tag":"var","name":"v"},"rhs":{"tag":"mul","lhs":{"tag":"var","name":"a"},"rhs":{"tag":"var","name":"dt"}}},"body":{"tag":"add","lhs":{"tag":"var","name":"x"},"rhs":{"tag":"mul","lhs":{"tag":"var","name":"v2"},"rhs":{"tag":"var","name":"dt"}}}}' \
  | dune exec driver/main.exe -- euler_step x,v,a,dt
def euler_step(x, v, a, dt):
    return ((v2 := (v + (a * dt))), (x + (v2 * dt)))[1]
```

Byte-for-byte the same output as the in-Coq `Compute` above, as it should
be — the CLI just drives the extracted version of the same proven
functions.

## Step 6 — and it actually runs

```
$ python3 -c "
def euler_step(x, v, a, dt):
    return ((v2 := (v + (a * dt))), (x + (v2 * dt)))[1]
print(euler_step(0, 0, 2, 1))
"
2
```

Matching the `Some 2` proved in step 1 — not just structurally translated,
but numerically correct when actually executed.

## Try it yourself

```
make all   # builds the Coq proofs, extracts, builds the OCaml CLI
make test  # runs the CLI against this exact example
```
