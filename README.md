# coq2py

A certified Coq-to-Python extraction backend: a translator written and
*proved correct* in Gallina, extracted to OCaml via Coq's own extraction
mechanism, rather than a hand-written, unverified code generator.

See [GOAL.md](GOAL.md) for the project's scope and architecture,
[docs/duality.md](docs/duality.md) for the theory (proofs-as-programs,
what extraction actually preserves, and exactly where this project's
trust boundary is drawn), [docs/examples.md](docs/examples.md) for a full
worked example from a Coq term to a running Python function, and
[docs/roadmap.md](docs/roadmap.md) for an honest list of what isn't built
yet.

> **Note:** this project was mainly vibe coded with
> [Claude Code](https://claude.com/claude-code). The Coq proofs
> themselves are machine-checked by `coqc` regardless of how they were
> written — `Print Assumptions` on the two main theorems reports "Closed
> under the global context" (no admitted lemmas, no extra axioms) — but
> you should read the code with that provenance in mind rather than
> assume any particular human has reviewed every line.

## What's actually proved here

- **`Translate.translate_preserves_semantics`** — the translation from the
  supported Gallina subset (`Lang.v`: integers, booleans, floats, pairs,
  comparisons, `if`, `let`, bounded iteration, functions/closures and
  self-recursion) to the Python-subset AST (`PyLang.v`) preserves
  semantics, for every term, environment, and amount of evaluation fuel,
  unconditionally.
- **`Json.parse_print_roundtrip`** — the JSON-flavoured parser
  (`Json.v`) is a proven inverse of its own printer, over every term with
  valid identifiers.

Neither relies on any axiom *of this project's own introduction*; `Print
Assumptions` on both does report a short list, but every entry is either a
Coq primitive type/operation (`PrimFloat`/`PrimInt63` — trusted at the
same level as the kernel's native `Z`/`bool`, not a project-specific
assumption) or, for `Json.parse_print_roundtrip` only,
`FloatAxioms.SF2Prim_Prim2SF` — a standard-library axiom asserting Coq's
own float-decomposition functions round-trip, used by `Json.v`'s float
JSON codec (see its comment) and in the same trust category as the kernel
itself. What's *not* proved — the final Python pretty-printer, and the
correspondence between this project's formal Python semantics (and
`PrimFloat`'s own IEEE-754 semantics) and real CPython's actual behaviour
— is explained and justified in [docs/duality.md](docs/duality.md), not
left implicit.

## Building

```
make all       # builds the Coq proofs, extracts to OCaml, builds the CLI
make test      # runs the CLI end-to-end against examples/Kinematics.v's terms
make physics   # checks the Minkowski/Calculus/Maxwell/Discretize.v example
make wave_sim  # extracts + runs the Discretize.v wave simulator, plots it
```

Requires `coqc`/`coq-stdlib`, OCaml, and `dune` for the first three —
nothing beyond what's already needed for ordinary Coq extraction (see
GOAL.md's dependency policy: deliberately no MetaCoq/coq-equations/bignum
libraries). `make wave_sim` additionally needs `numpy` (required) and
`matplotlib` (optional — skipped with a message if absent) to run
`runtime/wave1d.py`, the hand-written, unproven external runtime
described in [docs/examples.md](docs/examples.md)'s Example 13 and
[docs/roadmap.md](docs/roadmap.md)'s electromagnetism entry.

If your system's default `make` is BSD make (as on FreeBSD), use `gmake`
instead — `coqc`'s own generated build conventions assume GNU make.

## Using the CLI

```
echo -n '<json-encoded expr>' | ocaml/_build/default/driver/main.exe <function-name> <param1,param2,...>
```

prints the generated Python function to stdout. See
[docs/examples.md](docs/examples.md) for a full worked example of
producing that JSON and running the result.

## Layout

```
coq/        Lang.v, PyLang.v, Translate.v, Json.v, PyPrint.v, Extract.v
examples/   Kinematics.v -- the running physics example
ocaml/      dune project wrapping the extracted pipeline in a CLI
docs/       duality.md, examples.md, roadmap.md
GOAL.md     project scope, architecture, and the trust boundary
```
