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
  supported Gallina subset (`Lang.v`: integers, booleans, pairs,
  comparisons, `if`, `let`) to the Python-subset AST (`PyLang.v`)
  preserves semantics, for every term and environment, unconditionally.
- **`Json.parse_print_roundtrip`** — the JSON-flavoured parser
  (`Json.v`) is a proven inverse of its own printer, over every term with
  valid identifiers.

Both are axiom-free. What's *not* proved — the final Python pretty-printer,
and the correspondence between this project's formal Python semantics and
real CPython's actual behaviour — is explained and justified in
[docs/duality.md](docs/duality.md), not left implicit.

## Building

```
make all    # builds the Coq proofs, extracts to OCaml, builds the CLI
make test   # runs the CLI end-to-end against examples/Kinematics.v's terms
```

Requires `coqc`/`coq-stdlib`, OCaml, and `dune` — nothing beyond what's
already needed for ordinary Coq extraction (see GOAL.md's dependency
policy: deliberately no MetaCoq/coq-equations/bignum libraries).

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
