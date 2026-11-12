# coq2py — Goals

## Motivation

Coq's extraction mechanism is the practice of **certified programming**: write a
specification and proof in Gallina, then mechanically erase the proof content
(`Prop`), keeping only the computational content as an executable program in a
target language. Coq ships extraction to OCaml, Haskell, and Scheme natively.
Python is not a built-in target.

`coq2py` is a from-scratch Coq → Python extraction backend, built with the goal
of proving the *translator itself* correct — not just trusting it the way the
existing OCaml/Haskell backends are trusted (soundly, but without a machine-checked
preservation proof).

## Goals

- A Coq→Python translator, written as Gallina functions, with a machine-checked
  theorem that translation preserves program behaviour relative to a formally
  specified semantics of the supported subset of Coq and the supported subset
  of Python.
- The translator is extracted to OCaml via Coq's standard, mature OCaml
  extraction backend (no custom/native Coq extraction plugin, no dependence on
  Coq's internal, version-unstable OCaml APIs).
- Input ingestion (source Coq program → data the translator can pattern-match
  on) goes through Coq's existing JSON extraction backend (ships in `coq-core`,
  zero extra dependency). The JSON parser is itself formally specified and
  proven correct — but **only against the restricted grammar of the supported
  Coq subset**, not general JSON or general Coq. This is acceptable scope: we
  never need to parse anything the JSON backend wouldn't emit for a program in
  our supported subset.
- Keep the dependency footprint minimal — deliberately avoid MetaCoq/MetaRocq,
  `coq-equations`, and similar heavy, version-pinned research libraries. See
  "Dependency policy" below.
- Run on two machines with different roles (see "Target environments").

## Non-goals (for now)

- Supporting all of Gallina. Start with a minimal subset (first-order
  functions, inductive/record types, structural recursion, pattern matching)
  and grow deliberately. Modules, typeclasses, coinductives, well-founded/
  `Program Fixpoint` recursion are out of scope until the core pipeline is
  proven and working.
- Supporting all of Python. Target a formally specified subset. A `numpy`
  subset is a plausible future extension but is **explicitly deferred** —
  array broadcasting, dtype/overflow behaviour, and view-vs-copy aliasing
  semantics are each a substantial formalization effort in their own right,
  bigger than the core Python subset.
- Proving that the real CPython (or numpy) interpreter conforms to the formal
  semantics we write down. That's an accepted, explicit trust boundary (the
  same kind CompCert draws around real hardware/assembly semantics) — not
  something this project attempts to discharge.

## Architecture (pipeline)

```
 user .v file
     │  (coqc, Extraction Language JSON — stock Coq, no extra dependency)
     ▼
 JSON (MiniML-derived IR, restricted to the supported Coq subset)
     │  parsed by a Gallina-defined parser, PROVEN correct
     │  against the subset's formal grammar
     ▼
 CoqIR   (Coq-defined inductive type)
     │  translate : CoqIR -> PyAST   — Gallina function, PROVEN to
     │  preserve semantics relative to formal Coq-subset / Python-subset
     │  operational semantics
     ▼
 PyAST  (Coq-defined inductive type for the Python-subset target)
     │  pretty-printer PyAST -> string  — structure-preserving;
     │  left unverified by default (open question, see below)
     ▼
 Python source text
```

The whole pipeline (parser + translator + printer) is a Gallina development,
extracted as one unit via `Extraction "coq2py.ml" ...` to get the actual CLI
tool.

## Trust boundary — what's proven vs. assumed

**Proven (machine-checked):**
- JSON parser correctness, against the formal grammar of the supported Coq
  subset's JSON serialization.
- `translate`'s semantic preservation, against formal operational semantics
  for the supported Coq subset and the supported Python subset.

**Assumed (same category of trust as any Coq development, or as CompCert's
own documented trust base):**
- Soundness of the Coq kernel/type-checker, including its primitive
  `PrimFloat.float`/`PrimInt63.int` types and operations (used by the
  float arithmetic in `Lang.v`/`PyLang.v`, and transitively by `Json.v`'s
  float JSON codec) — trusted at the same level as the kernel's native
  `Z`/`bool`, not a project-specific assumption.
- `FloatAxioms.SF2Prim_Prim2SF`, a Coq standard-library axiom asserting
  that `Prim2SF`/`SF2Prim` (float <-> sign/mantissa/exponent) round-trip,
  relied on by `Json.v`'s float codec round-trip proof — same trust
  category as the kernel itself, not an axiom this project introduces.
- Correctness of Coq's own JSON extraction backend as a *serializer* (i.e.
  that it faithfully emits the erased IR — same trust level the OCaml/Haskell
  backends already rely on today; not a regression).
- Correctness of Coq's standard OCaml extraction, used once to bootstrap the
  `coq2py` binary itself from the proven Gallina pipeline.
- Faithfulness of the formal Python-subset semantics (and `PrimFloat`'s
  own IEEE-754 semantics) to the real CPython interpreter's behaviour on
  programs in that subset. Explicitly out of scope to prove.
- Pretty-printer correctness (open question — see below).

## Target environments

| | Local dev machine | Remote deployment host |
|---|---|---|
| Role | Development: writing/proving the translator | Deployment: a theory-evaluating agent authors its own Coq proofs there at runtime, and needs `coq2py` to extract Python programs from them |
| Coq | 8.18.0 (coq-core/coq-stdlib) | 8.20.1 (coq-core/coq-stdlib) |
| OCaml | 4.14.1 | 4.14.2 |
| dune | 3.11.1 | 3.24.2 |
| Needs `coqc` installed? | Yes — building/proving the translator happens here | **Yes** — the agent's freshly-written `.v` files still need `coqc` on that host to type-check and emit the JSON IR (input-dependent, can't be pre-baked) |
| Needs to *rebuild* `coq2py` itself? | Yes (that's the point) | **No** — the proven translator is built and proved once here, extracted to OCaml, compiled, and the resulting binary is copied over; the remote host never re-proves or re-extracts it, so the Coq version skew (8.18.0 vs 8.20.1) only matters for the JSON IR shape `coqc` emits on each side, not for rebuilding the tool |

Work for now stays on the local machine. The remote host runs `coqc` (already
installed there) on the agent's own proofs to get JSON IR, then feeds that
IR to the already-built `coq2py` binary — it is a deployment target for the
tool, not a second build environment for it.

## Dependency policy

Minimize dependencies, especially since whatever we depend on to *build* the
tool should not need to be replicated on the remote host at all (deployment
there is binary-only).

- `coq-core` + `coq-stdlib` — already present on both machines, nothing to add.
- OCaml + `dune` + `ocamlfind` — already present on both machines.
- No MetaCoq/MetaRocq, no `coq-equations`: these pull in a multi-package,
  per-Coq-version-pinned dependency chain (confirmed the two machines would
  need *different* MetaCoq generations — 1.2.x for 8.18 vs 1.3.x for 8.20 —
  which is exactly the kind of version-skew risk we're avoiding by not
  depending on it). Design the `CoqIR` type so `translate` recurses
  structurally, avoiding any need for `Program Fixpoint`/`Equations`.
- JSON ingestion uses Coq's own stock JSON extraction backend as the producer;
  the consumer (parser) is hand-written Gallina, so no external JSON library
  is required either, since we only need to parse the exact restricted grammar
  our subset produces, not general JSON.

Net: the proven Gallina pipeline should build from nothing beyond what's
already installed on both machines today.

## Status

A first vertical slice is implemented and proven (see `coq/`, `examples/`,
`docs/`): an `expr` subset covering integer/boolean/float arithmetic,
comparisons, boolean connectives, a general `if`, pairs/tuples, and
non-recursive `let`, translated to a Python-subset AST with a proven
preservation theorem, round-tripped through a restricted JSON codec with
its own proven round-trip theorem, extracted to OCaml, and wrapped in a
working CLI that produces real, executing Python. `docs/examples.md`
walks through four worked examples (a pair-returning Euler integration
step over integers, a boolean/comparison-based landing check, and both
again over real `PrimFloat.float` state) with real captured output;
`docs/roadmap.md` tracks what's intentionally deferred.
A larger worked example lives in `examples/physics/`: Lorentz symmetry
(`Minkowski.v`), a symbolic calculus layer (`Calculus.v`), Maxwell's
equations and the wave equation derived from them (`Maxwell.v`), and a
discretized numerical scheme for that wave equation with its own
consistency proof, extracted and actually run as a Python/numpy simulator
with a matplotlib plot (`Discretize.v`, `runtime/wave1d.py`, `make
wave_sim` — see `docs/examples.md`'s Example 5 for the full walkthrough).
That simulator's grid/loop/boundary-condition plumbing is hand-written,
unproven external runtime, not a formalized numpy subset (see
`docs/roadmap.md`'s electromagnetism entry for exactly what that does and
doesn't cover) — `Calculus.v`/`Maxwell.v`'s symbolic `R`-valued field
theory and the discretized, extracted `PrimFloat` simulator are
connected by `Discretize.v`'s consistency theorem, not by one continuous
proof chain from `R` down to the generated Python.

Decisions made along the way (superseding the "Open questions" below
where they overlap):
- The pretty-printer is left unproved (structure-preserving, not
  semantics-affecting — see `docs/duality.md`'s trust-boundary section).
- Invocation is a standalone CLI reading JSON on stdin, not a Coq
  vernacular command — simplest to get working first; revisit if the
  remote-host integration wants something tighter.

## Open questions

- Exact initial supported Coq subset beyond the current one (next likely
  additions: mutual/recursive `let`/`fix`, records, richer inductive
  types — see `docs/roadmap.md`).
- Reconciling `Json.v`'s grammar against Coq's actual
  `Extraction Language JSON` output (currently `expr` values are
  constructed directly rather than ingested from real `.v` sources — see
  `docs/roadmap.md`).
- What exactly the "theory-evaluating agent" on the remote host needs from
  `coq2py` at the interface level (input format, invocation, how generated
  Python gets executed) — needed to scope the deployment packaging.
