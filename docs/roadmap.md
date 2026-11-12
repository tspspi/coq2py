# Roadmap / known gaps

An honest accounting of where this project currently stands relative to
the vision in [GOAL.md](../GOAL.md), referenced from several source files
so the gaps are visible right next to the code they apply to rather than
only here.

## Not yet wired: real `coqc` JSON output

`Json.v`'s grammar is a restricted JSON-flavoured encoding this project
defines and proves a parser for — it is **not yet** reconciled against
what Coq's own `Extraction Language JSON` backend actually emits for a
real `.v` file. Today, `expr` values are constructed directly as Gallina
terms (see `examples/Kinematics.v`) or fed to the CLI by hand-writing the
JSON. Closing this gap means:

1. Picking a Coq subset to target first (this repo's `expr` is a
   reasonable first slice: arithmetic, variables, let-bindings,
   conditionals).
2. Reading `coqc`'s actual JSON backend output for small fixtures in that
   subset (empirically, against the exact Coq version in use — the schema
   isn't a stable, independently documented spec) and either adjusting
   `Json.v`'s grammar to match it, or writing a translation layer between
   the two.
3. Re-doing the round-trip proof against whatever grammar actually comes
   out the other end.

## Not proved: the pretty-printer

`PyPrint.v`'s `py_expr`/`py_function` are deliberately unproved, per
GOAL.md's distinction between "part of the translator" (needs proof) and
peripheral plumbing (doesn't). They're structure-preserving text
formatting, not a semantics-affecting transformation, so a bug there can
produce ugly or non-compiling Python but can't silently produce Python
that computes something different from what was proved — the walrus-
operator encoding of `PLet` is correct but not idiomatic, which is the
right kind of bug to be able to have at this layer.

## Narrow source and target subsets

`expr`/`pyexpr` currently cover: integer and boolean constants,
variables, `+`/`-`/`*`, general comparisons (`=`/`<`/`<=`) and boolean
connectives (`and`/`or`/`not`), a general `if` (on a genuine boolean
condition, not the earlier "equals zero" hack), pairs/tuples
(construction and projection), and a single non-recursive `let`. Values
are now a real three-way sum (`VZ`/`VBool`/`VPair`), not bare integers —
operations applied to a value of the wrong shape get stuck (`None`), the
same way an unbound variable already did; there is no separate static
type system layered on top. Not yet covered, in roughly the order they'd
likely be needed:

- Bounded iteration (a fixed, statically-known number of repetitions of a
  state-transforming expression) as a cheaper first step toward real
  recursion — see the next section.
- Mutual and recursive `let`/`fix` (general structural recursion).
- Records and non-trivial inductive types beyond pairs.
- Lists/arrays (needed before numpy-shaped state makes sense).
- Modules and typeclasses.
- Coinductives.

## `Z` extracts to native `int`, not arbitrary precision

`Extract.v` uses the stock `ExtrOcamlZInt` realizer, mapping Coq's `Z` to
OCaml's fixed-width native `int` — chosen deliberately to keep the
dependency footprint at zero (no bignum library), per GOAL.md's
dependency policy. The honest cost: this does not yet match Python's
arbitrary-precision integers for values outside native-int range. Revisit
if/when a project depending on this actually needs it (likely alongside
the real numbers vs. floats question below, when it does).

## The real target is physics, not integers

GOAL.md's actual motivation is expressing physics in Coq and extracting
proven-correct numpy/PyTorch-backed simulators. Getting there needs, at
minimum:

- A formalization of (a subset of) real-number arithmetic (`R` in Coq) and
  a stated, explicit, axiomatic correspondence to IEEE-754 floats — this
  is its own nontrivial trust boundary, structurally the same kind of gap
  as "does `peval` describe real CPython" (see
  [duality.md](duality.md)), and should be drawn just as explicitly rather
  than silently assumed.
- A target AST and formal semantics for a numpy-shaped subset: array
  values, shapes, broadcasting, and the view-vs-copy aliasing rules numpy
  actually has. This is a substantially bigger formalization effort than
  everything in this repository so far — comparable in scope to the core
  language work, not an incremental add-on — and is deliberately scoped
  as a separate, later phase rather than folded into the first subset.
- Only after those exist does a "PyTorch backend" become a sensible
  question (same array semantics, plus autodiff — a further, separate
  formalization question about what the generated code's gradients mean).

## Requested next example: symmetry → Maxwell's equations → wave equation

This was asked for directly, so it's worth being precise about scope
rather than quietly downgrading it. Taken literally — derive Maxwell's
equations from a symmetry group, get to the electromagnetic wave
equation, extract a numerical evaluation to Python, and plot it with
matplotlib (matplotlib/numpy as the only new *Python*-side dependencies,
consistent with the project's zero-new-Coq-dependency policy) — this is
several independent, substantial formalization efforts stacked on top of
each other, not a feature addition to `expr`:

1. **The physics derivation itself** (symmetry group → Maxwell's
   equations, e.g. via gauge invariance of a Lagrangian and the
   Euler–Lagrange equations, or via Lorentz-covariance of the
   electromagnetic field tensor) is genuine graduate-level theoretical
   physics, independent of Coq entirely. It would need to be pinned down
   mathematically before any formalization question even arises.
2. **Formalizing continuous mathematics in Coq**: real/vector/tensor
   calculus (gradient, divergence, curl, or the 4-tensor formalism),
   partial differential equations, and a chosen formalization of Lie
   groups/symmetry — none of which exist in this repository, and each of
   which is itself a significant formalization undertaking (there is no
   small shortcut here; this is comparable to or larger than existing
   standalone Coq analysis libraries).
3. **A numerical scheme for extraction**: the wave equation is a PDE;
   "evaluate it in Python" in practice means a discretization (e.g.
   finite-difference time-domain) over an array/grid, which needs the
   array/loop features already flagged as missing above (`expr` has no
   arrays, no loops, no mutable grid state) — plus a proof that the
   *discretization* itself is a faithful (consistent, stable) numerical
   method for the continuous equation, which is a numerical-analysis
   question layered on top of everything else.
4. Only the last mile — rendering a numpy array to a plot — is small, and
   is explicitly the "unverified utility function" category this project
   already has a place for (like `PyPrint.v`): a `matplotlib`-based
   plotting call sitting outside the trust boundary, consuming the
   (verified) simulator's output.

None of this is implemented, and shouldn't be faked with a hand-wavy
"proof" that doesn't actually establish what it claims to — that would
undermine the one thing this project has been careful about so far: that
"proved" here always means `coqc` checked it, not that it reads
plausibly.

**A tractable, honest first step in this direction**, if wanted: skip
the symmetry-group derivation and start directly from the 1D scalar wave
equation $\partial_t^2 u = c^2 \partial_x^2 u$ in its standard explicit
finite-difference form — a genuinely real instance of "a PDE simulator
extracted from Coq," just without claiming a from-first-principles
physics derivation that isn't built yet. Even that needs arrays/bounded
iteration first (the item at the top of the previous section), so it's
naturally the next rung on the ladder rather than a parallel track.

## Deployment target: the remote host

Per GOAL.md, the remote deployment host is meant to run `coqc` (already
installed there) against proofs a theory-evaluating agent writes at
runtime, feeding the resulting JSON IR to an already-built
`coq2py` binary copied over from the dev machine — not to rebuild
`coq2py` itself. That deployment packaging (what exactly ships to that
host, how the agent invokes it, how results come back) isn't built yet;
right now this repository only demonstrates the pipeline running locally.
