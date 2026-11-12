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

`expr`/`pyexpr` currently cover: integer, boolean, and float constants,
variables, integer and float `+`/`-`/`*` (plus float `/`), general
comparisons (`=`/`<`/`<=`, over both integers and floats, via
`EEq`/`ELt`/`ELe` and `EFEq`/`EFLt`/`EFLe` respectively) and boolean
connectives (`and`/`or`/`not`), a general `if` (on a genuine boolean
condition, not the earlier "equals zero" hack), pairs/tuples
(construction and projection), a single non-recursive `let`, and bounded
iteration (`ERepeat n x body init`, `n` a literal, compile-time `nat` —
see `examples/Kinematics.v`'s `euler_multi_step_expr` for a worked
instance chaining a whole trajectory this way, no external loop needed).
Values are now a real four-way sum (`VZ`/`VBool`/`VPair`/`VFloat`), not
bare integers — operations applied to a value of the wrong shape get
stuck (`None`), the same way an unbound variable already did; there is
no separate static type system layered on top. Not yet covered, in
roughly the order they'd likely be needed:

- Mutual and recursive `let`/`fix` (general structural recursion, where
  the number of steps depends on runtime data rather than being fixed
  up front the way `ERepeat`'s count is).
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
if/when a project depending on this actually needs it.

## `PrimFloat.float` is wired in, extracting to native `float`

`Lang.v`/`PyLang.v` now have a fourth value shape, `VFloat`/`PVFloat`,
backed by Coq's primitive, IEEE-754 `PrimFloat.float`, with `EFConst` and
`+`/`-`/`*`/`/` (`EFAdd`/`EFSub`/`EFMul`/`EFDiv`); `Translate.v`'s
preservation proof and `Json.v`'s JSON codec both cover it
unconditionally, the same as every other constructor (see
`examples/Kinematics.v`'s `euler_step_float_expr` for a worked instance
and `docs/examples.md`'s Example 3 for captured output). This was the
"`R` has no computational content" gap the Electromagnetism section used
to describe as an open design decision between `PrimFloat` and a
fixed-point `Z` encoding — resolved in favor of `PrimFloat`, since it
extracts to OCaml's native `float` via the stock `ExtrOCamlFloats`
realizer with no new *data-format* dependency (`Extract.v`'s comment
covers the one real cost: `Json.v`'s float codec goes through
`Prim2SF`/`SF2Prim`, which pull in enough further `PrimFloat`/`Uint63`
primitives that `ocaml/driver/`'s build now links `coq-core.kernel` —
already installed wherever `coqc` is, per GOAL.md's dependency table, so
this is "reachable as an OCaml library," not "a new install").

The JSON wire encoding is exact, not decimal: a float is serialized as
its `Prim2SF`/`SF2Prim` decomposition (sign, and either zero/infinity/nan
or an integer `(mantissa, exponent)` pair with value `(-1)^sign *
mantissa * 2^exponent`), round-tripped via `SF2Prim_Prim2SF` (a Coq
standard-library axiom — same trust category as the kernel itself, not
something this project introduces). `PyPrint.v`'s generated-Python
rendering of a literal float reuses the same decomposition, printed as
`mantissa * (2.0 ** exponent)`, for the same reason: exact, with no
decimal shortest-round-trip algorithm to get right (or get subtly wrong)
in an unverified pretty-printer.

What's still not covered: comparisons/conditionals over floats (tracked
above), and the "does `PrimFloat.float` arithmetic actually match
IEEE-754 the way the real CPython/numpy `float` does" question is the
same category of assumed-not-proved trust boundary as "does `peval`
describe real CPython" (see [duality.md](duality.md)) — not a new one
this addition introduces, since `PrimFloat` is itself specified to be
IEEE-754 binary64.

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

## Electromagnetism example: symmetry, Maxwell's equations, the wave equation

`examples/physics/` is a larger worked example built on reusable modules:

- `Minkowski.v` — the Minkowski metric and the Lorentz group as linear
  algebra, with a concrete boost matrix verified to preserve the metric.
- `Calculus.v` — a symbolic multivariable calculus layer (fields closed
  under differentiation with respect to each spacetime coordinate,
  commuting mixed partials proved rather than assumed) and the vector
  calculus identities (div/curl/grad/Laplacian, the double-curl identity)
  built on it.
- `Maxwell.v` — Maxwell's equations in vacuum as a hypothesis set, and
  the electromagnetic wave equation for E and B derived from them.

- `Discretize.v` — the discretized numerical scheme for the wave
  equation, a genuine (not assumed) consistency proof for it, the
  extractable `expr` term for its per-point update rule, and (via
  `make wave_sim` and `runtime/wave1d.py`) an actual running Python/numpy
  simulator built from the extracted code, with a matplotlib plot. See
  `docs/examples.md`'s wave-simulator walkthrough for a full worked
  account with captured output, and below for exactly what is and isn't
  covered.

`Calculus.v` and `Maxwell.v` use `R`, Coq's classical,
axiomatically-constructed real numbers, which — unlike `Z` — have no
computational content and cannot be extracted to a concrete numeric type
at all (`R`'s equality isn't decidable; this is inherent to how it's
built, not a missing extraction pragma); the discretized grid simulator
needs its own, separately computable numeric representation, which is
`Coq.Floats.PrimFloat` (`VFloat`/`EFConst`/`EFAdd`/`EFSub`/`EFMul`/`EFDiv`
— see the `PrimFloat.float` section above), not a fixed-point scheme over
`Z`.

`Discretize.v`'s `leapfrog_exact_for_cubic_profile` is a genuine
numerical-analysis theorem, not the "assumed, standard" hand-wave this
entry used to settle for: given that the continuous wave equation holds
at a point and the true solution agrees with its own third-order Taylor
expansion there (both in space and in time — exactly what "the solution
is smooth" buys locally), the discrete leapfrog update recovers the
*exact* next-time-step value, with literally zero error — not just
asymptotically small. It's proved by `field` over `R`, the same style as
`Calculus.v`'s `pderiv_comm`, not a limit/remainder argument (which would
need Taylor's-theorem machinery this project's dependency policy avoids
pulling in). The honest scope of what this does *not* claim: it says
nothing about points where the true solution's local Taylor expansion has
a nonzero 4th-order term (that's where real `O(dx^2+dt^2)` truncation
error actually comes from) — this theorem proves the error's *leading
term* is what remains after cubic-order matching, not that the leading
term is small.

What `Discretize.v` does *not* do is add arrays to `expr`/`pyexpr` itself
(still the gap tracked above) — `ERepeat` (bounded iteration, now
covered) doesn't close this one on its own, since the wave simulator's
state is a whole grid, not a small, fixed-shape value `ERepeat` could
carry around the way `examples/Kinematics.v`'s `euler_multi_step_expr`
does for a `(x, v)` pair. Instead, `leapfrog_update_expr` is the proven,
extracted *per-point* update rule (five scalar floats in, one out), and
`runtime/wave1d.py` is a hand-written, explicitly unproven external
runtime — in the same trust category as `ocaml/driver/main.ml`'s CLI glue
or `PyPrint.v`'s pretty-printer — that allocates the numpy grid, applies
Dirichlet boundary conditions, and drives the time-stepping loop, calling
the *literal* extracted `leapfrog_update` function (imported, not
re-transcribed) once per step, over whole-array numpy slices (its body is
plain `+`/`-`/`*`/`**`, so passing numpy arrays instead of scalars just
works via Python's operator overloading — no separate "vectorized"
rewrite was needed). This is a real, if narrower, way to reach "extracted
Python actually running a simulator" without first doing the
substantially larger numpy-semantics formalization described above; it
is not a substitute for that formalization, which remains future work if
arrays/loops ever need to live *inside* the proven subset (e.g. to prove
something about the loop itself, not just each step it runs).

## Deployment target: the remote host

Per GOAL.md, the remote deployment host is meant to run `coqc` (already
installed there) against proofs a theory-evaluating agent writes at
runtime, feeding the resulting JSON IR to an already-built
`coq2py` binary copied over from the dev machine — not to rebuild
`coq2py` itself. That deployment packaging (what exactly ships to that
host, how the agent invokes it, how results come back) isn't built yet;
right now this repository only demonstrates the pipeline running locally.
