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
JSON.

This was empirically checked (Coq 8.18.0, the dev-machine version per
GOAL.md's table) rather than left as an open guess, and the honest
answer is: it's a materially bigger gap than "adjust the grammar a bit."

- `Recursive Extraction add1.` for a one-line `Definition add1 (x : Z) :
  Z := x + 1.` emits **~1700 lines** of JSON — the real backend pulls in
  the full transitive closure of everything the function's type and body
  touch, here `Z`'s own `positive`-based binary representation and all of
  *its* recursive helper functions (`add`, `succ`, ...), each as a full
  `decl:ind`/`decl:fixgroup` declaration. `Extract Constant`/`Extract
  Inductive` realizer pragmas (the ones that successfully suppress this
  for the OCaml backend, e.g. `ExtrOcamlZInt`) do **not** suppress it for
  JSON — they only rename the emitted declarations, the expansion still
  happens.
- The practical entry point is instead the *non-recursive* `Extraction
  add1.` (no `Recursive`), which emits just one bounded `decl:term` for
  `add1` itself — 41 lines, referencing `Z`/`Zpos`/`XH`/`Z.add` (as
  `add0`) *by name* rather than inlining their definitions. That's a
  genuinely usable starting shape.
- But even that shape is further from `Json.v`'s grammar than hoped:
  - Functions are **curried lambdas** (`expr:lambda` with an arg-name
    list and a body) applied via a general `expr:apply` node — this
    project's `expr` has no function values or application *at all* yet
    (every "function" is the outermost `py_function` wrapper, not a
    first-class value), so supporting this is a prerequisite, not a
    grammar tweak.
  - Integer literals are **`positive`'s own binary constructor tree**
    (`1` prints as `Zpos XH`; bigger numbers nest `XI`/`XO` constructors
    bit by bit), not a flat decimal numeral the way `z_to_string` emits
    — needs its own conversion, structurally similar to (but distinct
    from) the `spec_float`/`Prim2SF` decomposition `Json.v`'s float codec
    already does.
  - Arithmetic appears as a **named function call** (`x + 1` is
    `expr:apply` of `expr:global "add0"`, not a primitive `+` node) --
    recognizing this as `EAdd` means pattern-matching on that specific
    global name, which is an extraction-internal detail, not a stable,
    documented one (confirming the schema-stability caveat below).

None of this is a reason to abandon the idea — the non-recursive,
single-declaration shape is a real, bounded starting point. The
"needs function application in `expr`/`pyexpr` first" prerequisite is
now done (`ELam`/`ERec`/`EApp`, see below) — what's still missing is a
translation layer from this richer, curried, named-global-reference
MiniML-style IR down to the subset `expr` actually covers (binary
`EAdd` vs. a named 2-argument `expr:apply`, binary-tree integer
literals vs. flat decimals, etc.), not a small adjustment to `Json.v`'s
current flat grammar. Re-doing the round-trip proof against whatever
grammar comes out the other end is still step 3, unchanged.

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
variables, integer and float `+`/`-`/`*` (plus float `/`, and integer
floor-`/`/`%` via `EDiv`/`EMod` — undefined, not merely assumed, on a
zero divisor; see `examples/Kinematics.v`'s `time_to_stop_expr`, where
that precondition turns out to need no separate runtime check at all,
since Python's own `//`/`%` already raise on one), general comparisons
(`=`/`<`/`<=`, over both integers and floats, via `EEq`/`ELt`/`ELe` and
`EFEq`/`EFLt`/`EFLe` respectively) and boolean connectives
(`and`/`or`/`not`), a general `if` (on a genuine boolean condition, not
the earlier "equals zero" hack), pairs/tuples (construction and
projection), a single non-recursive `let`, bounded iteration
(`ERepeat n x body init`, `n` a literal, compile-time `nat` — see
`euler_multi_step_expr` for a worked instance chaining a whole
trajectory this way, no external loop needed), and now real, first-class
functions and recursion: `ELam`/`EApp` (closures and application) and
`ERec` (a named self-referential closure, the only way to write
recursion here — see `examples/Kinematics.v`'s `fall_until_landed_expr`
for a worked instance whose step count genuinely depends on the data,
unlike `ERepeat`'s fixed count). Values are now a real five-way sum
(`VZ`/`VBool`/`VPair`/`VFloat`/`VClosure`), not bare integers —
operations applied to a value of the wrong shape get stuck (`None`), the
same way an unbound variable already did; there is no separate static
type system layered on top.

Adding functions forced one real architectural change, not just another
constructor: `eval`/`peval` now take an explicit `fuel : nat` (see
Lang.v's header). This isn't a style choice — once a closure can be
returned, stored, and reapplied, evaluating its body is no longer a
structural subterm of whatever `expr` `eval` was first called on, so
Coq's guardedness checker rejects the natural recursive definition
outright (confirmed directly: the obvious fuel-free interpreter fails
to compile with "cannot guess decreasing argument of fix", even for a
*non*-recursive closure). This is the same reason general-purpose
languages can't have a total type-checked interpreter written in a
total language at all — not a limitation specific to this project.
Running out of fuel is one more way to get stuck, alongside the
wrong-shape-value and unbound-variable cases that already existed;
`translate_preserves_semantics` holds for the *same* shared fuel on
both sides and needs no new axioms (`Print Assumptions` still reports
only the same `PrimFloat` primitives as before).

Lists are now in too: `ENil`/`ECons`/`EListMatch` (a `VList`, and the
first "recurse over a value's own structure" pattern this subset has —
see `examples/Kinematics.v`'s `total_distance_expr`, a Riemann sum over
a list of velocity samples of whatever length it happens to have).
Generated Python renders a list as nested tuples (`()` for `Nil`,
`(hd, tl)` for `Cons` — the same shape as pairs already use, not
Python's native mutable `list`; see `PyPrint.v`'s comment on
PListMatch`).

Records are now in too, but deliberately capped at exactly two named
fields: `ERecord k1 e1 k2 e2`/`EField name e` (a `VRecord`; nesting
handles more than two fields — `ERecord "a" e1 "rest" (ERecord "b" e2
"c" e3)` for three — the same way `EPair`/`VPair` are already capped
at two components). That cap isn't arbitrary: a general `list (string
* expr)`-shaped record needs a custom induction principle for `expr`
before `Json.v`'s structurally-inducting `parse_print_roundtrip`
theorem can state a useful hypothesis about a sub-expression buried
inside a list field, and a `Fixpoint eval ... with eval_fields ...
with lookup_field ...` attempt at it fails to compile outright
("cannot guess decreasing argument of fix") — confirmed directly
before settling on the fixed-arity design. Generated Python renders a
record as a `dict` literal keyed by the field names (`{"x": ...,
"v": ...}`), looked up by name (`state["x"]`) rather than by position —
see `examples/Kinematics.v`'s `euler_step_record_expr`, Example 1's
step again with named instead of positional output.

Mutual recursion is now in too, also capped — at exactly two
functions: `ERecMut f1 param1 body1 f2 param2 body2` (a `VClosureMut`),
`ERec`'s cousin for a pair of functions that may each call *either* of
themselves, not just `ERec`'s single self-call. The cap here reflects
a real representation limit, not just proof convenience: Coq values
can't be cyclic, so "two closures that capture each other" is only
representable by bundling *both* bodies into one value (tagged with a
`which : bool` saying which of the two it currently stands for) —
`EApp` reconstructs *both* siblings' bindings into the callee's
environment on every call, generalizing the single self-binding
`ERec`'s `EApp` case already reconstructs. `ERecMut` evaluates to
`VPair clo1 clo2`, so the usual `EFst`/`ESnd` picks out and calls
either one. See `examples/Kinematics.v`'s `bounce_expr`, Example 10: an
elastic bounce where `"fall"` (running Euler steps) hands off to
`"rise"` (reflecting the velocity) — a genuine cross-call between two
functions defined together, generated as two chained walrus
assignments in Python (the same self-reference trick `PRec` already
uses, extended to two names).

Not yet covered, in roughly the order they'd likely be needed:

- General N-field records / non-trivial inductive types beyond pairs,
  lists, and 2-field records.
- General mutually-recursive *groups* (more than two functions) —
  `ERecMut` only supports exactly two.
- Numpy-shaped arrays specifically (fixed-rank, fixed-dtype, with
  broadcasting and view-vs-copy aliasing rules) — a cons-list isn't
  that; it's the general-recursion building block arrays would need
  bounds/shape reasoning on top of, not a substitute for it.
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
