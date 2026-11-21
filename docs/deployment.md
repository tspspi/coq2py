# Deploying `coq2py` to the remote host

This is the packaging/invocation protocol GOAL.md's "Target environments"
table describes but, until now, didn't spell out: exactly what ships to
the remote deployment host, how the theory-evaluating agent there invokes
`coq2py`, and how results come back. See `docs/roadmap.md`'s "Deployment
target" entry for how this was closed and what it doesn't cover.

## What ships

One file: the `coq2py` binary (`ocaml/driver/main.exe`, built on the dev
machine by `gmake package` below and staged as `dist/coq2py`). Nothing
else from this repository needs to go with it -- no `.v` sources, no
`coq2py_core.ml`, no build tooling.

Confirmed directly (`ldd` on the built binary), not assumed: it has no
runtime dependency on `coq-core`, OCaml's own runtime, or anything else
beyond the OS's own `libc`/`libm`/`libthr`. The `coq-core.kernel`
library `coq/Extract.v`'s own header explains the build needs (for the
`PrimFloat`/`Uint63` realizers) is a *link-time* cost only: `dune
build`'s native-code default compiles it statically into the
executable. The remote host does still need `coqc`/`coq-core`
installed -- per GOAL.md's target-environment table, that's a separate,
already-assumed requirement for the host's own job of type-checking the
agent's freshly-written proofs, not something this binary itself needs
at runtime.

To build and stage it:

```
gmake package
```

produces `dist/coq2py` (a stripped, `release`-profile binary) and
`dist/README.md` (a copy of this file). Copy `dist/coq2py` to the
remote host by whatever means that host's own deployment process
already uses (`scp`, a container image layer, a release artifact --
this project doesn't prescribe one); nothing more is required on the
target end than an executable bit and a matching OS/architecture (the
same assumption any statically-linked-enough native binary already
makes).

## How the agent invokes it

Two input shapes are accepted, matching the two JSON dialects this
project's pipeline speaks (`coq2py --real` is new; the first form
already existed from this project's start):

```
coq2py <function-name> <param1,param2,...> < input.json
coq2py --real <function-name> < module.json
```

The second form is the one a theory-evaluating agent actually uses in
deployment: it writes an ordinary `.v` file (a `Definition`/`Fixpoint`
in the subset `docs/roadmap.md` documents as recognized), appends

```coq
Extraction Language JSON.
Extraction "module.json" <the_definition_name>.
```

and runs `coqc` on it the normal way -- already a requirement of that
host regardless of `coq2py` (GOAL.md's target-environment table). That
produces `module.json`, Coq's own standard extraction output, which is
then piped straight into `coq2py --real <the_definition_name>` on
stdin:

```
coqc my_proof.v   # agent's own proof; emits module.json via the
                   # Extraction commands above
coq2py --real the_definition_name < module.json > generated.py
```

`coq2py --real` tries, in order, the four declaration shapes
`RealIR.v`/`RealJson.v` prove how to recognize inside a real module --
plain (possibly multi-argument) non-recursive, single-argument
self-recursive, multi-argument self-recursive, and an N-way
mutually-recursive group -- and uses whichever one matches
`<function-name>`; a real declaration is always exactly one of these,
never more than one, so first-match is unambiguous, not a heuristic.

## How results come back

On success: the generated Python function's source text on stdout
(exactly `py_function`'s own output, the same text every `examples/`
file's `Compute py_function ...` already shows), exit code 0. The
agent reads this from the subprocess's stdout the same way it would
capture any CLI tool's output -- no further protocol.

On failure -- the name wasn't found in the module, or its declaration
isn't in the recognized subset -- nothing is printed to stdout, a
one-line explanation goes to stderr, and the exit code is nonzero. This
is a deliberate design choice carried over from this project's trust
boundary (GOAL.md): a `coq2py` failure is always a loud, checkable
`None`/nonzero-exit, never a silently-wrong Python program. The parse
step for the *first* input form (plain `Json.v`-encoded `expr`) also
warns on stderr (without failing) if trailing bytes are left over after
parsing, carried over unchanged from before this entry.

## What this does and doesn't cover

This closes the packaging/invocation gap itself -- what ships, how it's
invoked, how results return -- not the separately-tracked question of
*which* Coq programs are recognized at all. That's `docs/roadmap.md`'s
own, much longer-running concern (narrow source/target subsets,
modules/typeclasses/coinductives, numpy-shaped arrays, and so on); this
document only promises that whatever *is* recognized reaches the agent
through a real, tested, binary-only round trip -- confirmed end to end
against four genuine `coqc`-extracted modules (one per recognized
declaration shape, including a fresh ~350KB real Coquelicot capture),
not just this project's own hand-built JSON fixtures.
