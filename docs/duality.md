# Proofs and programs: the duality behind coq2py

## Propositions as types

Coq's logic is built on the Curry–Howard correspondence: a proposition is a
type, and a proof of that proposition is a term of that type. Checking a
proof is type-checking; constructing a proof is constructing a term. There
is no separate "proof language" sitting on top of a "programming language" —
Gallina, the term language of Coq, is both at once.

Concretely, a function type corresponds to implication:

$$
A \to B \quad\text{is both "a function from } A \text{ to } B\text{" and "}A\text{ implies }B\text{"}
$$

and a dependent product $\forall x : A, P(x)$ is simultaneously the type of
a function taking an $x : A$ and returning a $P(x)$, *and* the statement
"for all $x$, $P(x)$ holds" — a proof of it is a procedure that produces,
for every $x$, evidence of $P(x)$.

## Two sorts, two roles

Coq stratifies types into **sorts**. The one relevant here is the split
between `Prop` and everything else (`Set`/`Type`):

- A term of a type in `Prop` is a *proof*. Its only job is to exist — type
  checking confirms the proposition holds, and after that the proof's
  internal structure is never inspected by any program.
- A term of a type in `Set`/`Type` is *data* or *computation* — something
  that is actually run.

A single Gallina definition routinely contains both. A specification like

```
{ x : expr | expr_idents_valid is_valid_ident x = true }
```

pairs a `Set`-sorted payload (the `expr`) with a `Prop`-sorted certificate
(the proof that its identifiers are valid). Both live in the same term,
checked by the same kernel, but only one of them is meant to run.

## Extraction: erasure as a functor

**Extraction** is the operation that throws away the `Prop` half and keeps
the rest. Formally, it's a translation

$$
\mathcal{E} : \textbf{Gallina} \to \textbf{OCaml (or Python, here)}
$$

defined by structural recursion on well-typed terms, with the defining
property that on any `Prop`-sorted subterm $\mathcal{E}$ produces nothing —
proof obligations compile to nothing at all, not even a runtime check,
because type-checking has already confirmed they hold. What's left is pure
computational content: the same pattern matches, the same recursive calls,
the same data — just with every proof term removed.

This is the "duality" the project's name gestures at: a single certified
development is read two ways. Read through the `Prop` lens, it's a theorem
and its proof. Read through the `Set`/`Type` lens — which is what
extraction does — it's an algorithm. Coq's own `Extraction` command to
OCaml, Haskell, and Scheme is exactly $\mathcal{E}$ for those three target
languages; coq2py is $\mathcal{E}$ for a subset of Python.

## What extraction *doesn't* give you for free

Here is the point this project takes more seriously than is strictly
necessary for a hobby extractor: **extraction itself is an unverified
transformation**. Coq's own OCaml/Haskell/Scheme backends are trusted —
widely used, carefully engineered, but not machine-checked to preserve
semantics. Nothing stops a bug in the extraction code from silently
producing a program that doesn't behave like the Gallina term it came
from.

For most Coq developments that's an acceptable risk (the backend is
mature, the failure mode is rare, and and the alternative — don't extract,
just read the proof — gives you nothing to run). This project's premise,
stated in [GOAL.md](../GOAL.md), is to not accept that risk silently for
the Coq-to-Python direction: wherever a transformation step actually
changes a program's meaning (parsing text into an AST, translating one
AST into another), that step should itself be a Gallina function with a
theorem about it, not just "a function we're extracting and hoping is
right." Formatting the result back out as text is the one place this
project *does* accept the same unverified status Coq's own backends have
— that step can't change what a program computes, only how it's spelled.

## Stating "preserves meaning" precisely

To even ask whether a translation preserves meaning, both sides need a
formal semantics to be measured against. This project gives the source
subset (`Lang.v`) and the Python-subset target (`PyLang.v`) each a
big-step evaluator over their own (mirrored) notion of value —
`value` (`VZ`/`VBool`/`VPair`, recursively) on the source side,
`pyvalue` on the target side:

$$
\mathrm{eval} : \mathrm{env} \to \mathrm{expr} \to \mathrm{value}\ \mathrm{option},
\qquad
\mathrm{peval} : \mathrm{pyenv} \to \mathrm{pyexpr} \to \mathrm{pyvalue}\ \mathrm{option},
$$

with a structural correspondence `value\_to\_pyvalue` lifted pointwise to
environments (`env\_to\_pyenv`). `Translate.v` then proves, for
`translate : expr -> pyexpr`:

$$
\forall\, \rho,\, e.\quad \mathrm{peval}\,(\mathrm{env\_to\_pyenv}(\rho))\,(\mathrm{translate}\,(e)) \;=\; \mathrm{option\_map}\,(\mathrm{value\_to\_pyvalue})\,(\mathrm{eval}\,(\rho)\,(e))
$$

unconditionally — no side conditions, no restriction to closed or
well-typed terms. `peval` here is not "what Python really does"; it's a
formal specification this project writes down and then proves `translate`
respects. The honest, load-bearing assumption underneath all of it is that
`peval` correctly describes what the generated Python text actually does
when CPython runs it. That correspondence is accepted as an axiom here,
exactly the role real hardware/assembly semantics play in CompCert's own
trusted computing base — it is not something this project attempts to
discharge, and for a target as large and dynamically-typed as real
Python, it would be a substantial undertaking in its own right.

## The same move, one layer down: JSON ingestion

The same question — "does this transformation preserve meaning?" — applies
just as much to getting a `Coq` source term into the pipeline as it does to
the Coq→Python step itself. `Json.v` defines a restricted JSON-flavoured
text encoding of `expr`, and proves

$$
\forall\, e.\; \mathrm{valid\_idents}(e) \;\Rightarrow\;
\mathrm{parse\_expr}\big(\mathrm{print\_expr}(e)\big) = \mathrm{Some}\,(e,\, \texttt{""})
$$

i.e. the parser is a proven two-sided inverse of the printer, restricted to
exactly the subset this codebase supports — "acceptable if it only accepts
Coq's subset language," as [GOAL.md](../GOAL.md) puts it. There is no
separate, independently-stated "JSON grammar" floating around as prose
documentation that the code might silently drift from: `print_expr` *is*
the grammar, and the theorem says the parser recovers exactly what it
specifies.

## Where this leaves the trust boundary

Put together, here is what is actually proved versus assumed in this
repository, stated once so the rest of the documentation can point back
to it:

**Proved (machine-checked, axiom-free):**
- `Translate.translate_preserves_semantics` — the source-to-Python-subset-AST translation.
- `Json.parse_print_roundtrip` — the JSON parser, against its own printer's grammar.

**Assumed (same category of trust as any Coq development, or as
CompCert's own documented trust base):**
- Soundness of the Coq kernel itself.
- That the formal `peval` semantics in `PyLang.v` faithfully describes
  real CPython's behaviour on the generated source text.
- Correctness of Coq's own OCaml extraction, used once, in the ordinary
  (unverified) way, to turn the proven Gallina pipeline into a runnable
  binary.
- The `PyPrint.v` pretty-printer (text formatting only — see above).

This is a smaller, more precisely-drawn boundary than "trust the whole
tool," and it is exactly the boundary [GOAL.md](../GOAL.md) set out to
draw: proof where a transformation can silently change what a program
means, ordinary engineering trust everywhere else.
