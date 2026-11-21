# Roadmap / known gaps

An honest accounting of where this project currently stands relative to
the vision in [GOAL.md](../GOAL.md), referenced from several source files
so the gaps are visible right next to the code they apply to rather than
only here.

## Active goal (long-running, spans many sessions)

**Domain note, stated here because it's load-bearing for anyone resuming
this file cold**: everything in this repository is Coq/Rocq proof
engineering, compiler-correctness work, and classical mathematical
physics (linear algebra, vector calculus, PDEs, numerical analysis). There
is no biological, chemical, radiological, nuclear, or weapons content
anywhere in this codebase. Project vocabulary that can misparse out of
context: "axiom" is a Coq keyword for an assumed proposition/function, not
anything else; "wave equation"/`Discretize.v` are classical
electromagnetism/numerical-PDE terms (not epidemiology); "landed" is this
project's own slang for "a feature or proof is merged and compiling";
`exp`/`ln`/`pow` are the math functions (the `PrimFloat` section above
explains why they needed a new axiom category: no native transcendental
primitive).

Three phases, tackled in order, each landed as its own sequence of small,
fully-proving commits with this file updated alongside (the project's
existing convention):

1. **Numpy-shaped array semantics**: formalize fixed-rank/fixed-dtype
   arrays, broadcasting, and view-vs-copy aliasing as a real `expr`/
   `pyexpr` construct — not the hand-written, unproven numpy runtime glue
   `runtime/wave1d.py` uses today. This is the single largest deferred
   item in this file (see "The real target is physics, not integers" and
   the electromagnetism entry below) — comparable in scope to the core
   language work, expect it to need its own sub-phases (start 1-D/fixed-
   shape, validate the induction/fuel approach in an isolated prototype
   the way `ERecordN` was first proven in a throwaway file before
   touching `Lang.v`/`Translate.v`/`Json.v` for real).

   **Sub-step done** (isolated prototype, not committed to `coq/` — a
   throwaway file, same convention as `ERecordN`'s own first validation):
   a minimal standalone source/target pair (`EArrConst (es : list expr)`/
   `EArrGet (arr idx : expr)`/`EArrSet (arr idx val : expr)`, a
   `VArray (vs : list value)` backed by McCarthy-style functional
   get/set — deliberately *not* real aliasing/mutation, which stays
   explicitly out of scope per the paragraph above) confirms the
   strong-induction-on-`expr_size`/`well_founded_induction lt_wf`
   technique `ERecordN`/`RRecordN` already established scales cleanly to
   an indexed (not just structural Nil/Cons) list-backed construct, and
   that `translate`'s preservation proof for it needs **zero new
   axioms** (confirmed: `Print Assumptions` reports "Closed under the
   global context") — unsurprising since `EArrGet`/`EArrSet` are pure
   list manipulation (`nth_error`/`firstn`/`skipn`), not a new numeric
   primitive. One proof wrinkle worth recording: `simpl`/`cbn` one-step-
   unfolds `skipn (S n) l` into a bare `match l with ... end` (the exact
   "simpl over-unfolds a recursive call" gotcha
   `coq_rewrite_anonymous_fix_mismatch` already documents for a
   different function) — fixed with a one-line refold lemma
   (`match l with [] => [] | _::l' => skipn n l' end = skipn (S n) l`,
   by `destruct l; reflexivity`) rather than fighting `simpl`'s
   unfolding depth a second way.

   **What this does *not* yet de-risk, confirmed by inspection before
   starting the real multi-file landing** (so the next session doesn't
   rediscover this the hard way): every past `expr`/`pyexpr`-growing
   feature "touched every layer" for a structural reason, not a
   stylistic one — `expr` is matched exhaustively in `Lang.v` (`eval`,
   `expr_idents_valid`), `Translate.v` (`translate`), and `Json.v`
   (`print_expr`, plus `parse_expr`'s own grammar and the
   `parse_print_roundtrip` theorem that is historically the single
   hardest proof per past feature, per this file's own history); growing
   `pyexpr`/`pyvalue` additionally ripples into `PyPrint.v` (`py_expr`),
   and — the real cost center for *this* feature specifically —
   `PyRename.v`, which is not small (`rename_pyexpr`, `pyexpr_size`,
   `pyexpr_recgroup_ok`, and a multi-thousand-line
   `rename_pyexpr_correct` theorem with its own `value_corr`/
   `pyval_opt_corr` family). `ENone`/`ESome`'s own landing is the
   closest precedent: growing `value`/`pyvalue` by two constructors
   there needed fixing "~90 existing value-destructuring proof
   patterns across `Translate.v`/`RealIR.v`" (see this file's `option`
   entry below) — a new array value shape should expect a comparable
   ripple through `PyRename.v`'s own value-shaped hypotheses, on top of
   its own new rendering/renaming/size cases. None of this blocks
   starting; it sizes the next real commit honestly so it isn't
   attempted as a quick addition and abandoned half-done partway
   through a file that must stay fully proving.
2. **RealIR.v ingestion-side gaps**: extend the real-`coqc`-JSON
   recognizer to modules/typeclasses, then coinductives — the same
   incremental, confirm-directly-against-a-fresh-probe methodology every
   prior `RealIR.v` feature (`RCase`, `RRecordN`, `RCallN`, the Coquelicot
   fragment) already used.
3. **The general compositional `R`-vs-float correspondence theorem**:
   Flocq-scale relative-error propagation through nested arithmetic.
   Attempt only once phases 1-2 are stable; this file currently scopes it
   as deliberately deferred, not a bounded next step, so expect it to need
   its own sub-plan rather than a single addition.

Standing methodology for all three (unchanged from every prior session):
confirm every claim directly via a fresh `coqc`/`vm_compute` probe, never
by analogy alone; before implementing a new feature, check whether an
already-landed feature has the same proof shape and mirror its exact
proof text rather than re-deriving the technique (see this file's own
history, and `coq_rewrite_anonymous_fix_mismatch`/
`coq2py_mirror_template_strategy` in the assistant's session memory for
the debugging/mirroring techniques this has already needed); keep `Print
Assumptions` honest about any new axiom, and state its scope explicitly
when one is unavoidable.

## In progress: ingesting real `coqc` JSON output

`Json.v`'s grammar is a restricted JSON-flavoured encoding this project
defines and proves a parser for -- it is **not yet fully** reconciled
against what Coq's own `Extraction Language JSON` backend actually emits
for a real, human-written `.v` file, though a first, proven step now
exists (`coq/RealIR.v`). Everything below was checked empirically (Coq
8.18.0, the dev-machine version per GOAL.md's table) rather than left as
an open guess.

- With this project's own OCaml-native realizers loaded (`ExtrOcamlZInt`
  etc, needed so `Z`/`float` extract to OCaml's native types rather than
  Peano-style trees), the JSON output leaks raw OCaml source snippets as
  constructor names (a constructor literally named `"(fun p->1+2*p)"`)
  and pulls in unrelated transitive standard-library declarations
  (`Stdlib.Int.succ`, ...) -- confirmed directly. `Extract Constant`/
  `Extract Inductive` realizer pragmas do **not** give a clean,
  target-independent JSON IR; they just make the *OCaml-flavoured* mess
  visible inside it.
- Without those realizers, a genuinely human-written definition --
  ```coq
  Definition clamp_nonneg (a b : Z) : Z := if Z.ltb a 0 then b else a.
  ```
  -- extracts to clean, generic MiniML-shaped JSON: a `decl:term` whose
  `value` is an `expr:lambda` with `argnames: ["a"; "b"]` (a direct,
  *multi-argument* list, not curried) and an `expr:case` body dispatching
  on an `expr:apply` of `expr:global "ltb"` (the `Z.` module prefix is
  dropped in the emitted name) to an `expr:rel "a"` and an
  `expr:constructor "Z0"` (the literal `0`), with two `pat:constructor`
  cases on `True`/`False`. This is the real target. The catch: every
  individual arithmetic/comparison *operation* still extracts its own
  full recursive definition over `Z`/`positive`'s binary encoding (two
  one-line `Z`-valued definitions together ran to 67KB) unless the
  consuming code specifically recognizes well-known operation names
  (`"add"`, `"ltb"`, `"andb"`, ...) as intrinsics and simply ignores their
  extracted bodies -- exactly the same move a real compiler makes for
  built-ins. These names are **not even stable across a single
  extraction unit**, confirmed directly: `Z.ltb` extracted cleanly as
  `"ltb"` in one test, but in a second test requiring nothing but
  `ZArith`, `Z.add` (via plain `+`) extracted as `"add0"`, not `"add"`
  -- `positive`'s own internal `add` helper claims the bare name first
  (dependency order, not anything about `Z.add` itself), bumping `Z.add`
  to a disambiguated suffix. A name-based intrinsic recognizer that
  hardcodes `"add"` would silently fail to recognize `Z.add` the moment
  anything else in the same extracted module also defines (or itself
  transitively needs) an `add`.

  **Done**: `RealJson.v`'s `resolve_intrinsic_name` fixes this, not by
  controlling the extraction unit or interpreting the colliding
  declaration's full body, but by using the one thing that reliably
  distinguishes the two colliding declarations: their *type*.
  `Pos.add : positive -> positive -> positive` and `Z.add : Z -> Z ->
  Z` are never the same type, confirmed directly (the module's own
  declaration table carries both, side by side, with exactly these
  ground types) -- so `resolve_intrinsic_name` strips a call's name of
  any trailing digit suffix, and accepts the stripped candidate as a
  known intrinsic only if *this module's own* declaration for the
  exact (unstripped) name has that intrinsic's expected ground type
  (`module_decl_types` builds the name/type table once per module from
  every `decl:term`/`fixgroup:item`'s own `"type"` field, already
  present in the captured JSON and previously never read at all). The
  canonical, unsuffixed name is substituted in *before* `RApp1`/`RApp2`
  is built, so `RealIR.v`'s own `real_eval`/`real_to_expr` -- which only
  ever compare against the bare, canonical names -- needed zero
  changes to benefit. Covers the confirmed-collision-prone base names
  (`add`/`sub`/`mul`/`ltb`/`leb`/`eqb`/`andb`/`orb`/`negb`, and the
  Coquelicot float fragment's `ropp`/`rabs`/`sqrt`/`rplus`/`rmult`/
  `rminus`/`rdiv`) -- deliberately not `fst`/`snd` (polymorphic over
  the pair's own element types, no single ground type to check against,
  and never observed to collide). `examples/NaturalCoq.v`'s `sum_list`
  is the worked instance: a real module where `Z.add` genuinely
  extracts as `"add0"` (confirmed directly, `positive`'s own `add`
  claims the bare name in *this* module's declaration order), parsed
  through `real_fix_decl_multi_of_module_json`, correctly resolving to
  the canonical `RApp2 "add" ...` RealIR.v's unmodified dispatch
  already recognizes -- `sum_list 0 [1;2;3] = 6`, checked against the
  real Gallina definition and confirmed running correctly under actual
  Python. `Print Assumptions` shows no new axioms (this is a parse-time
  text transformation, not a new semantic primitive). Full test suite
  passes with zero other edits, confirming the fallback (no module-
  level collision found) is exactly today's behavior.
- `coq/RealIR.v` is that recognizer, as a first proven step: `real_expr`
  models exactly this fragment (variables, `Z`/`bool` literals, named
  unary/binary intrinsic calls, a 2-case boolean `if`), `real_eval`'s
  reference semantics calls Coq's own `Z.add`/`Z.ltb`/etc *directly*
  (not a reimplementation -- the trust boundary here is exactly "Coq's
  standard library means what it says", the same category as the kernel
  itself), and `real_to_expr : real_expr -> option expr` translates into
  this project's existing, already-proven `expr` subset, with
  `real_to_expr_preserves_semantics` proving the translation matches
  `real_eval` exactly (no new axioms -- confirmed via `Print
  Assumptions`). The recognized fragment now also covers lists (`RNil`/
  `RCons`/`RListMatch`, into `ENil`/`ECons`/`EListMatch`) -- `list`'s own
  constructor names (`Nil`/`Cons`) are stable across extraction the way
  `Z.add` is not (constructors aren't subject to the same
  dependency-order disambiguation named helper functions are), confirmed
  directly against a real extracted list pattern match.
  Pairs are in too (`RPair`, into `EPair`, with `RApp1` growing two more
  recognized names, `"fst"`/`"snd"`) -- confirmed directly against a real
  extracted pair construction/projection: pair construction is an
  `expr:constructor "Pair"` with 2 args (`RPair`'s own shape exactly),
  and `fst`/`snd` are plain unary calls, the same shape `negb` already
  had, so no new `real_expr` constructor was needed for them.
  2-field `Record`s are in too (`RProj1`/`RProj2`, into `EFst`/`ESnd`) --
  confirmed directly against a real extracted `Record point := mkpoint {
  px : Z; py : Z }.`: construction extracts identically to `pair`
  (another 2-arg `expr:constructor`, whatever it's named -- `RPair`
  already covers it unchanged), but field *access* (`py p`) does *not*
  extract as a named call the way `fst`/`snd` do; it is a 1-case
  `expr:case` match on that same constructor, binding one field to a
  real name and the other to `"_"`. Since a Coq `Record` really is just
  sugar for a single-constructor inductive -- isomorphic to a plain
  product at the value level, with field *names* living only in the
  generated projection functions, never in the runtime representation
  -- `RProj1`/`RProj2` model that 1-case match shape directly and
  translate into the same `EFst`/`ESnd` tuples already use, rather than
  inventing a second, keyed representation for what is, underneath, the
  value shape `RPair` already covers.
  `examples/NaturalCoq.v` closes the loop concretely for four real,
  captured examples -- `clamp_nonneg` (`Z`/`bool`/`if`), `head_or_zero`
  (a real list pattern match), `swap_pair` (real pair construction/
  projection), and `flip_point` (a real two-field `Record`, recognized
  as a plain pair): each one's real captured JSON output is reproduced
  verbatim in a comment, hand-encoded as a `real_expr` term, proved to
  match the real definition for every input, translated, and run all
  the way through this project's existing `Translate.v`/`Json.v`/
  `PyPrint.v` pipeline to real, executing Python.
- A second confirmed naming surprise, this time about `andb`/`orb`
  specifically rather than name *disambiguation*: they don't reliably
  extract as a named call *at all*. `andb`'s own definition is already
  exactly a 2-case boolean match (`match a with true => b | false =>
  false end`), small enough that extraction inlines it on the spot --
  `andb (Z.leb x 0) (Z.ltb v 0)` (the natural, `&&`-based way to write
  this project's own `landed_expr` check, confirmed directly) shows up
  as an `expr:case` on `leb x 0` directly, never as an `expr:apply` of
  `expr:global "andb"`. `RealIR.v`'s `RApp2` still recognizes a bare
  named `"andb"`/`"orb"` call for whatever *does* reach one that way
  (a `bool` value already sitting in a variable, say), but the
  recognized encoding of surface-level `&&`/`||` is `RIfBool c1 c2
  (RBoolLit false)`/`RIfBool c1 (RBoolLit true) c2` -- `andb`/`orb`'s
  own definitions, encoded directly -- not an `RApp2 "andb"`/`"orb"`
  call. `examples/NaturalCoq.v`'s fifth example, `landed_natural`, is
  exactly this: the natural, `&&`-based sibling of Kinematics.v's own
  `landed_expr`, its real captured extraction JSON reproduced
  verbatim, encoded as `RIfBool`, and run all the way to real Python.
- The `expr:lambda`/`argnames` wrapper around a whole `Definition` --
  not just its body -- is recognized now too, via `RealIR.v`'s
  `real_decl`: a thin wrapper carrying `argnames` alongside the
  already-recognized body, since Coq's own extraction presents a
  multi-arg function as *one* `expr:lambda` node with a direct list,
  not curried (confirmed directly, see `RealIR.v`'s header) -- so no
  new `real_expr` translation case was needed, only a record pairing
  the names with the body and a preservation theorem that is a direct
  corollary of `real_to_expr_preserves_semantics`.
  `examples/NaturalCoq.v`'s `clamp_nonneg_decl` reuses the first
  example's real captured JSON (including its real `argnames: ["a",
  "b"]`) to show the whole declaration recognized, with
  `py_function`'s parameter list now read off `rd_argnames` instead
  of retyped by hand at the call site.
- A real, self-recursive `Fixpoint` of one argument is recognized now
  too (`ERec`'s ingestion-side cousin), via `RealIR.v`'s `RSelf`/
  `real_fix_decl`: a self-call extracts as an ordinary named call to
  the fixgroup's *own* declared name (confirmed directly), so `RSelf`
  only needs to know that name at translation time, not a new
  evaluation rule -- `real_eval`/`real_to_expr` both still give it
  `None` unconditionally, and `real_to_expr_ctx` (a case-for-case
  near-duplicate, not a generalization) is what actually threads the
  enclosing name through. Checked the same concrete-instance way
  *every* `ERec` example in this project already is (Kinematics.v's
  `fall_until_landed_expr`), not a new universally-quantified theorem
  -- a recursive term's step count depends on its argument, not its
  static size, the same reason that theorem doesn't exist for
  non-recursive `ERec` either. `examples/NaturalCoq.v`'s `any_true`
  (its real captured JSON, encoded by hand, translated, and run as
  real Python) is the worked instance.
- General *mutually*-recursive fixgroups (`Fixpoint ... with ...`, two
  or more members) are recognized too, via `RealIR.v`'s `RCall`/
  `real_fix_group_decl`: a real `decl:fixgroup`'s `fixlist` simply has
  more than one `fixgroup:item` (confirmed directly against a real
  `alt_from_true`/`alt_from_false` pair), and a call to *any* member --
  self included -- is the exact same `expr:apply`/`expr:global <name>`
  shape a self-call or an unrelated intrinsic call already has,
  distinguishable only by knowing the *whole group's* declared names,
  not just one. `RSelf` itself is deliberately untouched (still the
  single-function, one-name case it always was, so every existing
  proof about it keeps working unchanged) -- `RCall` is a new,
  additive sibling, recording *which* member was called since it is no
  longer always "this same function". `real_to_expr_ctx` (and
  `RealJson.v`'s `real_expr_of_json`/`real_app_of_json`) gained one
  new threaded parameter, `siblings : list var`, defaulting to `[]`
  at every existing call site -- a membership check against `[]` is
  always `false`, so the single-function path is byte-for-byte
  unchanged, confirmed by the full test suite passing with zero other
  edits. `real_fix_group_decl_to_expr` lands on `Lang.v`'s already-
  proven `ERecGroup` (no new target constructor, no new evaluation
  rule to prove). Like `real_fix_decl`, deliberately no generic
  preservation theorem (recursion depth is argument-dependent, the
  same reason that theorem doesn't exist for the single-function case
  either) -- `examples/NaturalCoq.v`'s `alt_from_true`/`alt_from_false`
  (a genuine 2-way cross-call: each member's body calls the *other*,
  not itself) is the worked instance, checked three ways: against the
  real Gallina definition (concrete-instance `eval`, both directions
  of the cross-call), round-tripped through `Json.v`'s printer/parser,
  and parsed from the real captured JSON *text* (not just hand-built,
  the same way `quad`/`combo`/`absdiff` are in `CoquelicotDemo.v`) via
  a new `RealJson.v` entry point, `real_fix_group_decl_of_module_json`
  -- found starting from either member's own name, confirming
  `find_fixgroup_by_member_name` doesn't just happen to work for
  whichever name is listed first in a real `decl:fixgroup`'s own
  `["name"]: null` field. `Print Assumptions` on both
  `real_to_expr_preserves_semantics` and
  `real_decl_to_expr_preserves_semantics` shows no new axioms.
- **Done** (recursive functions of more than one argument, the cap
  `real_fix_decl` always had): confirmed directly against a fresh
  probe (`sum_upto (acc n : Z) (fuel : nat) : Z := match fuel with O
  => acc | S fuel' => sum_upto (acc + n) (n - 1) fuel' end`) that a
  real multi-argument recursive self-call extracts as *one*
  `expr:apply` node with a flat, direct `args` list (3 elements) --
  not curried -- the exact same "multi-arg is a direct list, not
  curried" shape `RealJson.v`'s header already confirmed for ordinary
  (non-recursive) `expr:lambda` declarations, now confirmed for the
  *call* side of a recursive one too. That meant the cap could be
  lifted with *zero* new `Lang.v`/`PyLang.v`/`Translate.v`/`Json.v`/
  `PyPrint.v`/`PyRename.v` constructors: a multi-argument `Fixpoint f
  (a1 ... an : T) : T' := body` curries into already-proven pieces --
  `ERec f a1 (ELam a2 (... (ELam an body') ...))` for the declaration,
  `EApp (EApp (... (EApp (EVar f) arg1') arg2' ...) argn')` for every
  recursive call -- the same way a multi-argument *non-recursive*
  `Definition` could always be curried through nested `ELam`/`EApp`,
  just never needed to be since `real_decl`'s direct `argnames`
  already handles that case without currying. The only new code is at
  the `RealIR.v`/`RealJson.v` *recognition* layer: `RSelfN`/`RCallN`
  (`RealIR.v`), additive new siblings carrying a whole argument list,
  alongside the fully untouched `RSelf`/`RCall` (same "don't touch
  what already works" move `RCall` itself made relative to `RSelf`);
  `real_fix_decl_multi` (`rfdm_params : list var`, curried by
  `real_fix_decl_multi_to_expr`), alongside the fully untouched
  `real_fix_decl`; and `RealJson.v`'s matching parse-side
  `decl_fixgroup_item_multi_of_json`/`real_fix_decl_multi_of_module_json`.
  `examples/NaturalCoq.v`'s `all_match` (two arguments: `target` and
  `l`) is the worked instance: checked against the real Gallina
  definition (both a matching and a non-matching list), round-tripped,
  parsed from the real captured JSON text, and printed to real,
  checked Python (curried: `all_match(v0, v1)` calling a function of
  one argument returning a function of the next, confirmed to run
  correctly under actual Python too). `Print Assumptions` on
  `real_to_expr_preserves_semantics` shows no new axioms -- this
  addition needed no new primitive, only composition of already-
  proven pieces.
- A real 2-case sum (`Datatypes.sum`, Coq's own `inl`/`inr`) is
  recognized too, via `RealIR.v`'s `RCase`: a 2-case `expr:case` with
  each `pat:constructor` carrying exactly one payload argument
  (confirmed directly) -- the same shape `RListMatch`'s own `Nil`/
  `Cons` match already has, and lines up directly with `Lang.v`'s own
  `EInl`/`EInr`/`ECase` (both payload-carrying), unlike `Record` field
  access, which needed `RProj1`/`RProj2`'s own encoding trick.
  `option`'s `None`/`Some` is *not* covered the same way: `None`
  carries no payload, so it doesn't fit this shape without a second,
  separate encoding. `examples/NaturalCoq.v`'s `classify` (over
  `Z + Z`) is the worked instance, run all the way to real Python.
- A real *3*-field `Record` is recognized too, via `RealIR.v`'s
  `RRecord3`/`RProj3_1`/`RProj3_2`/`RProj3_3`: construction is still a
  single `expr:constructor`, now with 3 args instead of 2, and each
  field access is still a 1-case `expr:case` with `argnames` binding
  the one accessed field to a real name and the *other two* to `"_"`
  (confirmed directly). Field names live only in the extracted
  projection functions, never in the runtime representation (true
  already for the 2-field case), so there is no name to key an
  `ERecordN` by here -- these model a 3-field `Record` the same way
  the 2-field case already does, as the nested pair
  `EPair e1 (EPair e2 e3)` a human would write by hand to work around
  `ERecord`'s own 2-field cap, not the genuinely-N-ary `ERecordN`.
  The first case in this file whose translation nests two `EPair`
  dispatches deep (`EFst (ESnd _)`/`ESnd (ESnd _)`, for the 2nd/3rd
  field), needing one extra fuel unit and a second `destruct fuel`
  step in the proof, unlike every single-level case before it.
  `examples/NaturalCoq.v`'s `swap_xz` (Example 4's two-field `point`
  grown a field) is the worked instance, run all the way to real
  Python.

**Done** (landed in `coq/RealJson.v`): parsing the actual JSON *text*
`Extraction Language JSON` emits -- not just building `real_expr` terms
directly as Gallina values the way `examples/Kinematics.v` builds
`expr` terms by hand. `RealJson.v` is a generic `jvalue` parser (reusing
`Json.v`'s string/number lexing; tolerant of the whitespace real `coqc`
output has that `Json.v`'s own bespoke grammar deliberately lacks) plus
an interpreter into `real_expr`/`real_decl`/`real_fix_decl`, confirmed
end to end against five fresh `coqc` probes (`clamp_nonneg`, `classify`,
`swap_xz`, `any_true`, `alt_from_true`/`alt_from_false`) -- each mechanically parsed from real extraction
JSON produces, through the rest of the already-proven pipeline,
byte-identical Python to the hand-built version already in
`examples/NaturalCoq.v`. This also landed the nested `Z0`/`Zpos`/
`Zneg`/`XH`/`XO`/`XI` numeral reconstruction (folding real `expr:constructor`
numeral encodings back into `RZLit`'s plain `Z`), so that item below is
done too, not just the parser shell around it.

**Done** (`jvalue_parse_print_roundtrip`): `RealJson.v` now has its own
proper print/parse round-trip theorem for the *generic* `jvalue` layer,
mirroring `Json.v`'s own `parse_print_roundtrip` -- `print_jvalue`
(added purely for this proof; nothing upstream ever prints a `jvalue`
in practice) followed by `parse_jvalue` always recovers the original
value, for any fuel at least `jvalue_fuel v` and any trailing `rest`
not mistakable for more digits of a trailing `JNum` (`safe_rest`, the
same proviso `Json.v`'s own `parse_number_print` already needs, for the
same reason -- a text-based number grammar is inherently ambiguous
against an adjacent digit without some terminator). Proved by strong
induction on `jvalue_fuel`, the same `well_founded_induction lt_wf`
pattern `Json.v`'s own theorem uses, with the array/object list-level
cases built from two dedicated lemmas each (`print_parse_jarray_singleton`/
`print_parse_jarray_roundtrip`, `print_parse_jobject_singleton`/
`print_parse_jobject_roundtrip`) via the same "named Fixpoint mirroring
an anonymous one, bridged by a `reflexivity`-proved equality lemma"
technique already established for `PyLang.v`'s anonymous `fix`es, plus
a `jvalue_list_fuel`/`jvalue_fields_fuel` pair of dedicated fuel
measures (`Json.v`'s own `fields_fuel`/`fns_fuel` pattern) rather than
inlining a `length + fold_right` formula that `lia` couldn't see
through cleanly inside the induction. `Print Assumptions` confirms
**zero axioms** -- a fully constructive proof, not resting on anything
beyond what `Json.v` itself already proved (`parse_qtext_print`,
`parse_number_print`, `string_append_assoc`, ...). One genuine, prior
off-by-one surfaced and got fixed along the way: `jvalue_fuel`'s
`JArray`/`JObject` cases needed *two* extra fuel units over their naive
`S (length + fold_right max ...)` form, not one -- one for
`parse_jvalue`'s own `"{"`/`"["` dispatch step, one more for
`parse_jarray_elems`/`parse_jobject_fields`'s own first loop
iteration (even an empty list still needs one fuel unit to check for
the closing bracket) -- caught by the proof itself refusing to close
at the tight boundary, not spotted by inspection first.

Deliberately scoped to *only* this generic `jvalue` layer -- not the
`real_expr_of_json`/`real_decl_of_json` interpretation layer built on
top of it, which remains checked empirically (the instances above),
not by proof, same as before. This split is principled, not an
oversight: the generic layer's grammar is closed and stable (objects/
arrays/strings/numbers/bools/null, unaffected by future `real_expr`
feature additions), while the interpretation layer's own target is
"whatever shapes `coqc`'s extraction can ever produce" -- an
open-ended, moving target this project has already declined to chase
elsewhere for a related reason (see the extraction-name-instability
discussion earlier in this section, `resolve_intrinsic_name`). It's
the exact same boundary `Json.v` itself draws between its own proven
`expr`/`parse_expr` round-trip and the hand-verified-not-mechanically-
proven claim that real `coqc`-extracted terms actually print through
`PyPrint.v` the way the worked examples show.

What `RealIR.v`/`RealJson.v` deliberately does *not* yet do, in
roughly the order they'd be needed next:

- ~~Broaden the recognized intrinsic set further: genuinely *N-ary*
  `Record`s/mutual-recursion groups specifically~~ -- **done**, see
  this section's own entry below (`RRecordN`/`RProjN`, plus a real
  3-member `decl:fixgroup` confirming the mutual-recursion side of
  this was never actually capped).
- ~~Make intrinsic recognition robust to the `"add"`/`"add0"`-style name
  disambiguation~~ -- **done**, see this section's own entry above
  (`resolve_intrinsic_name`, type-based, not by controlling the
  extraction unit).

**Done** (`option`): confirmed directly against a real extracted
`Definition default_zero (x : option Z) : Z := match x with None => 0
| Some v => v end.` and `Definition wrap_positive (x : Z) : option Z
:= if Z.ltb x 0 then None else Some x.`: `None`/`Some v` extract as
0-/1-argument `expr:constructor`s (the same shape `True`/`False` or
`Nil`/`Cons` already have), and a match on them is a 2-case
`expr:case` -- confirmed to appear in *either* order (`Some` first in
`default_zero`'s own captured JSON, matching `option`'s own
declaration order in Coq's stdlib -- `Some` before `None` -- even
though the source `match` was written the other way around), so
`real_case_of_json` checks both. `option`'s `None` carrying *no*
payload is why it was never covered by `EInl`/`EInr`/`RCase` (both
sides there always carry one) -- `Lang.v` gained a real, dedicated
`ENone`/`ESome`/`EOptionMatch` (not `EInl`/`EInr` with a dummy payload
for `None`, the same "dedicated constructor over an encoding trick"
move `EFOpp` made), threaded through every layer: `PyLang.v`
(`PNone`/`PSome`/`POptionMatch`), `Translate.v` (including fixing the
~90 existing value-destructuring proof patterns across `Translate.v`/
`RealIR.v` that needed `VNone`/`VSome` accounted for once `value`
grew two constructors), `Json.v` (`"none"`/`"some"`/`"optionmatch"`
tags, parser, round-trip proof), `PyPrint.v` (rendered the same
tagged-tuple way `PInl`/`PInr` already are: `("none",)`/`("some",
v)`), `PyRename.v` (`rename_pyexpr_correct`'s case, plus two new
`value_corr` constructors), `RealIR.v` (`RNone`/`RSome`/
`ROptionMatch`, `real_eval`/`real_to_expr`/`real_to_expr_ctx`, and
`real_to_expr_preserves_semantics`'s proof). `Print Assumptions` shows
no new axioms. `examples/NaturalCoq.v`'s `default_zero`/
`wrap_positive` are the worked instances: checked against the real
Gallina definitions (`Some`/`None` both directions), round-tripped,
parsed from the real captured JSON text, and printed to real, checked
Python (`def default_zero(v0): return (0 if (v0)[0] == "none" else
((v1 := (v0)[1]), v1)[-1])`, `def wrap_positive(v0): return (("none",)
if (v0 < 0) else ("some", v0))`), confirmed to run correctly under
actual Python too.

**Done** (genuinely N-ary records in the *real* recognizer): `RRecordN
(es : list real_expr)`/`RProjN (nskip : nat) (last : bool) (scrutinee
: real_expr)` generalize `RRecord3`/`RProj3_1`/`RProj3_2`/`RProj3_3`
(and the 2-field `RPair`/`RProj1`/`RProj2`) to *any* field count,
confirmed directly still working unchanged at 5 fields (a real
`Record point5 := mkpoint5 { ... 5 Z fields ... }.`): construction is
still a plain N-arg `expr:constructor` (just more args), and field
access is still a 1-case `expr:case` with an N-name `argnames` list,
all but one `"_"`. `RProjN`'s own `nskip`/`last` are exactly `RProj3_1`/
`RProj3_2`/`RProj3_3`/`RProj1`/`RProj2`'s own shapes generalized (one
`ESnd` skip per field position before the target, one final `EFst`
unless it's the list's last field) -- confirmed by recomputing each of
those four by hand against the general formula before trusting it.
Translating this needed no new `Lang.v`/`PyLang.v`/`Translate.v`/
`Json.v`/`PyPrint.v`/`PyRename.v` constructor at all: `RRecordN`/
`RProjN` translate into the same `EPair`/`EFst`/`ESnd` nested-pair
chain `RRecord3` already built, just over a list instead of 3 fixed
fields -- a `RealIR.v`-only change. The one genuine proof wrinkle:
`induction re`'s auto-generated induction hypothesis has nothing at
all to say about a nested `list real_expr` field's own elements
(confirmed directly by inspecting the open goal -- no `Forall`-shaped
hypothesis, just the list itself), the same obstacle the `Lang.v`-level
`ERecordN`/`ERecGroup` work (next section) already solved once via an
*outer* strong induction on a fuel/depth measure -- but wrapping
`real_to_expr_preserves_semantics` in that same `Hstrong`/
`well_founded_induction lt_wf` shell broke all ~30 of its *other*,
already-proven bullets at once (confirmed directly: introducing the
depth bound before `induction re` made `induction re` revert it back
into every bullet's own `IHre`, changing its type), so this proof
reaches for a different, less invasive tool instead: `fix SELF 1`,
Coq's tactic-mode self-reference (the equivalent of writing this
theorem as a `Fixpoint`), opened once at the very top and otherwise
inert -- every pre-existing bullet keeps using its own untouched
`induction re`-supplied IH exactly as before, and only `RRecordN`'s
new bullet reaches for `SELF` on each list element in turn (via a
fresh, local induction over the list), relying on `fix`'s own
guardedness check being more permissive than a plain `Fixpoint`'s
anonymous nested `fix` for this exact "element reached through a
separate nested list induction" shape (confirmed directly: the same
shape that blocked `real_eval`/`real_to_expr`/`real_expr_depth`'s own
`RRecordN` cases, which *do* need the mutual-helper/guard workarounds
the next section's own bullet points describe, is accepted without
complaint for a `fix`-tactic self-reference). `Print Assumptions`
confirms no new axioms. Along the way, fixed a real, pre-existing gap
in the 2-field case too: the old recognizer only matched a 2-arg
constructor literally named `"Pair"`, so a genuine 2-field `Record`
(whose constructor is named after its own declaration, e.g.
`"Mkpoint"`, not `"Pair"` -- confirmed directly) was silently
unrecognized; the new, uniformly-any-arity-and-name `RRecordN`
fallback closes that too. `examples/NaturalCoq.v`'s `mk5`/`getz5` (a
real 5-field `Record`, the 3rd-of-5 field) are the worked instance,
checked both ways: against the real Gallina definitions, round-tripped,
*and* parsed from the real captured JSON text (not just hand-built IR
matched by eye), printed to real, checked Python (`def mk5(v0, v1, v2,
v3, v4): return (v0, (v1, (v2, (v3, v4))))`, `def getz5(v0): return
(((v0)[1])[1])[0]`), confirmed to run correctly under actual Python.

**Done** (confirming the mutual-recursion side was never actually
capped): `RealJson.v`'s `decl_fixgroup_of_json`/
`real_fix_group_decl_of_module_json` (landed alongside `RCall`) never
had an arity cap in the code -- it iterates over a `decl:fixgroup`'s
whole `fixlist`, whatever its length -- but had only ever been
exercised, in any committed example, against a real captured *2*-member
group (`alt_from_true`/`alt_from_false`). "The code has no hardcoded
cap" and "a real 3+-way group has actually been run through it" are
different claims; only the first had been checked. Closed here, for
real: a genuine 3-way *cyclic* mutually-recursive group (`cycle_a`
calls `cycle_b` calls `cycle_c` calls `cycle_a`), run through `coqc`/
`Extraction Language JSON` during this session, confirmed to produce a
real captured `decl:fixgroup` with *three* `fixgroup:item`s, each
member's own cross-call the same ordinary `expr:apply`/`expr:global
<next member>` shape the 2-member group already had -- parsed by
`real_fix_group_decl_of_module_json` into exactly the hand-built
`real_fix_group_decl` `examples/NaturalCoq.v`'s `cycle3_decl` already
builds, found correctly starting from *any* of the three members' own
names (not just the first one listed), and run end to end through
`ERecGroup`/`translate`/real Python, confirmed on concrete lists both
through the member reached directly and through a cross-call to a
*different* member. No code changes were needed for this one -- the
gap was in what had been checked, not in what had been built.

## The N-field-record/mutual-recursion arity caps are liftable -- landed

The 2-field-record and 2-function-mutual-recursion caps elsewhere in
this file exist because Coq's *auto-generated* induction principle for
`expr` gives no usable hypothesis for an `expr` buried inside a `list
expr`-shaped field -- confirmed directly, first in an isolated
throwaway file, then applied to this project's real `Json.v` (see
below): a toy `ERecordN (fields : list expr)` with genuinely-N-ary
fields, proved via *strong induction on a size/fuel measure* instead
of structural induction on `expr`, closed with **no axioms or
admits**. The key move: generalize the goal to `forall n e, expr_fuel
e <= n -> ...`, induct on `n` via `well_founded_induction lt_wf`
rather than on `e`, and for the record case, derive a
`Forall`-shaped fact over `fields` by `Forall_forall` + `In` +
`lia` (every field's own `expr_fuel` is, by construction, strictly
less than the record's) -- each field's instance of the goal then
comes from the *same* blanket strong-induction hypothesis, not from
any constructor-specific name Coq would have had to invent. This is
exactly the same trick `Translate.v`'s own proof already uses (induct
on *fuel*, not on `e`) to get past `EApp`'s non-structural recursion
into a closure -- just applied to `Json.v`'s induction instead of
`Translate.v`'s.

**Done** (the refactor): `Json.v`'s real `parse_print_roundtrip` theorem
has been converted. That proof used to induct structurally on `e`
(`induction e as [...]`) across every constructor; it's now proved via
the `Hstrong` helper, strong induction on `expr_fuel e`
(`well_founded_induction lt_wf`), with every former `rewrite (IHk Hv
fuel' Hf)`-style call converted to the new blanket hypothesis's
calling convention (`rewrite ((IHn (expr_fuel ek) Hltk ek (le_n _)) Hv
fuel' Hf)`, `Hltk` freshly asserted from the (now `n`-indexed) fuel
bound by `lia`) -- a large, mostly mechanical change (done via a
one-off conversion script, then hand-verified), but a pure refactor:
no case's own reasoning changed, only how its induction hypothesis is
obtained. `Print Assumptions` confirms no new axioms, and the full
test suite passes unchanged.

**Done** (the feature): genuinely N-ary records, `ERecordN (fields :
list (var * expr))`/`EFieldN name e` (`VRecordN`), landed on top of the
refactor above, across `Lang.v`, `PyLang.v`, `Translate.v` and `Json.v`.
Two further obstacles beyond the induction one had to be cleared first,
both confirmed in an isolated throwaway file before touching the real
modules:

- `eval`/`peval`'s own `ERecordN` case can't be a top-level mutually
  recursive `Fixpoint eval ... with eval_fields ...` (Coq's guardedness
  checker rejects it, "cannot guess decreasing argument of fix" -- the
  same failure the 2-field cap's own history already hit once). The
  fix: an *anonymous* `fix` nested inside `eval`'s own body, scoped to
  just that one case, rather than a second top-level `Fixpoint`.
- `Translate.v`'s preservation proof and `Json.v`'s roundtrip proof each
  need one reusable helper lemma over the field list (`eval_fields_
  translate_correct`, `print_parse_fieldsN_roundtrip`), proved once by
  plain `induction` on the list and applied at the call site -- not
  re-derived inline per field.

`Print Assumptions` confirms no new axioms on either `translate_
preserves_semantics` or `parse_print_roundtrip`, and the full test
suite (`examples`/`test`/`physics`/`wave_sim`) passes unchanged.

**Done** (general mutually-recursive groups): `ERecGroup (fns : list
(var * var * expr))` lifts `ERecMut`'s 2-function cap the same way
`ERecordN` lifted `ERecord`'s 2-field one -- validated first in an
isolated prototype (including a genuine 3-way cross-call, f calling g
calling h), then landed across `Lang.v`, `PyLang.v`, `Translate.v` and
`Json.v`. It deliberately *reuses* `ERecordN`'s own machinery rather
than inventing a parallel position-indexed representation:
`ERecGroup fns` evaluates to a `VRecordN` whose fields are the
group's own names, each mapped to a `VClosureGroup fns cenv
self_name` -- so a member is picked out with the *same* `EFieldN`
that already picks a field out of any other `VRecordN`, and `EApp`'s
own case rebuilds every member's binding (itself included) with a
nested `fix` over `fns`, the same technique `ERecordN`'s own `eval`
case already needed, applied twice more (once in `eval`/`peval`'s
`EApp` case, once in `ERecGroup`'s own construction). `Translate.v`
needed three reusable helper lemmas this time (one more than
`ERecordN`'s two: a lookup-commutes-with-translation fact, plus one
each for the two nested `fix`es -- construction and rebinding), proved
once by `induction` on the member list; `Json.v`'s roundtrip proof is
`print_parse_fieldsN_roundtrip`'s own template with one extra
per-member identifier (`param`, alongside `name`) parsed. `Print
Assumptions` confirms no new axioms either side, and the full test
suite passes unchanged. `examples/Kinematics.v`'s `bounce3_expr`
(Example 10's bounce, with a third member, `"report"`, added to the
same group) is the worked instance, run as real, checked Python.

## Not proved: the pretty-printer

`PyPrint.v`'s `py_expr`/`py_function` are deliberately unproved, per
GOAL.md's distinction between "part of the translator" (needs proof) and
peripheral plumbing (doesn't). They're structure-preserving text
formatting, not a semantics-affecting transformation, so a bug there can
produce ugly or non-compiling Python but can't silently produce Python
that computes something different from what was proved — the walrus-
operator encoding of `PLet` is correct but not idiomatic, which is the
right kind of bug to be able to have at this layer.

That said, several *narrow, syntactic* properties of what this
unproved printer actually emits are still fully proved, each closed
under the global context (only the pre-existing `PrimFloat.float`
axiom, no new ones):
- `safe_py_name_not_keyword`: the generated function's own name
  (never alpha-renamed) is never one of Python's reserved words
  (`keyword.kwlist`, soft keywords like `match`/`case` deliberately
  excluded -- confirmed directly that `def match(): return 1` is
  valid Python).
- `fresh_name_not_keyword`/`fresh_name_is_py_identifier`: every
  *other* identifier `py_function` emits -- every `PyRename.fresh_name`-
  generated parameter or bound variable, shape `"v" ++ digits` -- is
  provably non-keyword (no Python keyword starts with `'v'`) and a
  syntactically valid Python identifier.
- `py_escape_text_is_escape_text`/`py_qstring_is_quote_string` (plus
  their `_parses_back` corollaries): `py_escape_text`/`py_qstring` are
  not just "similar to" `Json.v`'s own `escape_text`/`quote_string` --
  they *are* the same functions, so Python string/identifier literals
  for `EStrConst`/record field keys inherit `Json.v`'s already-proven
  round-trip theorems for free, no new round-trip proof needed.
- `rename_function_params_NoDup`: the parameter list `py_function`
  actually prints into `def f(p1, ..., pn):` is always pairwise
  distinct, for *any* input parameter list -- including one that had
  duplicate or keyword-colliding names before renaming -- ruling out a
  real Python `SyntaxError: duplicate argument 'x' in function
  definition` that a bug in the renaming pass could otherwise produce.
  Proved by naming `rename_function`'s previously-anonymous parameter-
  seeding `fix` (`mk_param_env`, no behavior change) so it has
  something to state a lemma about: `mk_param_env_snd_eq_seq` shows
  the renamed parameters are exactly `fresh_name` applied to
  consecutive seeds, then `fresh_name_injective` (PyRename.v, already
  proved for the CPython scoping fix) plus the standard library's
  `seq_NoDup` finish it.

None of this is the semantics-preservation theorem GOAL.md's trust
boundary explicitly declines to attempt for this file -- it's the
largest *bounded* slice of "verification where possible" that doesn't
require one.

Also checked, as a second CPython-specific evaluation-order question
alongside the walrus/closure-capture one the header above already
fixes: `PAnd`/`POr` print as Python's own `and`/`or`, which
short-circuit, while `peval`'s own `PAnd`/`POr` are strict (both
operands evaluated unconditionally, both required to succeed). Unlike
the walrus case, this is confirmed *not* to be a second instance of
the same "printing silently changes the result" bug class: whenever
`peval` proves `PAnd`/`POr` evaluates to `Some (VBool b)`, both
operands are already known to evaluate to definite booleans, and
`andb`/`orb`'s value agrees with what short-circuit evaluation would
have produced from the same two values -- short-circuiting only
changes whether Python's runtime *bothers* to evaluate the
already-proven-safe right operand, never what boolean it would
compute if it did. So there is no reachable case where this pipeline
proves an expression evaluates to `v` and real Python, running the
printed `and`/`or` text, computes a *different* `v`. See `PyPrint.v`'s
header for the full argument.

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

Records are now in too. The original form is still capped at exactly
two named fields: `ERecord k1 e1 k2 e2`/`EField name e` (a `VRecord`;
nesting handles more than two fields — `ERecord "a" e1 "rest" (ERecord
"b" e2 "c" e3)` for three — the same way `EPair`/`VPair` are already
capped at two components). That cap was never arbitrary — see the
induction obstacle explained above — but it is no longer the only
option: `ERecordN (fields : list (var * expr))`/`EFieldN name e` (a
`VRecordN`) now covers genuinely-N-ary records directly, once the
strong-induction/nested-`fix` fix above cleared the way. Generated
Python renders either record form as a `dict` literal keyed by the
field names (`{"x": ..., "v": ...}`), looked up by name (`state["x"]`)
rather than by position — see `examples/Kinematics.v`'s
`euler_step_record_expr`, Example 1's step again with named instead of
positional output.

Mutual recursion is now in too. The original form is still capped at
exactly two functions: `ERecMut f1 param1 body1 f2 param2 body2` (a
`VClosureMut`), `ERec`'s cousin for a pair of functions that may each
call *either* of themselves, not just `ERec`'s single self-call. Coq
values can't be cyclic, so "two closures that capture each other" is
only representable by bundling *both* bodies into one value (tagged
with a `which : bool` saying which of the two it currently stands
for) — `EApp` reconstructs *both* siblings' bindings into the
callee's environment on every call, generalizing the single
self-binding `ERec`'s `EApp` case already reconstructs. `ERecMut`
evaluates to `VPair clo1 clo2`, so the usual `EFst`/`ESnd` picks out
and calls either one. See `examples/Kinematics.v`'s `bounce_expr`,
Example 10: an elastic bounce where `"fall"` (running Euler steps)
hands off to `"rise"` (reflecting the velocity) — a genuine cross-call
between two functions defined together, generated as two chained
walrus assignments in Python (the same self-reference trick `PRec`
already uses, extended to two names). That cap is no longer the only
option either: `ERecGroup (fns : list (var * var * expr))` (a
`VClosureGroup`) covers an arbitrary number of mutually-recursive
functions directly, tagging each member by *name* (reusing
`ERecordN`'s own `VRecordN`/`EFieldN` machinery) rather than `which`'s
boolean — the representation limit above was specific to the
fixed-two-closures encoding, not mutual recursion itself. See
`examples/Kinematics.v`'s `bounce3_expr`, Example 15: Example 10's own
bounce with a third member, `"report"`, added to the same group — a
genuine three-way chain (`"fall"` calls `"rise"` calls `"report"`).

The last basic algebraic-data-type piece is in too: `EInl e`/`EInr e`/
`ECase scrutinee x1 case1 x2 case2` (`VInl`/`VInr`), a 2-alternative
*sum* type dual to `EPair`/`ERecord`'s *products* — a value tagged as
one of exactly two cases, eliminated the same two-case way
`EListMatch` already eliminates `Nil`/`Cons`. No arity cap is needed
here the way records/mutual-recursion needed one: a sum of more than
two alternatives already nests (`EInr (EInl e)` is "the third of three
cases"), so this one constructor-pair handles every finite sum, not
just a 2-case special case. `examples/Kinematics.v`'s Example 11 uses
it to turn Example 6's division precondition into a genuine value
(`EInl time` / `EInr v`, "stopped" vs. "never stops") instead of
`eval` simply getting stuck — directly the "extract an assumption
into a value, not just a runtime check" idea the records/division
examples were already gesturing at. Generated Python renders a sum
value as a tagged 2-tuple (`("inl", v)`/`("inr", v)`) and `ECase` as a
tag check with the same walrus-binding trick `EListMatch` already
uses.

A fifth scalar value shape is in too: `EStrConst s`/`EStrConcat e1
e2`/`EStrEq e1 e2` (`VStr`), genuine first-class strings alongside
`VZ`/`VBool`/`VFloat` — not just the identifiers `var` was already
used for everywhere else in this file. `EStrConst`'s payload was first
restricted exactly like an identifier (checked by `is_valid_ident`,
the same predicate `EVar`'s name already is), reusing `Json.v`'s
`quote_string`/`parse_qstring` identifier codec as-is — but that
restriction is lifted now: `expr_idents_valid` no longer checks
`EStrConst`'s payload at all, and `Json.v`'s `quote_text`/`parse_qtext`
is a real escaping codec (any string, including one containing a
literal quote or backslash, round-trips), proved the same way as
every other case, no new axioms. Deliberately not a *full* JSON
string codec: control characters (newline, tab, ...) pass through
unescaped rather than gaining their own escape sequences, since
unlike a quote or backslash they are not metacharacters in this
grammar and escaping them would be unneeded complexity, not
correctness. `PyPrint.v`'s `py_escape_text` mirrors the same two-
character escaping for Python's own double-quoted string syntax.
`examples/Kinematics.v`'s Example 12 first used this for an
identifier-shaped label (`"landed"`/`"falling"`); Example 14 reuses
the same condition for an ordinary human phrase with a space and an
embedded quote mark, which Example 12's restricted form could never
have represented. Generated Python renders a string value as a real,
escaped Python string literal, and `EStrConcat`/`EStrEq` as `+`/`==`
— nothing exotic, since Python's own strings already are what this
models.

Not yet covered, in roughly the order they'd likely be needed:

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

## Coquelicot support -- the `R`-vs-float bridge is landed; the recognizer isn't yet

A real request: extend `RealIR.v`/`RealJson.v`'s recognized fragment to
cover code built on [Coquelicot](http://coquelicot.saclay.inria.fr/)
(derivatives, limits, series, integrals over Coq's classical `R`). This
is *not* a small addition to the existing ingestion recognizer the way
`RCase`/`RRecord3` were — it was blocked on a "formalization of `R` and
its correspondence to IEEE-754 floats" prerequisite, for a structural
reason confirmed directly (not just argued) this session, by actually
installing Coquelicot (`opam install coq-coquelicot`, which needed the
`coq-released` repo added; it also needs `Require Coq.extraction.Extraction.`
stated explicitly before `Extraction Language JSON.` once Coquelicot is
loaded, since loading it otherwise leaves the extraction plugin's
vernacular grammar extension unavailable — a new, empirically-confirmed
wrinkle, not a hypothetical one) and extracting a genuine, Coquelicot-
proven function:

```coq
Definition quad (x : R) : R := x * x + 1.
Lemma quad_is_derive : forall x, is_derive quad x (2 * x).
Proof. intro x. unfold quad. auto_derive; auto. ring. Qed.
```

- Coq's `R` is axiomatic (Dedekind-cut/Cauchy-style, not a computable
  representation); extracting `quad` confirms this directly — the JSON
  output is 350KB, dominated by `ClassicalDedekindReals`'s own internal
  cut representation (`rabst`/`rrepr`/`rquot1`/`rquot2`/...) and an
  axiom-to-realize (`sig_forall_dec`), versus a few bytes for the
  equivalent `Z` function.
- But — also confirmed directly, and good news — `quad`'s own extracted
  *body* is clean: `rplus (rmult x x) (iZR (Zpos XH))`, i.e. a plain
  named-global-call shape, exactly the `RApp2`-style intrinsic pattern
  `RealIR.v` already recognizes for `Z.add`/`Z.ltb`. `R`'s own
  operations extracting to call sites this recognizable — not buried
  inside the cut machinery — was the open empirical question; it's
  answered. The same "ignore a well-known intrinsic's own extracted
  body, recognize only the call" move `RealIR.v` already makes for `Z`
  carries over to `R` unchanged.
- Coquelicot's own calculus lemmas (continuity, differentiability,
  `is_derive`, limits, integrals) are `Prop`-sorted *statements about*
  such functions, not themselves computational — under this project's
  own erasure model (`docs/duality.md`), a proof using them contributes
  nothing to extracted code either way (confirmed above: `quad_is_derive`
  does not appear anywhere in `quad`'s own extracted JSON), which is
  correct and expected, not a gap to close.
- So the actually computational part of a Coquelicot-based `Definition`
  is whatever real-valued *function* it names (built from `R`'s
  operations) — and translating that needs the `R`-vs-float
  correspondence below.

**Done**: `coq/RealBridge.v` is that correspondence, as a first,
explicit step, in the same spirit as the `PrimFloat`-to-`VFloat`
relationship: `R_of_float : PrimFloat.float -> R`, a genuine
`Definition` (not an axiom) interpreting a finite float's own
`Prim2SF` decomposition (`(-1)^sign * mantissa * 2^exponent`, `Json.v`'s
own convention, reused verbatim) as the real number it exactly denotes
— exact arithmetic, nothing to assume for that direction. Negation and
absolute value (sign-bit flip/clear in IEEE-754) correspond to `R`'s own
`Ropp`/`Rabs` *exactly*, proved outright (`R_of_float_opp`/
`R_of_float_abs`, no new axiom — `Print Assumptions` shows only
`PrimFloat`'s own existing primitives and `R`'s inherent classical axioms,
which any use of `Reals` already carries). For `+`/`*`, real rounding is
unavoidably involved; proving the standard relative-error bound from
`SpecFloat`'s own rounding definitions is exactly what Flocq exists to
do, and re-deriving Flocq-scale numerical-analysis machinery here would
be a new, nontrivial dependency this project's policy (see the `Z`/
`PrimFloat` sections above) deliberately avoids repeating — so
`R_of_float_add_rounded`/`R_of_float_mul_rounded` state the textbook
IEEE-754 binary64 round-to-nearest relative-error model (`fl(x+y) =
(x+y)(1+delta)`, `|delta| <= 2^-53`) as two explicit, honestly-scoped
`Axiom`s, in the same trust-boundary category `docs/duality.md` already
uses for "does `PrimFloat.float` arithmetic actually match IEEE-754" and
for `SF2Prim_Prim2SF` itself — assumed and named, not silently elided.

**Done** (a first, narrow extension): `RealIR.v`'s `real_expr` gained
`RFLit`/`RApp2`'s new `"rplus"`/`"rmult"` cases, recognizing exactly
the `quad` shape above and translating into the existing `EFConst`/
`EFAdd`/`EFMul` (`PrimFloat`, already in `Lang.v`); `real_to_expr_
preserves_semantics` is extended for both, fully proved, no new axioms
(`Print Assumptions` shows only the pre-existing `PrimFloat` primitives
— the same set every other `PrimFloat`-backed theorem in this project
already carries). Deliberately **not** the same trust move `RZLit`
makes for `Z`: Coq's `Rplus`/`Rmult` have no computational content at
all (confirmed above), so there's no "Coq's own stdlib function,
called directly" option here — this fragment's `real_eval` models
`"rplus"`/`"rmult"` *directly* as `PrimFloat` arithmetic instead (the
same trust category as every other `PrimFloat`-backed operation
already in this project, not a new kind of assumption), with the
correspondence to the *original*, classical-`R` source semantics
tracked separately, and only approximately, by the `R_of_float`
bridge above — composing the two into one *general, compositional*
"translating a Coquelicot-authored function preserves its
mathematical meaning up to a stated rounding bound" theorem is
deliberately not attempted: doing that for arbitrarily nested
arithmetic needs real error-propagation tracking (how do two already-
approximate sub-results' errors combine under a further `+`/`*`?),
which is exactly the Flocq-scale work the bridge's own section above
already declines to re-derive — not a new boundary. `examples/
CoquelicotDemo.v`'s `quad_ir`/`quad_expr` is the worked instance,
checked end to end: the captured JSON above, hand-encoded, translated,
and run as real Python (`def quad(v0): return ((v0 * v0) + (...2.0**-52
decomposition of 1.0...))`), with a concrete-instance correspondence
check (`quad(3) = 10`, exact — no rounding error to propagate for this
one input) standing in for the general theorem the paragraph above
explains is not yet in scope.

**Done** (rounding out the four basic operations): `"rminus"`/`"rdiv"`
translate into the existing `EFSub`/`EFDiv`, the same way `"rplus"`/
`"rmult"` do — `real_to_expr_preserves_semantics` extended again, no
new axioms.

**Done** (`"ropp"`, including the signed-zero edge case): a real,
dedicated `EFOpp` landed in `Lang.v` (and its mirror, `PFOpp`, in
`PyLang.v`), calling `PrimFloat.opp` directly — deliberately *not*
translating unary negation as `EFSub (EFConst 0) e` the way a
recognizer without its own constructor would have to, since that
would compute `PrimFloat.sub 0 f` where the exact value needed is
`PrimFloat.opp f`, and those two genuinely differ for `f = 0` under
IEEE-754 signed zero (`0.0 - 0.0 = +0.0`, but `opp 0.0 = -0.0`,
confirmed directly). A dedicated constructor sidesteps the edge case
entirely rather than special-casing around it. This touched every
layer the other float operations already touch —
`Lang.v`/`PyLang.v`/`Translate.v`/`Json.v`/`PyPrint.v`/`PyRename.v`
(including `rename_pyexpr_correct`'s own, freshly-completed
correctness theorem, which needed one more case, following the exact
pattern its other unary cases already use) — fully proved throughout,
no new axioms beyond the pre-existing `PrimFloat` ones (`PrimFloat.opp`
joins the set `PrimFloat.add`/`PrimFloat.sub`/etc. were already in).
`RealIR.v`'s `RApp1` now recognizes `"ropp"` too, translating into
`EFOpp`, confirmed directly (`eval` negates `3.0` to `-3.0` and `0.0`
to `-0.0`, exactly matching `PrimFloat.opp`, not the `EFSub`
workaround's wrong answer for the zero case).

**Done** (ingested from the real JSON *text*, not just hand-built):
`RealJson.v` gained one small addition -- a Coquelicot-adjacent `R`
literal extracts as `expr:apply`/`expr:global "iZR"` applied to a
nested `Z` numeral (confirmed directly, in the real captured JSON),
which the file's already-generic `expr:apply`/`expr:global` dispatch
would otherwise turn into an *unrecognized* `RApp1 "iZR" (RZLit 1)`
(`"iZR"` was never a name `RealIR.v` knows, only `RFLit` is). A new
`float_of_Z` turns the parsed `Z` numeral directly into that `RFLit`
instead. `examples/CoquelicotDemo.v`'s `quad_decl_json` is the real
captured JSON bytes for `quad`'s own `decl:term` (not retyped by
hand beyond JSON's own `"` escaping), run through
`real_decl_of_module_json`, checked by `vm_compute` to produce
*exactly* the same `real_decl` the hand-built `quad_ir` above was
checked against -- and from there translated, evaluated, and printed
to the same Python as the hand-built version, closing the loop this
section's very first entry opened. This is also the first time
`RealJson.v`'s own parser is actually exercised in a *committed*
example at all, for any fragment (confirmed by checking: nothing in
`examples/`/`test/` previously called `real_decl_of_module_json`,
despite the four `Z`/`bool`-fragment instances this file's own header
already claims were "confirmed" -- apparently only ever checked in
now-discarded scratch files during an earlier session, not landed).

A real limitation surfaced doing this, now root-caused rather than
just worked around: parsing the *whole* captured module (~350KB,
dominated by `ClassicalDedekindReals`'s own cut representation -- see
above) made `vm_compute` segfault on the dev machine. Confirmed
directly to actually be a shell stack-size limit, not a bug in the
parsing logic or a fundamental `vm_compute` defect: the default
`ulimit -s` here is 12.5MB; raising it to 128MB (`ulimit -s 131072`)
is enough that the *same* `coqc` invocation, on the *same* 350KB
string, no longer segfaults at all (it was still running, correctly,
past the 60-second mark it was given before that check was cut off
for time) -- so the underlying cause is `vm_compute` representing a
string that large as deeply nested `String` constructors, consuming
stack proportional to the string's length, not a `vm_compute` bug or
a flaw in this file's own recognizer. Separately confirmed: once given
enough stack (512MB tried), the full module *does* finish, correctly
(`Some {| rd_argnames := ["x"]; rd_body := ... |}`, the same answer as
the per-declaration JSON below), but takes about 90 seconds of CPU --
consistent with this file's own header's already-documented O(n^2)
string-scanning behavior at this scale, scaled up from the 22KB/45s
figure already on record there. `examples/CoquelicotDemo.v` still uses
the per-declaration JSON object, both because this recognizer was
never going to look at the surrounding 349KB of cut-representation
bulk anyway, and because baking a `ulimit`/90-second dependency into
a routine `coqc` build would be a real cost for every future build,
not a one-off probe -- the right fix for the *general* case is
`Extract.v`'s own realizer-level string-handling speedup (already
proven effective for the extracted OCaml path), not a bigger stack --
**done**, see this section's own later entry below (90s down to 1.28s
under `vm_compute`, `ulimit` still needed but now for an orthogonal,
unrelated reason: elaborating a 350KB string *literal*, not this
project's own parsing code).

**Done** (`"rminus"`/`"rdiv"`/`"ropp"` confirmed against real JSON
text too, not just `"rplus"`/`"rmult"`): a second real probe --
`combo (x y : R) := (x - y) / (- y)`, actually run through `coqc` with
`coq-coquelicot` installed, not assumed by analogy -- confirms its
extracted JSON is exactly `rdiv (rminus x y) (ropp y)`, the
`RApp2`/`RApp1` shapes `RealIR.v`/`RealJson.v` already recognize, no
further parser changes needed. `examples/CoquelicotDemo.v`'s
`combo_decl_json` is that real captured JSON (one declaration, for
the same `vm_compute`-stack reason as `quad`'s), parsed, translated,
evaluated (`(10 - 4) / (-4) = -1.5` exactly), and printed to real,
checked Python (`def combo(v0, v1): return ((v0 - v1) / (-v1))`).

**Done** (`"rabs"`, including the same signed-zero edge case `"ropp"`
had): a fresh probe, `absdiff (x y : R) := Rabs (x - y)`, actually run
through `coqc` with `coq-coquelicot` installed, confirms `Rabs`
extracts as a plain unary `expr:apply`/`expr:global "rabs"` call --
despite `Rabs`'s own Gallina definition being a decidability case
split (`Rcase_abs`/`total_order_T`), not anything resembling a single
primitive -- so the extraction-shape bet already made for `"ropp"`
holds here too, confirmed rather than assumed by analogy. Translating
`"rabs"` as an `EIf`-based workaround (`EIf (EFLt e (EFConst 0))
(EFOpp e) e`, built from already-existing constructors) would be
*wrong* at `e = -0.0`: `-0.0 < 0.0` is `false` under IEEE-754, so the
`else` branch returns `-0.0` unchanged, while `PrimFloat.abs (-0.0) =
0.0` -- confirmed directly, including in real Python
(`math.copysign(1, abs(-0.0)) == 1.0`). So a real, dedicated `EFAbs`
landed in `Lang.v` (and its mirror, `PFAbs`, in `PyLang.v`), calling
`PrimFloat.abs` directly, the same move `EFOpp` already made for
`"ropp"` -- threaded through every layer (`Translate.v`, `Json.v`'s
`"fabs"` tag plus parser/round-trip proof, `PyPrint.v`'s `abs(...)`
rendering, `PyRename.v`'s `rename_pyexpr_correct` case, `RealIR.v`'s
`RApp1` dispatch and its own preservation proof). `Print Assumptions`
across every touched theorem shows only `PrimFloat.abs` joining the
pre-existing `PrimFloat` axiom set -- no new kind of trust boundary.
`examples/CoquelicotDemo.v`'s `absdiff_decl_json` is the real captured
JSON (`rabs (rminus x y)`), parsed, translated, evaluated (`|4 - 10| =
6` exactly), and printed to real, checked Python (`def absdiff(v0,
v1): return abs((v0 - v1))`, confirmed to run correctly under actual
Python too).

**Done** (`"sqrt"`, Coq's own `Reals.R_sqrt.sqrt`): a fresh probe,
`hyp_len (x y : R) := sqrt (x * x + y * y)`, confirms `sqrt` extracts
as a plain unary `expr:apply`/`expr:global "sqrt"` call, the same
shape `"ropp"`/`"rabs"` already have, even though its own Gallina
definition goes through `Rsqrt_exists` and a classical completeness
argument. Unlike `"ropp"`/`"rabs"`, there was not even an
*almost*-right workaround to reject: nothing already in `expr` --
built only from `+`/`-`/`*`/`/` -- can compute a square root at all,
so a dedicated `EFSqrt` (calling `PrimFloat.sqrt` directly) is the
only way to support this operation, not an exactness refinement.
Threaded through every layer the same way `EFOpp`/`EFAbs` were
(`Lang.v`/`PyLang.v`, `Translate.v`, `Json.v`'s `"fsqrt"` tag plus
parser/round-trip proof, `PyRename.v`'s `rename_pyexpr_correct` case,
`RealIR.v`'s `RApp1` dispatch and its own preservation proof), with
one new printing wrinkle specific to this operation: Python's
`math.sqrt` needs `math` imported, and `py_function` emits a bare
`def` with no header to put an import in (`PyPrint.v`'s printer has
no notion of a statement, only expressions), so `PyPrint.v` renders
`EFSqrt` as the self-contained expression `__import__("math").sqrt(...)`
instead -- confirmed directly to compute the exact same bits as
`math.sqrt`, sign of zero included (the importless alternative,
`x ** 0.5`, was confirmed *wrong* at `x = -0.0`: it gives `+0.0`, not
`-0.0`, in real Python, while `PrimFloat.sqrt (-0.0) = -0.0` matches
IEEE-754's sign-preserving sqrt-of-zero rule). `Print Assumptions`
across every touched theorem shows only `PrimFloat.sqrt` joining the
pre-existing `PrimFloat` axiom set. `examples/CoquelicotDemo.v`'s
`hyp_len_decl_json` is the real captured JSON (`sqrt (rplus (rmult x
x) (rmult y y))`), parsed, translated, evaluated (`hyp_len 3 4 = 5`
exactly -- a real Pythagorean triple, no rounding), and printed to
real, checked Python (`def hyp_len(v0, v1): return
__import__("math").sqrt(((v0 * v0) + (v1 * v1)))`, confirmed to run
correctly under actual Python too).

**Done** (`"rinv"`, `"rmax"`/`"rmin"`): three more probes -- `inv_sum
(x y : R) := / (x + y)`, `bigger_plus_one (x y : R) := Rmax x y + 1`,
`smaller_plus_one (x y : R) := Rmin x y + 1` -- confirm `/ e` extracts
as a plain unary `rinv` call, and `Rmax`/`Rmin` as plain binary
`rmax`/`rmin` calls (not eta-reduced to a bare `expr:global`, which a
point-free `Definition bigger (x y : R) : R := Rmax x y.` is confirmed
to trigger -- wrapping the call in `+ 1` avoids it). Each needed a
different kind of addition: `"rinv"` needed *no* new `Lang.v`
constructor at all -- `PrimFloat.div` is already correctly-rounded, so
`1.0 / x` computes the correctly-rounded reciprocal exactly, so
`"rinv"` just translates to the already-proven `EFDiv (EFConst 1) e`.
`"rmax"`/`"rmin"` needed a real `EFMax`/`EFMin`, but not calling one
more `PrimFloat` primitive -- `PrimFloat` has no native max/min at
all, so they're defined directly in Gallina via `PrimFloat.ltb`
(already trusted): `if f1 < f2 then f2 else f1` for max, `if f2 < f1
then f2 else f1` for min. Which operand a signed-zero tie returns is a
genuine, explicit choice made here (classical `R` has no signed zero
at all, so there's no "faithful to Coquelicot" answer to match in the
first place -- the same kind of boundary `RealBridge.v`'s own
rounding axioms already draw) -- confirmed directly to match real
Python's own `max`/`min` builtins' tie-breaking exactly (`max(0.0,
-0.0) = 0.0`, `max(-0.0, 0.0) = -0.0`, both returning their *first*
argument on a tie), so `PyPrint.v` renders them as plain `max(...)`/
`min(...)` calls. `Print Assumptions` shows no new axioms (`rinv`
reuses `div`; `rmax`/`rmin` reuse `ltb`, both already in the set).
`examples/CoquelicotDemo.v`'s `inv_sum`/`bigger_plus_one`/
`smaller_plus_one` are the worked instances: checked against concrete
values (`1/(3+1) = 0.25`, `max(3,5)+1 = 6`, `min(3,5)+1 = 4`),
parsed from the real captured JSON text, and printed to real, checked
Python, confirmed to run correctly under actual Python too.

**Not viable the same way** (confirmed, not assumed): `exp`/`ln`/
`pow` were considered next, but `PrimFloat` has *no* native
transcendental-function primitive at all (confirmed directly:
`Print PrimFloat` lists only `abs`/`sqrt`/`opp`/`eqb`/`ltb`/`leb`/
`compare`/`mul`/`add`/`sub`/`div` -- no `exp`/`ln`/`pow`), unlike
`sqrt` (a primitive) or `rmax`/`rmin` (definable from an existing
primitive, `ltb`). Supporting them would need a *new category* of
trust boundary -- an `Axiom` asserting some IEEE-754-correct
`exp`/`ln`/`pow` exists and that Python's `math.exp`/`math.log`/`**`
match it, the same shape `RealBridge.v`'s own two rounding axioms
already are, but for a reference semantics this project cannot
compute in Gallina at all (unlike `rmax`/`rmin`, which compute a real
answer via `ltb`) -- not a bounded addition on the same footing as
the others above, and not attempted here.

**Done** (`R` literals beyond small-integer `iZR`): checked directly,
not assumed, which literal shapes actually needed new work. A
negative (`-2`) and a large (`1000000`) integer literal both already
parsed correctly through the *existing* `iZR`/`float_of_Z`/
`positive_of_json` machinery with zero changes -- confirmed directly
(`RFLit (-0x1p+1)` and `RFLit 0x1.e848p+19` respectively), since
`positive_of_json`'s nested `XI`/`XO`/`XH` reconstruction was never
actually limited to "small" numbers, and `Zneg` was already a
recognized case alongside `Zpos`/`Z0` -- the roadmap's own earlier
"small-integer" phrasing undersold what already worked. Likewise
`1/2` (`Rdiv (IZR 1) (IZR 2)`) already parses correctly as `RApp2
"rdiv" (RFLit 1) (RFLit 2)` with no changes, since `rdiv`/`iZR` were
each already recognized independently. The one genuine gap: a
*decimal* literal (`3.14`) does **not** extract as `iZR` at all --
confirmed directly (a fresh probe, `decimal_lit (x : R) := x + 3.14`)
-- it extracts as `q2R (Qmake num den)`, `QArith`'s own rational-to-
real coercion applied to a `Q` built the same `Zpos`/`Zneg`/`Z0`/
`XI`/`XO`/`XH` way an ordinary integer literal already is. `num/den`
is in general not exactly representable in binary64 (`3.14 =
314/100`, and `100` is not a power of two) -- but that is the same
single rounding step any decimal-to-float literal already needs
(confirmed directly: Python's own literal `3.14` is already the
nearest binary64 double, not the exact rational), so `RealJson.v`'s
new `rational_of_json` computes `PrimFloat.div (float_of_Z num)
(float_of_Z (Zpos den))` once at parse time -- the correctly-rounded
quotient through the one already-trusted primitive that performs it,
not a new approximation. `Print Assumptions` shows no new axioms.
`examples/CoquelicotDemo.v`'s `decimal_lit_decl_json` is the real
captured JSON, parsed to `RFLit 0x1.91eb851eb851fp+1`, confirmed
bit-for-bit identical to Python's own `3.14` literal
(`float.fromhex("0x1.91eb851eb851fp+1") == 3.14`), and printed to
real, checked Python, confirmed to run correctly under actual Python
too.

**Done** (extending the string-handling speedup to the `vm_compute` path
too, not just the extracted-OCaml one `Extract.v`'s own `Extract
Constant` pragmas already covered): root-caused directly, not
guessed. `Json.v`'s `parse_qtext` (the entry point every quoted string
in the input goes through) used to call `String.length` on the
*entire remaining input* every time a quoted string started, purely
to hand `parse_text_chars` a fuel bound it never structurally needed --
harmless for the OCaml path (`Extract.v`'s realizer ignores fuel and
scans directly) but a genuine O(n^2) cost in pure Gallina/`vm_compute`,
since most of a real `coqc`-extracted module's bytes *are* quoted
strings (every `"what"`/`"name"` key and value). `parse_text_chars` is
rewritten to recurse structurally on the string itself with no `fuel`
parameter at all -- its backslash-escape case recurses two characters
deep via nested destructuring (`rest2` obtained by matching `rest`,
itself obtained by matching the original string), the same
iterated-subterm shape Coq's guard checker already accepts for
`Nat.div2`-style `S (S n')` recursion, so no well-founded-recursion
machinery was needed. `parse_qtext` is `Opaque` past its own proof
block and every downstream file (`PyPrint.v`, `RealJson.v`) only ever
rewrites with `parse_qtext_print`'s *statement*, never its
implementation, so the fix (and its reproof, actually slightly
*shorter* than before since the fuel side-conditions disappear) stayed
entirely local to `Json.v` -- confirmed by rebuilding the whole
project (`coq`, `examples`, `physics`, `test`, `wave_sim`) with no
other file touched besides `Extract.v`'s matching realizer-arity
update. Measured, not estimated: a real ~350KB module (the same
Coquelicot-derived capture this section's `quad`/`combo`/`absdiff`
probes above are each one declaration of) was re-extracted fresh via
`coqc`/`coq-coquelicot`, and a standalone microbenchmark walking the
*identical* string and calling old-vs-new `parse_qtext` on every one
of its 12,409 quoted strings (same count, same result, both versions)
went from 65.6s to 0.4s under `vm_compute` -- a ~165x speedup, and
`real_decl_of_module_json` on the *actual* full module (not a
microbenchmark) now completes in 1.28s under `Time Eval vm_compute`,
down from the ~90s this section documented above. A raised `ulimit -s`
is still needed to even reach that point, though -- confirmed this is
an *orthogonal*, unrelated cost: `coqc`'s own front-end elaborating a
350KB string *literal* into the kernel's nested `String` term (before
`vm_compute` ever runs) is already O(stack depth proportional to
string length) by construction, independent of which parser function
is later applied to it. That's a cost of writing a 350KB string as a
literal in a `.v` file at all, not of this project's own parsing code
-- out of scope for this fix, and not expected to matter for the
remote-deployment path (the deployment entry below), where the agent's
own `.v` files are the proof source, not a `.v` file containing a
pre-serialized giant JSON string constant.

Still not done: anything
nested deeper where the error-propagation question above would
actually start to matter; and
the general compositional correspondence theorem itself, if ever
prioritized -- which the paragraph above already scopes as Flocq-scale
work, not a bounded next step.
`coq-coquelicot`/`coq-mathcomp-ssreflect` are installed in this dev
environment (via `coq-released`) so further real captures are possible,
but neither is a build dependency of `coq2py` itself — they only
produce example *source* `.v` files to extract from, the same
"devtime-only" role `coqc` itself already plays for every other
`RealJson.v` capture.

**Done** (`exp`/`ln`/a binary real power — a new, honestly-scoped axiom
category, not a bounded addition to the existing `rplus`/`rmult`/...
style): `PrimFloat` has no native transcendental primitive at all
(confirmed directly: `Print PrimFloat` lists `abs`/`sqrt`/`opp`/`eqb`/
`ltb`/`leb`/`compare`/`mul`/`add`/`sub`/`div` and the bit-level
`of_uint63`/`normfr_mantissa`/`frshiftexp`/`ldshiftexp`/`next_up`/
`next_down` — nothing resembling `exp`/`log`/`pow`), and unlike
`rmax`/`rmin` there is no finite composition of what's already in
`expr` that computes one either. `Lang.v` gains three new, genuinely
project-introduced `Axiom`s — `prim_exp`/`prim_ln : float -> float`,
`prim_pow : float -> float -> float` — kept to the barest honest claim
(a function of the right type exists; no equation or property about
what it computes is assumed, not even "agrees with classical
`Rpower`/`exp`/`ln` on any input"). That bare-existence scope is what
makes `EFExp`/`EFLn`/`EFPow`'s `translate_preserves_semantics` cases
trivial — `eval`/`peval` call the same opaque axiom on the same
argument, the same reason `EFSqrt`'s own case already was, not because
anything is known about the result. The one cost this honestly defers
elsewhere: with no Gallina body, `prim_exp`/`prim_ln`/`prim_pow` leave
`vm_compute`/`simpl` permanently stuck on them, so the "matches this
exact float" check every arithmetic-only example in this project uses
isn't available for anything built from these — what's checked instead
(`examples/CoquelicotDemo.v`) is a fully symbolic `reflexivity` showing
`real_eval`/`eval` reduce *exactly* down to the opaque call and no
further (the same technique `examples/physics/Discretize.v`'s
`one_pass_symbolic_7point` already uses), the full translation/
round-trip proof chain, `Print Assumptions` confirming exactly these
three new axioms appear (alongside `PrimFloat`'s own pre-existing
kernel primitives, nothing from `Json.v`'s unrelated float-codec
axioms), and the *generated Python* actually running and producing the
numerically expected answer for a concrete, hand-checked input — real
`math.exp`/`math.log`/`math.pow` are computable, even though the
axiomatized Coq side deliberately isn't.

No new `RealIR.v` constructor was needed: confirmed directly (three
fresh probes, actually run through `coqc` with `coq-coquelicot`
installed, each wrapping the transcendental inside a non-trivial
expression to dodge an eta-reduction edge case confirmed separately —
a *bare* wrapper like `myexp (x : R) := exp x` extracts as `argnames
[]` with body just the bare global `exp`, since Coq's extraction
eta-contracts the trivial identity application), `exp`/`ln` extract as
plain unary `expr:apply`/`expr:global` calls (the same shape `RApp1`
already recognizes for `ropp`/`rabs`/`sqrt`) and `Rpower` extracts as a
plain binary call named `rpower` (the same shape `RApp2` already
recognizes for `rmax`/`rmin`) — so this closed with three new names in
the existing, generic `RApp1`/`RApp2` dispatch, not a new recognizer
shape. `PyPrint.v` renders `EFPow` as `math.pow(...)`, deliberately not
Python's own `**` operator: confirmed directly that `**` silently
returns a *complex* number for a negative base and non-integer exponent
(`(-1.0) ** 0.5` in real Python), while `math.pow` raises `ValueError`
instead — a loud failure being the honest choice for a domain
`EFPow`'s own `float`-only semantics never anticipates leaving.
`Extract.v` realizes the three new axioms via `coq-core.kernel`'s own
`Float64.of_float`/`Float64.to_float` (the same conversion
`ExtrOCamlFloats` itself already realizes `PrimFloat.float` against)
bridging to OCaml's `Stdlib.exp`/`Stdlib.log`/`( ** )` — the one place
in this whole codebase where a numeric result is produced with nothing
in Coq to check it against, an honest, unavoidable shape for this
particular trust boundary, not a shortcut.

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

`runtime/wave1d.py` remains a hand-written, explicitly unproven external
runtime — in the same trust category as `ocaml/driver/main.ml`'s CLI glue
or `PyPrint.v`'s pretty-printer — that allocates the numpy grid, applies
Dirichlet boundary conditions, and drives the time-stepping loop, calling
the *literal* extracted `leapfrog_update` function (imported, not
re-transcribed) once per step, over whole-array numpy slices (its body is
plain `+`/`-`/`*`/`**`, so passing numpy arrays instead of scalars just
works via Python's operator overloading — no separate "vectorized"
rewrite was needed). This remains a real, if narrower, way to reach
"extracted Python actually running a simulator" at numpy speed, and is
*not* being replaced by what follows below.

**Done** (the whole-grid loop, as a second, proven, list-based
simulator): `examples/physics/Discretize.v`'s own final section closes
the "arrays/loops aren't in `expr`/`pyexpr` yet" gap this entry used to
end on — not via a new array type, but by noticing `Lang.v` already had
everything needed: `VList`/`ENil`/`ECons`/`EListMatch` (a real,
structural list, not an encoding), `ERec`/`ELam`/`EApp` (self-recursive
closures, curried for the two-list case the way `RealIR.v`'s own
`RSelfN` comment already established multi-argument recursion works),
`EPair`/`EFst`/`ESnd`, `ELet`, and `ERepeat` (bounded iteration) — so
`compute_interior_expr`/`one_pass_expr`/`wave_sim_expr` are a *pure
composition* of already-proven pieces, needing zero new `Lang.v`/
`PyLang.v`/`Translate.v`/`Json.v`/`PyPrint.v`/`PyRename.v` constructors,
the same "nothing new to re-prove below this line" shape `RealIR.v`'s
`real_fix_group_decl_to_expr` (landing on `ERecGroup`) already has.
`compute_interior_expr` walks the current and previous time steps' grids
in lockstep, rebinding each 3-point stencil (plus the matching previous
value) to the exact names `leapfrog_update_expr` already expects via
`ELet` — reusing that already-proven update formula verbatim, not
re-deriving it — and stops (fixing the boundary to `0`) once fewer than
3 elements remain; `one_pass_expr` is one whole-grid step; `wave_sim_expr
nt` chains `nt` such steps via `ERepeat`, threading `(prev, curr)` as its
own loop state — the exact `u_prev, u_curr = u_curr, u_next` swap
`runtime/wave1d.py` already does, now *inside* the proven fragment too.

What's actually proved about it, stated precisely (the same "concrete
run, not a universally-quantified theorem" standard every other
`ERec`-based recursive example in this project already uses, for the
same reason — `RealIR.v`'s header on `real_fix_decl`: a self-recursive
function's own recursion depth is its argument's size, not a static
property of the term): `one_pass_symbolic_7point` is *fully symbolic* in
every grid value (not one hand-picked numeric instance) for a fixed
7-point grid, confirmed by `reflexivity` alone to reduce to the exact
closed-form update formula at every interior point, for *any* values —
confirming the whole stencil-over-two-lists machinery, not just the
already-proven per-point formula in isolation. `wave_sim_3steps_7point`
is a genuine multi-step run of the whole simulator (not just one pass) —
a unit pulse on a 7-point grid, 3 time steps, Courant number `r = 1` —
cross-checked against an independent, from-scratch Python computation of
the same scheme (not derived from this expression) before trusting it.
`Print Assumptions` on both shows no new axioms beyond the pre-existing
`PrimFloat` primitives. The generated Python (a list-of-nested-tuples
simulator, the same representation every other list in this project
already renders as) was run for real too, confirmed to produce the exact
pair `wave_sim_3steps_7point` computes in Coq.

Honestly scoped, what this is *not*: not a replacement for
`runtime/wave1d.py`'s numpy-array-based fast path (a second, slower,
proven way to run the simulator, not a substitute for the first), and
not an arbitrary-grid-length inductive theorem (the fixed-size,
symbolic-values standard above, consistently with every other recursive
`expr` example already in this project) — formalizing numpy's own array
semantics specifically (mutable, fixed-size, vectorized) remains the
substantially larger undertaking this entry originally deferred, if ever
prioritized; what's closed here is "arrays/loops as *some* proven `expr`
construct", not "numpy's own semantics as a proven `expr` construct".

## Deployment target: the remote host

Per GOAL.md, the remote deployment host is meant to run `coqc` (already
installed there) against proofs a theory-evaluating agent writes at
runtime, feeding the resulting JSON IR to an already-built
`coq2py` binary copied over from the dev machine — not to rebuild
`coq2py` itself.

**Done**: the packaging/invocation protocol itself — what exactly ships
to that host, how the agent invokes it, how results come back — is now
built and documented in full in `docs/deployment.md`; this entry just
summarizes what that closed and what it deliberately didn't try to.

A real, previously-unnoticed functional gap surfaced doing this, not
just a documentation gap: `coq/Extract.v`'s own `Extraction "coq2py_core.ml"
...` root list only ever named `real_decl_of_module_json`/
`real_fix_decl_of_module_json` among the four `real_*_of_module_json`
entry points `RealIR.v`/`RealJson.v` actually prove — Coq's `Extraction`
only pulls in the transitive dependencies of what's named as a root, so
`real_fix_decl_multi_of_module_json` (a real *multi*-argument
self-recursive `Fixpoint`, `RSelfN`/`RCallN`'s own entry point) and
`real_fix_group_decl_of_module_json` (a real N-way mutually-recursive
group) were proven in Coq but **never reached the compiled binary at
all**, confirmed directly by grepping the generated `.mli` before this
fix (absent) and after (present). A theory-evaluating agent writing
either shape of proof would have hit a wall at the OCaml layer even
though the underlying Coq recognizer already handled it — this is now
fixed by adding both (plus their `_to_expr` counterparts) to the
`Extraction` root list.

The CLI itself (`ocaml/driver/main.ml`) previously only read this
project's own hand-rolled `Json.v` wire format for a bare `expr` —
never Coq's actual `Extraction Language JSON` module output, which is
the only thing a real agent's `coqc` run would ever produce. A new
`coq2py --real <function-name>` mode reads a whole real module on
stdin and tries, in declaration order, all four recognized shapes
(plain/possibly-multi-arg non-recursive, single-argument
self-recursive, multi-argument self-recursive, N-way mutually-recursive
group), applying the right number of parameters via `EApp` (and, for a
group, projecting the named member via `EFieldN` first) before handing
the result to `translate`/`py_function` — the same calling convention
every hand-built multi-argument example in this repository already
uses at its own call site, not a new one invented for this. Confirmed
end to end, not just compiled: all four shapes were run through the
actual staged binary against **genuinely `coqc`-extracted** JSON (not
this project's own fixtures) — a fresh ~350KB real Coquelicot capture
for the plain-declaration case (`quad`), a fresh throwaway single-arg
self-recursive probe (`any_true`), and the project's own committed
`all_match`/`sum_list` (multi-arg self-recursive) and `cycle_a`/
`cycle_b`/`cycle_c` (N-way group, entered from all three members)
module captures — every one byte-for-byte identical to that example's
own already-proven, hand-checked generated Python.

Also confirmed, not assumed: the built binary's only runtime
dependencies (`ldd`) are the OS's own `libc`/`libm`/`libthr` — nothing
from `coq-core` or OCaml's own runtime, meaning the `coq-core.kernel`
link dependency `Extract.v`'s header already documents is exactly the
link-time-only cost it claims to be. A new `gmake package` target
builds (at dune's `release` profile, stripped) and stages the single
deployable binary into `dist/`; copying just that file to an empty
directory with no build tooling present and running it there
(simulating the actual remote-host copy) worked identically to running
it from the build tree.

Still not done, deliberately out of scope for this entry: anything
about *which* Coq programs are recognized at all (modules/typeclasses/
coinductives, numpy-shaped arrays — this section's sibling entry
below), and the open question of how the agent's own harness decides
*which* declaration name(s) in its proof to extract (left to that
harness, same as any other CLI tool's caller deciding its own
arguments) — not something `coq2py` itself needs an opinion on.
