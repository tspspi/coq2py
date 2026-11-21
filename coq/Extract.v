(** Extract.v

    Bootstraps the proven Gallina pipeline (Lang/PyLang/Translate/Json/
    PyPrint) into an OCaml module via Coq's standard, mature extraction
    backend -- deliberately *not* a custom extraction backend of our own,
    per the discussion in GOAL.md: this reuses the same trusted mechanism
    every other Coq project already relies on, rather than adding a new,
    unproven piece of machinery to the trusted base.

    Extracted OCaml's [string] is [char list], not OCaml's native
    [string]; the driver (ocaml/driver/) converts at the boundary. That
    conversion is boundary glue, not part of the proven pipeline. *)

Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Require Import RealIR.
Require Import RealJson.
Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.
Require Import ExtrOCamlInt63.
Require Import ExtrOCamlFloats.

Extraction Language OCaml.

(** Native-OCaml realizers for bool/option/list/pair, strings, and Z --
    all standard, Coq-shipped pragmas used by essentially every real-world
    Coq extraction, not anything bespoke to this project. [ExtrOcamlZInt]
    maps [Z] to OCaml's native fixed-width [int] rather than an arbitrary-
    precision bignum library (keeping the dependency footprint at zero,
    per GOAL.md's dependency policy) -- the honest cost is that this demo
    does not yet match Python's arbitrary-precision integers for very
    large values, tracked in docs/roadmap.md.

    [ExtrOCamlFloats]/[ExtrOCamlInt63] are the stock realizers for
    [PrimFloat.float] (used directly by [Lang.v]/[PyLang.v]'s float
    arithmetic) and [Uint63.int] (needed transitively: [Json.v]'s float
    JSON codec goes through [Prim2SF]/[SF2Prim], whose own definitions
    bit-twiddle a float via its underlying 63-bit integer representation).
    Both map to `coq-core`'s own kernel types (kernel/float64.ml,
    kernel/uint63.ml) rather than bare OCaml primitives -- the honest cost
    is that `ocaml/driver/`'s build now needs the `coq-core.kernel`
    ocamlfind library linked (see its dune file), not just the OCaml
    standard library. This doesn't violate GOAL.md's dependency policy,
    though: `coq-core` is already a required install on both machines
    (it's what runs `coqc`) -- this only means the already-present
    `coq-core` install needs to additionally be reachable as an OCaml
    *library* at the point `coq2py` itself is built, which per GOAL.md's
    own deployment split only ever happens on the dev machine (the remote
    host receives the prebuilt binary, never rebuilds it). A hand-written
    realizer mapping [PrimFloat.float] directly to OCaml's bare [float]
    was tried first and works for the four arithmetic ops alone, but
    [Prim2SF]/[SF2Prim] pull in enough further primitives
    ([frshiftexp]/[ldshiftexp]/[normfr_mantissa]/[of_uint63] and the
    [Uint63] bit operations they're built from) that hand-realizing all of
    them would mean re-deriving Coq's own float/bit-decomposition logic by
    hand -- strictly worse than taking the already-trusted stock pragma
    and its one honest linking cost. *)

(** [RealJson.v] (this project's new real-[coqc]-JSON ingestion parser,
    see that file's header) exposed a genuine performance problem in
    *existing* [Json.v]/[nat] extraction choices that its own small,
    hand-written test inputs never surfaced: parsing a real, 22KB
    [coqc]-extracted module took 45 seconds before the fixes below.
    Root-caused directly (not guessed), by a sequence of synthetic
    benchmarks isolating each cost in turn -- the four fixes below,
    cumulatively: 45s, then 28s, then 18s, then 15s, then *0.15s*:

    - [take_while]/[expect] ([Json.v]'s two generic "scan forward
      through a [string]" primitives, used by every parser in the
      pipeline) recurse via [String c rest]; [ExtrOcamlNativeString]
      realizes that pattern match by literally re-slicing the
      remaining native OCaml string on every character consumed,
      making one linear scan cost O(n^2).
    - Without [ExtrOcamlNatInt], [nat] extracts as its default unary
      Peano representation ([O]/[S n]), and every character classifier
      in [Json.v] ([is_digit]/[is_alnum]/[RealJson.v]'s own [is_ws])
      goes through [nat_of_ascii] plus a [Nat.leb] comparison against
      a literal bound (48, 57, 90, 122, ...) -- *constructing and
      structurally walking a ~100-long unary number for every single
      character of input*.
    - [parse_text_chars] ([Json.v]'s quoted-string body, after the
      leading quote) has the same [String c rest] recursion as
      [take_while], run once per quoted string -- plentiful in real
      extraction JSON (every object's ["what"]/["name"] key and
      value).
    - [parse_qtext] -- the actual entry point every quoted string goes
      through -- turned out to be the dominant cost of all four: its
      *own*, separate one-step [match s with String a s1 => ...]
      before ever reaching [parse_text_chars] peels the *entire
      remaining input* off as [s1] in one slow slice, every single
      time a quoted string starts, which is most of the time in real
      JSON (confirmed by a synthetic, object/string-heavy benchmark
      that stayed fast after the first three fixes and only dropped
      from 13s to under 0.1s once this one was added too).

    Each [Extract Constant] below replaces *only* the extracted OCaml
    body with an equivalent, O(n)-per-scan implementation (one
    index-walking loop, plain OCaml string slicing) -- the Coq-level
    definitions, and every proof about them ([Json.v]'s
    [take_while_app_stop], the [parse_print_roundtrip] theorem that
    depends on it, etc.), are untouched and remain exactly as proved;
    this is the same "trust extraction's realizer pragmas to compute
    the same function, the same way floats/Z/int63 already do" category
    of unverified-but-standard extraction step the rest of this file's
    comments already describe, not a new one. *)
Extract Constant take_while => "(fun p s ->
  let n = String.length s in
  let i = ref 0 in
  while !i < n && p s.[!i] do incr i done;
  (String.sub s 0 !i, String.sub s !i (n - !i)))".

Extract Constant expect => "(fun lit s ->
  let ll = String.length lit and ls = String.length s in
  if ll <= ls && String.sub s 0 ll = lit then Some (String.sub s ll (ls - ll)) else None)".

(** [parse_text_chars] (the body of every quoted-string literal,
    [Json.v]'s own [quote_char]/[backslash_char] escaping) has the same
    character-by-character [String c rest] recursion as [take_while]
    above, called once per quoted string in the input -- plentiful in
    real extraction JSON (every object's ["what"]/["name"] key and
    value). [Json.v] no longer threads a [fuel] parameter through this
    at all (it was a Coq-side termination device only, dropped once
    [parse_text_chars] was rewritten to recurse structurally on [s]
    itself -- see that file's own comment); the realizer below matches
    that signature and, as always, ignores Coq's own recursion
    structure and scans directly. *)
Extract Constant parse_text_chars => "(fun s ->
  let n = String.length s in
  let buf = Buffer.create 16 in
  let rec go i =
    if i >= n then None
    else
      let c = s.[i] in
      if c = '""' then Some (Buffer.contents buf, String.sub s (i + 1) (n - i - 1))
      else if c = '\\' then
        (if i + 1 >= n then None
         else (Buffer.add_char buf s.[i + 1]; go (i + 2)))
      else (Buffer.add_char buf c; go (i + 1))
  in go 0)".

(** [parse_qtext] -- the entry point every quoted string in the input
    actually goes through -- has its *own*, separate one-step
    [match s with String a s1 => ...] before ever reaching
    [parse_text_chars]: checking the leading quote by pattern-matching
    peels the *entire remaining input* off as [s1] in one slow slice,
    every single time a quoted string starts, which is most of the
    time in real JSON. This was the actual dominant cost all along:
    confirmed directly with a synthetic, 500-small-object benchmark
    (deliberately object/string-heavy, unlike the flat-number-array
    benchmark that stayed fast) -- 13s with every fix above already
    in place, under 0.1s with this one additionally. Realized as a
    single O(n) scan that checks the leading quote *and* walks the
    content in one pass, folding [parse_text_chars]'s own job in. *)
Extract Constant parse_qtext => "(fun s ->
  let n = String.length s in
  if n = 0 || s.[0] <> '""' then None
  else
    let buf = Buffer.create 16 in
    let rec go i =
      if i >= n then None
      else
        let c = s.[i] in
        if c = '""' then Some (Buffer.contents buf, String.sub s (i + 1) (n - i - 1))
        else if c = '\\' then
          (if i + 1 >= n then None
           else (Buffer.add_char buf s.[i + 1]; go (i + 2)))
        else (Buffer.add_char buf c; go (i + 1))
    in go 1)".

(** The deployment-host CLI (ocaml/driver/main.ml) needs to ingest a
    *real* [coqc]-extracted module, not just this project's own
    hand-rolled [Json.v] wire format -- see docs/roadmap.md's
    deployment entry. That means every [real_*_of_module_json]/
    [real_*_to_expr] entry point [RealIR.v]/[RealJson.v] actually
    proves needs to be reachable from the extracted binary, not just
    the two ([real_decl_of_module_json]/[real_fix_decl_of_module_json])
    this list used to name: a real multi-argument self-recursive
    [Fixpoint] or a real N-way mutually-recursive [Fixpoint ... with
    ...] group are both already-recognized, already-proven fragments
    (RealIR.v's [RSelfN]/[RCallN], [ERecGroup]) that the driver
    couldn't reach at all before this, since [Extraction]'s root list
    only extracts the transitive dependencies of what's named here --
    an otherwise-proven definition simply doesn't appear in the
    generated [.ml]/[.mli] if nothing in this list depends on it. *)
Extraction "coq2py_core.ml"
  expr pyexpr
  print_expr parse_expr_top
  translate
  py_function
  real_decl_of_module_json real_fix_decl_of_module_json
  real_fix_decl_multi_of_module_json real_fix_group_decl_of_module_json
  real_decl_to_expr real_fix_decl_to_expr
  real_fix_decl_multi_to_expr real_fix_group_decl_to_expr.
