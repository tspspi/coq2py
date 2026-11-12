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
Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZInt.
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

Extraction "coq2py_core.ml"
  expr pyexpr
  print_expr parse_expr_top
  translate
  py_function.
