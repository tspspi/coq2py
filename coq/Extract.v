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

Extraction Language OCaml.

(** Native-OCaml realizers for bool/option/list/pair, strings, and Z --
    all standard, Coq-shipped pragmas used by essentially every real-world
    Coq extraction, not anything bespoke to this project. [ExtrOcamlZInt]
    maps [Z] to OCaml's native fixed-width [int] rather than an arbitrary-
    precision bignum library (keeping the dependency footprint at zero,
    per GOAL.md's dependency policy) -- the honest cost is that this demo
    does not yet match Python's arbitrary-precision integers for very
    large values, tracked in docs/roadmap.md. *)

Extraction "coq2py_core.ml"
  expr pyexpr
  print_expr parse_expr_top
  translate
  py_function.
