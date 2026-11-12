(** PyPrint.v

    The final stage of the pipeline: rendering a [pyexpr] (PyLang.v) as
    actual Python source text. Per GOAL.md this is explicitly *not* part
    of the translator that requires proof -- it's structure-preserving
    text formatting, not a semantics-affecting transformation, so it sits
    outside the trust boundary the rest of this development cares about
    (the same way CompCert does not verify its final assembly printer).

    [pyexpr] has no notion of statements, so [PLet] -- which has no direct
    Python expression form -- is rendered with the walrus operator plus a
    2-tuple index, which is valid Python (3.8+) and evaluates with exactly
    the left-to-right, assign-then-use order [peval] gives [PLet]:
    [(x := e1), e2)[1]] assigns [x] and then evaluates/returns [e2]. It is
    not the prettiest Python a human would write, but it is correct, and
    "pretty" is exactly the kind of concern this file is allowed to not
    prove.

    Pairs render as real Python tuples ([(a, b)], [e[0]], [e[1]]), and
    booleans as Python's capitalized [True]/[False] literals.

    Floats render as [mantissa * (2.0 ** exponent)] (zero/inf/nan as
    [0.0]/[float("inf")]/[float("nan")]), reusing the same
    [Prim2SF]/[spec_float] decomposition [Json.v] already uses for the
    wire format -- not because it's pretty, but because it's *exact*:
    [mantissa] fits within a double's 53-bit precision and [2.0**exponent]
    is an exactly-representable power of two (for any exponent
    [Prim2SF] actually produces), so Python recomputes the precise
    original bit pattern with no decimal-rounding algorithm needed here
    (that's the hard problem [Json.v]'s codec comment explains avoiding).
    This is unverified text formatting like the rest of this file, not a
    new proof obligation -- but it's worth noting it was easy to get
    exactly right, unlike a decimal pretty-printer would have been.

    [PRepeat] -- bounded iteration -- is rendered by literally unrolling
    the loop [n] times at print time (valid since [n] is a compile-time
    [nat], not a runtime value): a tuple of [n+1] walrus assignments to
    [x] (the first seeded from [init], each later one re-reading and
    overwriting [x] with [body]'s value) followed by a bare [x], indexed
    with [-1] to take the last one. For [n = 0] this degenerates to just
    binding and returning [init], matching [piterate 0 f v = Some v]. No
    Python [for]/[while] statement is used -- [pyexpr] still has no
    statement forms -- so this stays a single expression like everything
    else in this file.

    [PDiv]/[PMod] render as Python's [//]/[%] directly -- correct, not
    just structure-preserving, for every operand (including negative
    ones): Python's [//]/[%] are floor division/modulo, the exact same
    convention Coq's [Z.div]/[Z.modulo] use (confirmed empirically: e.g.
    both give [(-7) `div` 2 = -4, -7 `mod` 2 = 1]), unlike OCaml's native
    [/]/[mod], which truncate toward zero instead -- precisely why
    [ExtrOcamlZInt] (Extract.v) declines to give [Z.div]/[Z.modulo] a
    native-[int] realizer. Zero divisors need no special-casing in the
    printer either: [Lang.v]'s [eval] already gets stuck on a zero
    divisor (see its comment), and Python's [//]/[%] *already* raise
    [ZeroDivisionError] for one -- the two "undefined" cases line up on
    their own.

    [PLam]/[PApp] render as an ordinary Python [lambda]/call -- real
    first-class functions on the Python side too, no encoding needed.
    [PRec] (a named recursive function) is the one case needing a trick,
    since Python's [lambda] has no way to refer to itself by name: it
    reuses the exact same walrus assignment [PLet] already does,
    [(f := (lambda param: BODY)), f)[1]], which works for recursion
    specifically *because* Python resolves a free variable inside a
    [lambda]'s body against its enclosing scope at *call* time, not at
    the [lambda]'s creation time -- so by the time [f] is actually
    invoked (always after the assignment that created it has run), [f]
    inside [BODY] already refers to the very closure being called. No
    textual substitution of [f] for anything else is needed anywhere in
    [BODY] (confirmed by actually running a generated recursive
    [factorial] this way, not just reasoned about).

    [PNil]/[PCons] render as Python tuples, matching the choice already
    made for pairs: [()] is [Nil], and [(hd, tl)] is [Cons hd tl] --
    structurally the exact same shape as our own cons-list [value]s, not
    Python's native (mutable, random-access) [list]. [PListMatch] checks
    [scrutinee == ()] for the empty case and indexes [[0]]/[[1]] for the
    non-empty one, printing [scrutinee] three times over; since this
    subset is purely functional (nothing to evaluate it for side effects
    would even mean), re-evaluating it those extra times changes no
    answer, only (unverified, acceptable here) generated-code size. *)

From Coq Require Import String List ZArith.
From Coq Require Import Floats.PrimFloat Floats.FloatOps Floats.SpecFloat.
Import ListNotations.
Require Import Lang. (* reuses var *)
Require Import PyLang.
Require Import Json. (* reuses z_to_string *)
Open Scope string_scope.

Definition bool_to_py (b : bool) : string := if b then "True" else "False".

(** Field/key names are restricted to [is_valid_ident] (alnum/underscore,
    nonempty -- see [Lang.expr_idents_valid]), so a plain wrap in double
    quotes is always a valid, unambiguous Python string literal; no
    escaping logic is needed. *)
Definition py_qstring (x : var) : string := """" ++ x ++ """".

Definition float_to_py (f : float) : string :=
  match Prim2SF f with
  | S754_zero false => "0.0"
  | S754_zero true => "-0.0"
  | S754_infinity false => "float(""inf"")"
  | S754_infinity true => "float(""-inf"")"
  | S754_nan => "float(""nan"")"
  | S754_finite false m e =>
      "(" ++ z_to_string (Zpos m) ++ " * (2.0 ** " ++ z_to_string e ++ "))"
  | S754_finite true m e =>
      "(-" ++ z_to_string (Zpos m) ++ " * (2.0 ** " ++ z_to_string e ++ "))"
  end.

(** [n] repetitions of [", (x := body_str)"], one per remaining
    iteration -- see [py_expr]'s [PRepeat] case. *)
Fixpoint py_repeat_steps (n : nat) (x : var) (body_str : string) : string :=
  match n with
  | O => ""
  | S n' => ", (" ++ x ++ " := " ++ body_str ++ ")" ++ py_repeat_steps n' x body_str
  end.

Fixpoint py_expr (e : pyexpr) : string :=
  match e with
  | PConst z => z_to_string z
  | PBool b => bool_to_py b
  | PVar x => x
  | PAdd e1 e2 => "(" ++ py_expr e1 ++ " + " ++ py_expr e2 ++ ")"
  | PSub e1 e2 => "(" ++ py_expr e1 ++ " - " ++ py_expr e2 ++ ")"
  | PMul e1 e2 => "(" ++ py_expr e1 ++ " * " ++ py_expr e2 ++ ")"
  | PEq e1 e2 => "(" ++ py_expr e1 ++ " == " ++ py_expr e2 ++ ")"
  | PLt e1 e2 => "(" ++ py_expr e1 ++ " < " ++ py_expr e2 ++ ")"
  | PLe e1 e2 => "(" ++ py_expr e1 ++ " <= " ++ py_expr e2 ++ ")"
  | PAnd e1 e2 => "(" ++ py_expr e1 ++ " and " ++ py_expr e2 ++ ")"
  | POr e1 e2 => "(" ++ py_expr e1 ++ " or " ++ py_expr e2 ++ ")"
  | PNot e1 => "(not " ++ py_expr e1 ++ ")"
  | PIf c e1 e2 =>
      "(" ++ py_expr e1 ++ " if " ++ py_expr c ++ " else " ++ py_expr e2 ++ ")"
  | PPair e1 e2 => "(" ++ py_expr e1 ++ ", " ++ py_expr e2 ++ ")"
  | PFst e1 => "(" ++ py_expr e1 ++ ")[0]"
  | PSnd e1 => "(" ++ py_expr e1 ++ ")[1]"
  | PLet x e1 e2 =>
      "((" ++ x ++ " := " ++ py_expr e1 ++ "), " ++ py_expr e2 ++ ")[1]"
  | PFConst f => float_to_py f
  | PFAdd e1 e2 => "(" ++ py_expr e1 ++ " + " ++ py_expr e2 ++ ")"
  | PFSub e1 e2 => "(" ++ py_expr e1 ++ " - " ++ py_expr e2 ++ ")"
  | PFMul e1 e2 => "(" ++ py_expr e1 ++ " * " ++ py_expr e2 ++ ")"
  | PFDiv e1 e2 => "(" ++ py_expr e1 ++ " / " ++ py_expr e2 ++ ")"
  | PFEq e1 e2 => "(" ++ py_expr e1 ++ " == " ++ py_expr e2 ++ ")"
  | PFLt e1 e2 => "(" ++ py_expr e1 ++ " < " ++ py_expr e2 ++ ")"
  | PFLe e1 e2 => "(" ++ py_expr e1 ++ " <= " ++ py_expr e2 ++ ")"
  | PRepeat n x body init =>
      "((" ++ x ++ " := " ++ py_expr init ++ ")"
        ++ py_repeat_steps n x (py_expr body) ++ ", " ++ x ++ ")[-1]"
  | PDiv e1 e2 => "(" ++ py_expr e1 ++ " // " ++ py_expr e2 ++ ")"
  | PMod e1 e2 => "(" ++ py_expr e1 ++ " % " ++ py_expr e2 ++ ")"
  | PLam param body => "(lambda " ++ param ++ ": " ++ py_expr body ++ ")"
  | PRec f param body =>
      "((" ++ f ++ " := (lambda " ++ param ++ ": " ++ py_expr body ++ ")), " ++ f ++ ")[-1]"
  | PApp func arg => "(" ++ py_expr func ++ "(" ++ py_expr arg ++ "))"
  | PNil => "()"
  | PCons hd tl => "(" ++ py_expr hd ++ ", " ++ py_expr tl ++ ")"
  | PListMatch scrutinee nilcase hd tl conscase =>
      "(" ++ py_expr nilcase ++ " if (" ++ py_expr scrutinee ++ ") == () else "
        ++ "((" ++ hd ++ " := (" ++ py_expr scrutinee ++ ")[0]), ("
        ++ tl ++ " := (" ++ py_expr scrutinee ++ ")[1]), " ++ py_expr conscase ++ ")[-1])"
  | PRecord k1 e1 k2 e2 =>
      "{" ++ py_qstring k1 ++ ": " ++ py_expr e1 ++ ", "
        ++ py_qstring k2 ++ ": " ++ py_expr e2 ++ "}"
  | PField name e1 => "(" ++ py_expr e1 ++ ")[" ++ py_qstring name ++ "]"
  end.

Fixpoint join_comma (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ ", " ++ join_comma rest
  end.

Definition newline : string := String (Ascii.ascii_of_nat 10) EmptyString.

(** Wrap a translated [pyexpr] as a complete, standalone Python function
    definition. *)
Definition py_function (name : string) (params : list string) (body : pyexpr) : string :=
  "def " ++ name ++ "(" ++ join_comma params ++ "):" ++ newline
    ++ "    return " ++ py_expr body ++ newline.
