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
    exactly right, unlike a decimal pretty-printer would have been. *)

From Coq Require Import String List ZArith.
From Coq Require Import Floats.PrimFloat Floats.FloatOps Floats.SpecFloat.
Import ListNotations.
Require Import PyLang.
Require Import Json. (* reuses z_to_string *)
Open Scope string_scope.

Definition bool_to_py (b : bool) : string := if b then "True" else "False".

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
