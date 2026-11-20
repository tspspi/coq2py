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

    A real bug this design used to have, found by inspection and
    confirmed by actually running the generated code: a walrus
    assignment writes into the *one shared* enclosing Python scope, not
    a fresh block scope, while [peval] models a closure as capturing an
    *immutable snapshot* of its environment. If two sibling bindings
    (anywhere: [PLet], [PListMatch]'s [hd]/[tl], [PCase]'s arms, ...) in
    the same scope reused the same source name, and a closure created
    under the first escaped past the point where the second rebound
    that name, the escaped closure would (under real Python's
    late-binding closure rule) read back the *second* binding's value,
    not the first -- exactly the class of "printing silently changes
    what the program computes" bug [docs/duality.md] says this project
    does not accept for a Coq-to-Python step. [PyRename.rename_pyexpr]
    fixes this the standard way: every binder is alpha-renamed to a
    fresh, globally-unique name before any printing happens, so no two
    distinct bindings in one generated function body ever share a
    Python identifier, and no walrus write can ever land on a slot a
    still-live closure depends on under a different meaning. [py_function]
    below applies it; nothing in this file's own printing logic changed.

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
    answer, only (unverified, acceptable here) generated-code size.

    [PRecordN]/[PFieldN] (genuinely-N-ary records, see Lang.v) render
    the same way the fixed-arity [PRecord]/[PField] already do -- a
    [dict] literal keyed by field name, looked up by name -- just built
    from a nested anonymous [fix] walking the field list instead of a
    fixed two-field literal.

    [PRecGroup] (genuinely-N-way mutual recursion, see Lang.v) renders
    as [PRecMut]'s own walrus-self-reference trick, generalized from a
    fixed pair to a list: one [(name := (lambda param: body)), ] per
    member, ending in a [dict] -- [PRecordN]'s own encoding, not a new
    one, since a group's *value* genuinely is a [VRecordN] of
    closures (Lang.v's [ERecGroup] comment) -- so an individual member
    is called by reading it back out of that [dict] with the *same*
    [PFieldN] a [PRecordN] field already uses, not a new accessor.
    Python resolves each member's free reference to a sibling against
    the enclosing scope at *call* time, the same reason [PRec]'s/
    [PRecMut]'s own single/double self-reference already works. *)

From Coq Require Import String List ZArith Ascii.
From Coq Require Import Floats.PrimFloat Floats.FloatOps Floats.SpecFloat.
Import ListNotations.
Require Import Lang. (* reuses var *)
Require Import PyLang.
Require Import Json. (* reuses z_to_string *)
Require Import PyRename. (* the alpha-renaming pass fixing the walrus/
  closure-capture hazard described below *)
Open Scope string_scope.

Definition bool_to_py (b : bool) : string := if b then "True" else "False".

(** Field/key names are restricted to [is_valid_ident] (alnum/underscore,
    nonempty -- see [Lang.expr_idents_valid]), so a plain wrap in double
    quotes is always a valid, unambiguous Python string literal; no
    escaping logic is needed. *)
Definition py_qstring (x : var) : string := """" ++ x ++ """".

(** [py_qstring] is literally [Json.v]'s own [quote_string] (same
    quote-wrapping, no escaping needed since [is_valid_ident]-
    restricted names can't contain one) -- so it inherits [quote_
    string]/[parse_qstring]'s already-proven [parse_qstring_print]
    round trip for free, the same move [py_text_qstring_parses_back]
    below makes for the escaped case. Covers every [py_qstring] call
    site: record/[RecordN] field keys and a [PRecGroup] member's own
    (never-renamed) name, every one of which is already required to
    satisfy [is_valid_ident] elsewhere in this pipeline
    ([expr_idents_valid]). *)
Lemma py_qstring_is_quote_string : forall x, py_qstring x = quote_string x.
Proof. intro x. reflexivity. Qed.

Theorem py_qstring_parses_back : forall x, is_valid_ident x = true ->
  forall rest, parse_qstring (py_qstring x ++ rest) = Some (x, rest).
Proof.
  intros x Hvalid rest. rewrite py_qstring_is_quote_string. apply parse_qstring_print, Hvalid.
Qed.

(** [EStrConst]'s own payload (see Lang.v's header) is *not* restricted
    to [is_valid_ident] -- any string, including one containing a
    literal double-quote or backslash character, is a valid literal --
    so rendering it needs real escaping, the same two characters
    [Json.v]'s [escape_text] escapes for the same structural reason
    (Python's own double-quoted string syntax needs exactly those two
    escaped, nothing else, to stay unambiguous). *)
Fixpoint py_escape_text (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c quote_char then String backslash_char (String c (py_escape_text rest))
      else if Ascii.eqb c backslash_char then String backslash_char (String backslash_char (py_escape_text rest))
      else String c (py_escape_text rest)
  end.

Definition py_text_qstring (x : var) : string := """" ++ py_escape_text x ++ """".

(** [py_escape_text]'s own comment above already claims it "mirrors"
    [Json.v]'s [escape_text] -- true literally, not just in spirit:
    same two characters, same escaping, same fallback case, just
    written once more by hand. Proved here so [py_text_qstring]
    inherits [escape_text]/[quote_text]'s own already-proven
    [parse_qtext_print] round trip for free, instead of that claim
    staying an unverified comment: this is genuine new verification
    for [PyPrint.v] (a real correctness property -- the Python string
    literal rendered for an arbitrary [EStrConst] payload, including
    one containing a literal quote or backslash, is unambiguous and
    reconstructs the exact original string -- not just structure-
    preserving text formatting), reusing already-proven machinery
    rather than opening new attack surface with a second, independent
    escaping proof. *)
Lemma py_escape_text_is_escape_text : forall s, py_escape_text s = escape_text s.
Proof.
  induction s as [| c s' IH]; simpl.
  - reflexivity.
  - destruct (Ascii.eqb c quote_char) eqn:Hq.
    + apply Ascii.eqb_eq in Hq. subst. rewrite IH. reflexivity.
    + destruct (Ascii.eqb c backslash_char) eqn:Hb; rewrite IH; reflexivity.
Qed.

Lemma py_text_qstring_is_quote_text : forall x, py_text_qstring x = quote_text x.
Proof.
  intro x. unfold py_text_qstring, quote_text.
  rewrite py_escape_text_is_escape_text.
  reflexivity.
Qed.

Theorem py_text_qstring_parses_back : forall x rest,
  parse_qtext (py_text_qstring x ++ rest) = Some (x, rest).
Proof.
  intros x rest. rewrite py_text_qstring_is_quote_text. apply parse_qtext_print.
Qed.

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
  | PFOpp e1 => "(-" ++ py_expr e1 ++ ")"
  | PRepeat n x body init =>
      "((" ++ x ++ " := " ++ py_expr init ++ ")"
        ++ py_repeat_steps n x (py_expr body) ++ ", " ++ x ++ ")[-1]"
  | PDiv e1 e2 => "(" ++ py_expr e1 ++ " // " ++ py_expr e2 ++ ")"
  | PMod e1 e2 => "(" ++ py_expr e1 ++ " % " ++ py_expr e2 ++ ")"
  | PLam param body => "(lambda " ++ param ++ ": " ++ py_expr body ++ ")"
  | PRec f param body =>
      "((" ++ f ++ " := (lambda " ++ param ++ ": " ++ py_expr body ++ ")), " ++ f ++ ")[-1]"
  | PRecMut f1 param1 body1 f2 param2 body2 =>
      "((" ++ f1 ++ " := (lambda " ++ param1 ++ ": " ++ py_expr body1 ++ ")), ("
        ++ f2 ++ " := (lambda " ++ param2 ++ ": " ++ py_expr body2 ++ ")), ("
        ++ f1 ++ ", " ++ f2 ++ "))[-1]"
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
  | PInl e1 => "(""inl"", " ++ py_expr e1 ++ ")"
  | PInr e1 => "(""inr"", " ++ py_expr e1 ++ ")"
  | PCase scrutinee x1 case1 x2 case2 =>
      "(((" ++ x1 ++ " := (" ++ py_expr scrutinee ++ ")[1]), " ++ py_expr case1 ++ ")[-1] if ("
        ++ py_expr scrutinee ++ ")[0] == ""inl"" else ((" ++ x2 ++ " := ("
        ++ py_expr scrutinee ++ ")[1]), " ++ py_expr case2 ++ ")[-1])"
  | PStrConst s => py_text_qstring s
  | PStrConcat e1 e2 => "(" ++ py_expr e1 ++ " + " ++ py_expr e2 ++ ")"
  | PStrEq e1 e2 => "(" ++ py_expr e1 ++ " == " ++ py_expr e2 ++ ")"
  | PRecordN fields =>
      "{" ++
      (fix py_fields (fs : list (var * pyexpr)) : string :=
         match fs with
         | [] => ""
         | [(k, fe)] => py_qstring k ++ ": " ++ py_expr fe
         | (k, fe) :: rest => py_qstring k ++ ": " ++ py_expr fe ++ ", " ++ py_fields rest
         end) fields
      ++ "}"
  | PFieldN name e1 => "(" ++ py_expr e1 ++ ")[" ++ py_qstring name ++ "]"
  | PRecGroup fns =>
      "(" ++
      (fix py_group_assigns (fs : list (var * var * pyexpr)) : string :=
         match fs with
         | [] => ""
         | (f, p, b) :: rest =>
             "(" ++ f ++ " := (lambda " ++ p ++ ": " ++ py_expr b ++ ")), " ++ py_group_assigns rest
         end) fns
      ++ "{" ++
      (fix py_group_dict (fs : list (var * var * pyexpr)) : string :=
         match fs with
         | [] => ""
         | [(f, p, b)] => py_qstring f ++ ": " ++ f
         | (f, p, b) :: rest => py_qstring f ++ ": " ++ f ++ ", " ++ py_group_dict rest
         end) fns
      ++ "})[-1]"
  end.

Fixpoint join_comma (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ ", " ++ join_comma rest
  end.

(** Python's reserved words ([keyword.kwlist] on a real Python 3
    interpreter -- soft keywords like [match]/[case]/[_], which *can*
    still be used as ordinary identifiers, are deliberately excluded,
    confirmed directly: [def match(): return 1] is valid Python).
    [rename_function] below already protects every parameter and bound
    variable from ever colliding with one of these -- every renamed name
    has the shape ["v" ++ digits], never a bare reserved word -- but the
    function's own *name*, unlike a parameter, is never renamed, and is
    directly reachable from a real Coq [Definition]'s own name once
    [RealIR.v]'s ingestion pipeline feeds it through (a hypothetical
    [Definition lambda := ...] is perfectly legal Coq; every example in
    this repository today happens to avoid this, but nothing enforced
    that). [safe_py_name] closes the gap: if [name] is one of these
    words, suffix it with [_] (never itself one of these words either --
    proved below, by direct, decidable case analysis over this fixed,
    finite list, not assumed), otherwise leave it untouched. This is a
    real, narrow piece of *verification* in this file -- unlike the
    rest of [PyPrint.v]'s deliberately-unproved text formatting (this
    file's own header), "the generated function name is never a Python
    keyword" is a genuine, checkable correctness property with its own
    proof, not just structure-preserving output. *)
Definition py_keywords : list string :=
  ["False"; "None"; "True"; "and"; "as"; "assert"; "async"; "await";
   "break"; "class"; "continue"; "def"; "del"; "elif"; "else"; "except";
   "finally"; "for"; "from"; "global"; "if"; "import"; "in"; "is";
   "lambda"; "nonlocal"; "not"; "or"; "pass"; "raise"; "return"; "try";
   "while"; "with"; "yield"].

Definition is_py_keyword (s : string) : bool :=
  if in_dec string_dec s py_keywords then true else false.

Definition safe_py_name (s : string) : string :=
  if is_py_keyword s then s ++ "_" else s.

Lemma safe_py_name_not_keyword : forall s, is_py_keyword (safe_py_name s) = false.
Proof.
  intro s. unfold safe_py_name.
  destruct (is_py_keyword s) eqn:Hk; [| exact Hk].
  assert (Hcheck : forallb (fun w => negb (is_py_keyword (w ++ "_"))) py_keywords = true)
    by (vm_compute; reflexivity).
  unfold is_py_keyword in Hk.
  destruct (in_dec string_dec s py_keywords) as [Hin | Hnin]; [| discriminate].
  pose proof (forallb_forall (fun w => negb (is_py_keyword (w ++ "_"))) py_keywords) as [Hf _].
  specialize (Hf Hcheck s Hin).
  destruct (is_py_keyword (s ++ "_")); [discriminate | reflexivity].
Qed.

(** [safe_py_name_not_keyword] only covers the one identifier that is
    never renamed (the function's own name) -- every *other*
    identifier [PyPrint.v] ever emits comes from [PyRename.fresh_name]
    (["v" ++ digits]) instead, and was only ever *claimed*, never
    proved, to avoid [py_keywords] too (this file's own header, and
    [PyRename.v]'s). [fresh_name_not_keyword] below closes that gap
    for real: no word in [py_keywords] starts with ['v'] (a direct,
    decidable check over the fixed, finite list, same style as
    [safe_py_name_not_keyword]), and [fresh_name] always does, so it
    can never equal one. [fresh_name_is_py_identifier] goes further,
    confirming the *syntactic* shape Python's own grammar requires (a
    letter, then any run of letters/digits/underscores) rather than
    just asserting it from the "v" ++ digits description in prose. *)
Definition starts_with_v (s : string) : bool :=
  match s with
  | String c _ => Ascii.eqb c "v"%char
  | EmptyString => false
  end.

Lemma py_keywords_not_v_prefixed :
  forallb (fun k => negb (starts_with_v k)) py_keywords = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fresh_name_not_keyword : forall n, is_py_keyword (PyRename.fresh_name n) = false.
Proof.
  intro n.
  assert (Hv : starts_with_v (PyRename.fresh_name n) = true)
    by (unfold PyRename.fresh_name; reflexivity).
  unfold is_py_keyword.
  destruct (in_dec string_dec (PyRename.fresh_name n) py_keywords) as [Hin | Hnin];
    [| reflexivity].
  exfalso.
  pose proof (forallb_forall (fun k => negb (starts_with_v k)) py_keywords) as [Hf _].
  specialize (Hf py_keywords_not_v_prefixed (PyRename.fresh_name n) Hin).
  rewrite Hv in Hf. simpl in Hf. discriminate.
Qed.

Lemma fresh_name_is_py_identifier : forall n,
  exists t, PyRename.fresh_name n = String "v"%char t /\ string_forallb is_digit t = true.
Proof.
  intro n. unfold PyRename.fresh_name.
  eexists. split; [reflexivity |].
  apply nat_to_string_all_digits.
Qed.

Definition newline : string := String (Ascii.ascii_of_nat 10) EmptyString.

(** Alpha-rename every parameter and bound variable in [body] (and the
    [params] themselves) to a fresh, globally-unique name before any
    printing happens -- see this file's header. [n0] is an arbitrary
    starting seed (there is only one top-level call per generated
    function, so any value works; [0] keeps it simple). *)
Definition rename_function (params : list string) (body : pyexpr) : list string * pyexpr :=
  let '(env0, n0) :=
    (fix mk (ps : list string) (n : nat) : list (var * var) * nat :=
       match ps with
       | [] => ([], n)
       | p :: rest =>
           let y := fresh_name n in
           let '(restenv, n') := mk rest (S n) in
           ((p, y) :: restenv, n')
       end) params 0%nat
  in
  let '(body', _) := rename_pyexpr env0 n0 body in
  (map snd env0, body').

(** Wrap a translated [pyexpr] as a complete, standalone Python function
    definition. *)
Definition py_function (name : string) (params : list string) (body : pyexpr) : string :=
  let '(params', body') := rename_function params body in
  "def " ++ safe_py_name name ++ "(" ++ join_comma params' ++ "):" ++ newline
    ++ "    return " ++ py_expr body' ++ newline.
