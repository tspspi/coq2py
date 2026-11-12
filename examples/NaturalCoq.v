(** NaturalCoq.v

    Closes the loop RealIR.v opens: genuine, human-style Coq
    [Definition]s -- the kind of thing chapter 2 of a book like
    *Certified Programming with Dependent Types* writes without a
    second thought -- carried all the way through to real, running
    Python, via [RealIR.v]'s [real_to_expr] and then this project's
    already-proven [Translate.v]/[Json.v]/[PyPrint.v] pipeline. Five
    examples: [clamp_nonneg] (Z/bool arithmetic and [if] -- plus,
    right after it, [clamp_nonneg_decl]: the same definition again but
    recognized as a *whole declaration*, via [RealIR.v]'s [real_decl],
    reading its parameter names off the real JSON's own [argnames]
    instead of supplying them by hand), [head_or_zero] (a real list
    pattern match), [swap_pair] (real pair construction/projection),
    [flip_point] (a real two-field [Record], recognized as a plain
    pair), [landed_natural] -- this project's own [landed_expr]
    (Kinematics.v), written the natural way with [&&] instead of
    built directly as [EAnd] -- and a sixth, [any_true]: a genuinely
    self-recursive [Fixpoint], recognized via [RealIR.v]'s [RSelf]/
    [real_fix_decl], the first real recursion this file reaches (the
    first five examples are all non-recursive).

    [clamp_nonneg] below is not invented for this file: it is exactly
    what was typed into a throwaway [.v] file and run through
    [coqc]/[Extraction Language JSON] during this session, to find out
    what Coq's own extraction backend really emits (see [RealIR.v]'s
    header for the two complications that experiment found). The
    captured JSON is reproduced in the comment above [clamp_nonneg_ir]
    below so the encoding can be checked by eye against the real
    output, not just trusted. *)

From Coq Require Import ZArith String List Bool Lia.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Require Import RealIR.
Open Scope Z_scope.
Open Scope string_scope.

(** The real, human-written Coq this example starts from: *)
Definition clamp_nonneg (a b : Z) : Z :=
  if Z.ltb a 0 then b else a.

(** What [coqc]/[Extraction Language JSON] (with no OCaml-targeting
    realizer loaded -- see RealIR.v's header) actually emitted for it,
    captured verbatim during this session:

    [[
    {
      "what": "decl:term", "name": "clamp_nonneg",
      "type": { ... Z -> Z -> Z ... },
      "value": {
        "what": "expr:lambda", "argnames": ["a", "b"],
        "body": {
          "what": "expr:case",
          "expr": {
            "what": "expr:apply",
            "func": { "what": "expr:global", "name": "ltb" },
            "args": [
              { "what": "expr:rel", "name": "a" },
              { "what": "expr:constructor", "name": "Z0", "args": [] }
            ]
          },
          "cases": [
            { "pat": {"name": "True", ...},  "body": {"what":"expr:rel","name":"b"} },
            { "pat": {"name": "False", ...}, "body": {"what":"expr:rel","name":"a"} }
          ]
        }
      }
    }
    ]]

    [clamp_nonneg_ir]'s shape below is that JSON tree, written as a
    [real_expr] term by hand (the textual-JSON-to-[real_expr] parser
    itself is the next step -- see docs/roadmap.md) -- an
    [expr:apply]/[expr:global "ltb"] over two [expr:rel]/[expr:
    constructor "Z0"] arguments becomes [RApp2 "ltb" (RRel "a") (RZLit
    0)], and the 2-case [expr:case] over [True]/[False] becomes
    [RIfBool] with the [True]-case's body first, matching the real
    JSON's case order exactly. *)
Definition clamp_nonneg_ir : real_expr :=
  RIfBool (RApp2 "ltb" (RRel "a") (RZLit 0)) (RRel "b") (RRel "a").

(** [real_eval] calls Coq's own [Z.ltb] directly (RealIR.v's header),
    so this is already a check against the real [clamp_nonneg]
    definition, not a hand reimplementation of it. *)
Example clamp_nonneg_ir_matches_real_definition :
  forall a b : Z,
    real_eval [("a", VZ a); ("b", VZ b)] clamp_nonneg_ir = Some (VZ (clamp_nonneg a b)).
Proof.
  intros a b. unfold clamp_nonneg_ir, clamp_nonneg. simpl.
  destruct (Z.ltb a 0); reflexivity.
Qed.

(** Translating into our existing, already-proven [expr] subset: *)
Definition clamp_nonneg_expr : expr :=
  match real_to_expr clamp_nonneg_ir with
  | Some e => e
  | None => EConst 0 (* unreachable: clamp_nonneg_ir is in the recognized fragment *)
  end.

Example clamp_nonneg_ir_translates :
  real_to_expr clamp_nonneg_ir = Some clamp_nonneg_expr.
Proof. reflexivity. Qed.

(** [RealIR.v]'s preservation theorem then carries the match with
    [Z.ltb]/[Z.add]/etc proved above all the way down to [eval]: *)
Example clamp_nonneg_expr_matches_real_definition :
  forall a b : Z,
    eval 10 [("a", VZ a); ("b", VZ b)] clamp_nonneg_expr = Some (VZ (clamp_nonneg a b)).
Proof.
  intros a b.
  rewrite (real_to_expr_preserves_semantics clamp_nonneg_ir clamp_nonneg_expr
             clamp_nonneg_ir_translates 10 [("a", VZ a); ("b", VZ b)] ltac:(simpl; lia)).
  apply clamp_nonneg_ir_matches_real_definition.
Qed.

Theorem clamp_nonneg_idents_valid :
  expr_idents_valid is_valid_ident clamp_nonneg_expr = true.
Proof. reflexivity. Qed.

Compute print_expr clamp_nonneg_expr.

Lemma string_app_nil_r : forall s : string, s ++ "" = s.
Proof.
  induction s as [| c s' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Corollary clamp_nonneg_json_roundtrip :
  parse_expr_top (print_expr clamp_nonneg_expr) = Some (clamp_nonneg_expr, "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip clamp_nonneg_expr clamp_nonneg_idents_valid
                (String.length (print_expr clamp_nonneg_expr) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_app_nil_r in H. exact H.
Qed.

Corollary clamp_nonneg_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate clamp_nonneg_expr)
      = option_map value_to_pyvalue (eval fuel rho clamp_nonneg_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The real, running Python -- from a human-written [Definition],
    through Coq's own extraction JSON shape (modeled, not yet parsed
    from text), through every already-proven stage this project has:
    [translate], [Json.v]'s codec, and [PyPrint.v]. *)
Compute py_function "clamp_nonneg" ["a"; "b"] (translate clamp_nonneg_expr).

(** Run for real:

    [[
    >>> clamp_nonneg(-5, 7)
    7
    >>> clamp_nonneg(5, 7)
    5
    ]]
*)

(** Everything above recognized only [clamp_nonneg]'s *body* -- the
    real captured JSON's outer [decl:term]/[expr:lambda] wrapper and
    its [argnames: ["a", "b"]] were supplied by hand at each call site
    above ([eval [("a", ...); ("b", ...)] ...], [py_function
    "clamp_nonneg" ["a"; "b"] ...]). [RealIR.v]'s [real_decl] now
    recognizes that outer wrapper too, so the same two argument names
    the real JSON actually carries drive both sides directly: *)
Definition clamp_nonneg_decl : real_decl := mk_real_decl ["a"; "b"] clamp_nonneg_ir.

Example clamp_nonneg_decl_matches_real_definition :
  forall a b : Z,
    real_decl_eval clamp_nonneg_decl [VZ a; VZ b] = Some (VZ (clamp_nonneg a b)).
Proof.
  intros a b. unfold real_decl_eval, clamp_nonneg_decl. simpl.
  apply clamp_nonneg_ir_matches_real_definition.
Qed.

Example clamp_nonneg_decl_translates :
  real_decl_to_expr clamp_nonneg_decl = Some clamp_nonneg_expr.
Proof. reflexivity. Qed.

Corollary clamp_nonneg_decl_translation_correct :
  forall a b : Z,
    eval 10 [("a", VZ a); ("b", VZ b)] clamp_nonneg_expr
      = real_decl_eval clamp_nonneg_decl [VZ a; VZ b].
Proof.
  intros a b.
  rewrite (real_decl_to_expr_preserves_semantics clamp_nonneg_decl clamp_nonneg_expr
             clamp_nonneg_decl_translates 10 [VZ a; VZ b] [("a", VZ a); ("b", VZ b)]
             ltac:(simpl; lia) eq_refl).
  reflexivity.
Qed.

(** The same generated Python as before -- now with [py_function]'s
    parameter list read straight off [clamp_nonneg_decl.(rd_argnames)]
    instead of retyped by hand. *)
Compute py_function "clamp_nonneg" clamp_nonneg_decl.(rd_argnames) (translate clamp_nonneg_expr).

(* ----------------------------------------------------------------- *)
(** * A second example: a real list pattern match *)

(** Another genuine, human-written Coq definition, also run through
    [coqc]/[Extraction Language JSON] during this session: *)
Definition head_or_zero (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: _ => x
  end.

(** What Coq's real extraction emitted for it, captured verbatim:

    [[
    {
      "what": "decl:term", "name": "head_or_zero",
      "type": { ... list z -> z ... },
      "value": {
        "what": "expr:lambda", "argnames": ["l"],
        "body": {
          "what": "expr:case",
          "expr": { "what": "expr:rel", "name": "l" },
          "cases": [
            { "pat": {"name": "Nil", "argnames": []},
              "body": {"what":"expr:constructor","name":"Z0","args":[]} },
            { "pat": {"name": "Cons", "argnames": ["x", "_"]},
              "body": {"what":"expr:rel","name":"x"} }
          ]
        }
      }
    }
    ]]

    -- an [expr:case] over [l] with [Nil]/[Cons] patterns (in that
    order, matching [RealIR.v]'s [RListMatch]'s [nilcase]-then-
    [conscase] argument order exactly), [RListMatch]'s own [hd]/[tl]
    binder names taken directly from the real [Cons] pattern's
    [argnames]. *)
Definition head_or_zero_ir : real_expr :=
  RListMatch (RRel "l") (RZLit 0) "x" "_" (RRel "x").

Example head_or_zero_ir_matches_real_definition :
  forall l : list Z,
    real_eval [("l", VList (map VZ l))] head_or_zero_ir = Some (VZ (head_or_zero l)).
Proof. intro l. destruct l as [| x xs]; reflexivity. Qed.

Definition head_or_zero_expr : expr :=
  match real_to_expr head_or_zero_ir with
  | Some e => e
  | None => EConst 0 (* unreachable: head_or_zero_ir is in the recognized fragment *)
  end.

Example head_or_zero_ir_translates :
  real_to_expr head_or_zero_ir = Some head_or_zero_expr.
Proof. reflexivity. Qed.

Example head_or_zero_expr_matches_real_definition :
  forall l : list Z,
    eval 10 [("l", VList (map VZ l))] head_or_zero_expr = Some (VZ (head_or_zero l)).
Proof.
  intro l.
  rewrite (real_to_expr_preserves_semantics head_or_zero_ir head_or_zero_expr
             head_or_zero_ir_translates 10 [("l", VList (map VZ l))] ltac:(simpl; lia)).
  apply head_or_zero_ir_matches_real_definition.
Qed.

Theorem head_or_zero_idents_valid :
  expr_idents_valid is_valid_ident head_or_zero_expr = true.
Proof. reflexivity. Qed.

Compute print_expr head_or_zero_expr.

Corollary head_or_zero_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate head_or_zero_expr)
      = option_map value_to_pyvalue (eval fuel rho head_or_zero_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** Lists render as nested Python tuples, the same as every other list
    example in this project (see PyPrint.v's comment on [PListMatch]). *)
Compute py_function "head_or_zero" ["l"] (translate head_or_zero_expr).

(** Run for real:

    [[
    >>> head_or_zero((3, (4, (5, ()))))
    3
    >>> head_or_zero(())
    0
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * A third example: real pair construction and projection *)

(** A third genuine, human-written Coq definition, also run through
    [coqc]/[Extraction Language JSON] during this session: *)
Definition swap_pair (p : Z * Z) : Z * Z := (snd p, fst p).

(** What Coq's real extraction emitted for it, captured verbatim:

    [[
    {
      "what": "decl:term", "name": "swap_pair",
      "type": { ... (z * z) -> (z * z) ... },
      "value": {
        "what": "expr:lambda", "argnames": ["p"],
        "body": {
          "what": "expr:constructor", "name": "Pair",
          "args": [
            { "what": "expr:apply",
              "func": {"what":"expr:global","name":"snd"},
              "args": [{"what":"expr:rel","name":"p"}] },
            { "what": "expr:apply",
              "func": {"what":"expr:global","name":"fst"},
              "args": [{"what":"expr:rel","name":"p"}] }
          ]
        }
      }
    }
    ]]

    -- pair construction is an [expr:constructor "Pair"] with 2 args
    ([RPair]'s own shape exactly), and [fst]/[snd] are plain unary
    [expr:apply]/[expr:global] calls, the same shape [negb] already
    had -- [RealIR.v]'s [RApp1] simply grew two more recognized names,
    not a new constructor. *)
Definition swap_pair_ir : real_expr :=
  RPair (RApp1 "snd" (RRel "p")) (RApp1 "fst" (RRel "p")).

Example swap_pair_ir_matches_real_definition :
  forall a b : Z,
    real_eval [("p", VPair (VZ a) (VZ b))] swap_pair_ir = Some (VPair (VZ b) (VZ a)).
Proof. reflexivity. Qed.

Definition swap_pair_expr : expr :=
  match real_to_expr swap_pair_ir with
  | Some e => e
  | None => EConst 0 (* unreachable: swap_pair_ir is in the recognized fragment *)
  end.

Example swap_pair_ir_translates :
  real_to_expr swap_pair_ir = Some swap_pair_expr.
Proof. reflexivity. Qed.

Example swap_pair_expr_matches_real_definition :
  forall a b : Z,
    eval 10 [("p", VPair (VZ a) (VZ b))] swap_pair_expr = Some (VPair (VZ b) (VZ a)).
Proof.
  intros a b.
  rewrite (real_to_expr_preserves_semantics swap_pair_ir swap_pair_expr
             swap_pair_ir_translates 10 [("p", VPair (VZ a) (VZ b))] ltac:(simpl; lia)).
  apply swap_pair_ir_matches_real_definition.
Qed.

Theorem swap_pair_idents_valid :
  expr_idents_valid is_valid_ident swap_pair_expr = true.
Proof. reflexivity. Qed.

Compute print_expr swap_pair_expr.

Corollary swap_pair_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate swap_pair_expr)
      = option_map value_to_pyvalue (eval fuel rho swap_pair_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

Compute py_function "swap_pair" ["p"] (translate swap_pair_expr).

(** Run for real:

    [[
    >>> swap_pair((3, 7))
    (7, 3)
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * A fourth example: a real two-field Record *)

(** A fourth genuine, human-written Coq definition, also run through
    [coqc]/[Extraction Language JSON] during this session: *)
Record point := mkpoint { px : Z; py : Z }.

Definition flip_point (p : point) : point := mkpoint (py p) (px p).

(** What Coq's real extraction emitted for it, captured verbatim
    (abbreviated -- [point]'s own [decl:ind] declares [Mkpoint] with 2
    [z] fields, unremarkable and omitted here):

    [[
    {
      "what": "decl:term", "name": "flip_point",
      "type": { ... point -> point ... },
      "value": {
        "what": "expr:lambda", "argnames": ["p"],
        "body": {
          "what": "expr:constructor", "name": "Mkpoint",
          "args": [
            { "what": "expr:case",
              "expr": {"what":"expr:rel","name":"p"},
              "cases": [
                { "pat": {"name":"Mkpoint","argnames":["_","py"]},
                  "body": {"what":"expr:rel","name":"py"} }
              ] },
            { "what": "expr:case",
              "expr": {"what":"expr:rel","name":"p"},
              "cases": [
                { "pat": {"name":"Mkpoint","argnames":["px","_"]},
                  "body": {"what":"expr:rel","name":"px"} }
              ] }
          ]
        }
      }
    }
    ]]

    -- a [Record]'s own constructor ([Mkpoint]) builds exactly like
    [pair] (a 2-arg [expr:constructor], [RPair]'s existing shape,
    regardless of the constructor's name), while each field *access*
    ([py p]/[px p]) is a 1-case [expr:case] on that same constructor
    binding one field to a real name and the other to ["_"] -- exactly
    [RProj2]/[RProj1]'s shape (see [RealIR.v]'s header for why a
    [Record] is treated as a plain product here, not given its own
    keyed representation). *)
Definition flip_point_ir : real_expr :=
  RPair (RProj2 (RRel "p")) (RProj1 (RRel "p")).

Example flip_point_ir_matches_real_definition :
  forall a b : Z,
    real_eval [("p", VPair (VZ a) (VZ b))] flip_point_ir = Some (VPair (VZ b) (VZ a)).
Proof. reflexivity. Qed.

Definition flip_point_expr : expr :=
  match real_to_expr flip_point_ir with
  | Some e => e
  | None => EConst 0 (* unreachable: flip_point_ir is in the recognized fragment *)
  end.

Example flip_point_ir_translates :
  real_to_expr flip_point_ir = Some flip_point_expr.
Proof. reflexivity. Qed.

Example flip_point_expr_matches_real_definition :
  forall a b : Z,
    eval 10 [("p", VPair (VZ a) (VZ b))] flip_point_expr = Some (VPair (VZ b) (VZ a)).
Proof.
  intros a b.
  rewrite (real_to_expr_preserves_semantics flip_point_ir flip_point_expr
             flip_point_ir_translates 10 [("p", VPair (VZ a) (VZ b))] ltac:(simpl; lia)).
  apply flip_point_ir_matches_real_definition.
Qed.

Theorem flip_point_idents_valid :
  expr_idents_valid is_valid_ident flip_point_expr = true.
Proof. reflexivity. Qed.

Compute print_expr flip_point_expr.

Corollary flip_point_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate flip_point_expr)
      = option_map value_to_pyvalue (eval fuel rho flip_point_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** Coq's [Record] becomes a plain Python tuple on the generated side,
    the same as a tuple [point] would have -- the field *names* were
    only ever a source-level convenience, not part of the runtime
    value, on either side of this pipeline. *)
Compute py_function "flip_point" ["p"] (translate flip_point_expr).

(** Run for real:

    [[
    >>> flip_point((3, 7))
    (7, 3)
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * A fifth example: the project's own physics, written naturally *)

(** A fifth genuine, human-written Coq definition -- this one not
    arbitrary, but the natural, source-level sibling of this project's
    own [landed_expr] (Kinematics.v Example 2: "has the projectile
    reached or passed ground level while still moving downward?"),
    written the way a human actually writes it ([&&], not [EAnd]):
    also run through [coqc]/[Extraction Language JSON] during this
    session. *)
Definition landed_natural (x v : Z) : bool :=
  andb (Z.leb x 0) (Z.ltb v 0).

(** What Coq's real extraction emitted for it, captured verbatim --
    and a genuine surprise, found by direct experiment, not assumed:
    [andb] does *not* extract as a named call the way [fst]/[negb] do.
    [andb]'s own definition is already exactly a 2-case boolean match
    ([match a with true => b | false => false end]), small enough that
    extraction inlines it on the spot, so [andb (Z.leb x 0) (Z.ltb v
    0)] shows up as an [expr:case] on [leb x 0] directly, not as an
    [expr:apply] of [expr:global "andb"]:

    [[
    {
      "what": "decl:term", "name": "landed_natural",
      "type": { ... z -> z -> bool ... },
      "value": {
        "what": "expr:lambda", "argnames": ["x", "v"],
        "body": {
          "what": "expr:case",
          "expr": {
            "what": "expr:apply",
            "func": {"what":"expr:global","name":"leb"},
            "args": [{"what":"expr:rel","name":"x"},
                     {"what":"expr:constructor","name":"Z0","args":[]}]
          },
          "cases": [
            { "pat": {"name":"True","argnames":[]},
              "body": {
                "what": "expr:apply",
                "func": {"what":"expr:global","name":"ltb"},
                "args": [{"what":"expr:rel","name":"v"},
                         {"what":"expr:constructor","name":"Z0","args":[]}]
              } },
            { "pat": {"name":"False","argnames":[]},
              "body": {"what":"expr:constructor","name":"False","args":[]} }
          ]
        }
      }
    }
    ]]

    -- so a recognizer that only looks for a named [andb]/[orb] call
    (as [RealIR.v]'s [RApp2] does) would never actually fire on [&&]/
    [||] written at the Coq source level; it only applies to a [bool]
    value already sitting in a variable. The *correctly* recognized
    shape for [andb c1 c2] is [RIfBool c1 c2 (RBoolLit false)] --
    exactly [andb]'s own definition, encoded directly: *)
Definition landed_natural_ir : real_expr :=
  RIfBool (RApp2 "leb" (RRel "x") (RZLit 0))
          (RApp2 "ltb" (RRel "v") (RZLit 0))
          (RBoolLit false).

Example landed_natural_ir_matches_real_definition :
  forall x v : Z,
    real_eval [("x", VZ x); ("v", VZ v)] landed_natural_ir
      = Some (VBool (landed_natural x v)).
Proof.
  intros x v. unfold landed_natural_ir, landed_natural. simpl.
  destruct (Z.leb x 0); destruct (Z.ltb v 0); reflexivity.
Qed.

Definition landed_natural_expr : expr :=
  match real_to_expr landed_natural_ir with
  | Some e => e
  | None => EConst 0 (* unreachable: landed_natural_ir is in the recognized fragment *)
  end.

Example landed_natural_ir_translates :
  real_to_expr landed_natural_ir = Some landed_natural_expr.
Proof. reflexivity. Qed.

Example landed_natural_expr_matches_real_definition :
  forall x v : Z,
    eval 10 [("x", VZ x); ("v", VZ v)] landed_natural_expr
      = Some (VBool (landed_natural x v)).
Proof.
  intros x v.
  rewrite (real_to_expr_preserves_semantics landed_natural_ir landed_natural_expr
             landed_natural_ir_translates 10 [("x", VZ x); ("v", VZ v)] ltac:(simpl; lia)).
  apply landed_natural_ir_matches_real_definition.
Qed.

Theorem landed_natural_idents_valid :
  expr_idents_valid is_valid_ident landed_natural_expr = true.
Proof. reflexivity. Qed.

Compute print_expr landed_natural_expr.

Corollary landed_natural_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate landed_natural_expr)
      = option_map value_to_pyvalue (eval fuel rho landed_natural_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python -- an [if]/[else] rather than a Python [and],
    tracking the real extracted shape exactly rather than the surface
    [andb] call; compare Kinematics.v's own [landed_expr], which (built
    directly as an [EAnd]) renders as a plain [and] instead -- two
    different routes to the same boolean, both proven correct against
    their own source. *)
Compute py_function "landed_natural" ["x"; "v"] (translate landed_natural_expr).

(** Run for real:

    [[
    >>> landed_natural(-1, -3)
    True
    >>> landed_natural(5, -3)
    False
    >>> landed_natural(-1, 3)
    False
    ]]
*)

(* ----------------------------------------------------------------- *)
(** * A sixth example: a real self-recursive Fixpoint *)

(** A sixth, genuinely recursive definition -- "does this list of
    booleans contain a [true] anywhere?" -- also run through [coqc]/
    [Extraction Language JSON] during this session. *)
Fixpoint any_true (l : list bool) : bool :=
  match l with
  | nil => false
  | b :: rest => orb b (any_true rest)
  end.

(** What Coq's real extraction emitted for it, captured verbatim: one
    [decl:fixgroup] wrapping a single [fixgroup:item] named
    ["any_true"], whose own [value] is the familiar [expr:lambda]/
    [argnames] wrapper. [orb]'s own definition inlines on the spot the
    same way [andb]'s already does (this file's fifth example), so the
    [Cons] case is a 2-case [expr:case] on [b], not a named [orb]
    call -- and the recursive call in its [False] branch is an
    ordinary [expr:apply] of [expr:global "any_true"], the function's
    *own* name, indistinguishable by shape alone from an unrelated
    named call (see RealIR.v's header on [RSelf] for why):

    [[
    { "what": "decl:fixgroup", "fixlist": [
      { "what": "fixgroup:item", "name": "any_true",
        "type": { ... list bool -> bool ... },
        "value": {
          "what": "expr:lambda", "argnames": ["l"],
          "body": {
            "what": "expr:case",
            "expr": {"what":"expr:rel","name":"l"},
            "cases": [
              { "pat": {"what":"pat:constructor","name":"Nil","argnames":[]},
                "body": {"what":"expr:constructor","name":"False","args":[]} },
              { "pat": {"what":"pat:constructor","name":"Cons","argnames":["b","rest"]},
                "body": {
                  "what": "expr:case",
                  "expr": {"what":"expr:rel","name":"b"},
                  "cases": [
                    { "pat": {"what":"pat:constructor","name":"True","argnames":[]},
                      "body": {"what":"expr:constructor","name":"True","args":[]} },
                    { "pat": {"what":"pat:constructor","name":"False","argnames":[]},
                      "body": {
                        "what": "expr:apply",
                        "func": {"what":"expr:global","name":"any_true"},
                        "args": [{"what":"expr:rel","name":"rest"}]
                      } }
                  ]
                } }
            ]
          }
        } } ] }
    ]]

    [any_true_ir] is that [fixgroup:item]'s body, written by hand: the
    outer [expr:case] on [l] becomes [RListMatch]; the inner one on
    [b], inlined [orb], becomes [RIfBool] exactly the way [andb]'s own
    inlining already does (the fifth example's [RIfBool c1 c2
    (RBoolLit false)] pattern, mirrored here as [RIfBool c1 (RBoolLit
    true) c2]); and the recursive [expr:apply]/[expr:global
    "any_true"] becomes [RSelf] -- it calls the fixgroup's own
    declared name, not an unrelated intrinsic. *)
Definition any_true_ir : real_expr :=
  RListMatch (RRel "l") (RBoolLit false) "b" "rest"
    (RIfBool (RRel "b") (RBoolLit true) (RSelf (RRel "rest"))).

Definition any_true_decl : real_fix_decl := mk_real_fix_decl "any_true" "l" any_true_ir.

Definition any_true_expr : expr :=
  match real_fix_decl_to_expr any_true_decl with
  | Some e => e
  | None => EConst 0 (* unreachable: any_true_decl is in the recognized fragment *)
  end.

Example any_true_decl_translates :
  real_fix_decl_to_expr any_true_decl = Some any_true_expr.
Proof. reflexivity. Qed.

Theorem any_true_idents_valid :
  expr_idents_valid is_valid_ident any_true_expr = true.
Proof. reflexivity. Qed.

(** Checked against the real [any_true] the same way Kinematics.v's
    own [ERec] example (Example 7, [fall_until_landed_concrete]) is:
    a concrete run, with fuel comfortably more than this particular
    list's length needs -- not a universally-quantified theorem, for
    the reason RealIR.v's header on [real_fix_decl] explains. *)
Example any_true_expr_matches_real_definition :
  eval 10 [] (EApp any_true_expr (ECons (EBool false) (ECons (EBool false) (ECons (EBool true) ENil))))
    = Some (VBool (any_true [false; false; true])).
Proof. reflexivity. Qed.

Compute print_expr (EApp any_true_expr (ECons (EBool false) (ECons (EBool false) (ECons (EBool true) ENil)))).

Corollary any_true_json_roundtrip :
  parse_expr_top (print_expr (EApp any_true_expr (ECons (EBool false) (ECons (EBool false) (ECons (EBool true) ENil)))))
    = Some (EApp any_true_expr (ECons (EBool false) (ECons (EBool false) (ECons (EBool true) ENil))), "").
Proof.
  unfold parse_expr_top.
  pose proof (parse_print_roundtrip
                (EApp any_true_expr (ECons (EBool false) (ECons (EBool false) (ECons (EBool true) ENil))))
                any_true_idents_valid
                (String.length (print_expr (EApp any_true_expr
                  (ECons (EBool false) (ECons (EBool false) (ECons (EBool true) ENil))))) + 1)
                ltac:(vm_compute; lia) "") as H.
  rewrite string_app_nil_r in H. exact H.
Qed.

Corollary any_true_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate any_true_expr)
      = option_map value_to_pyvalue (eval fuel rho any_true_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

(** The generated Python: the same walrus-self-reference recursive
    closure [fall_until_landed]'s own generated Python already uses
    (PyPrint.v's [PRec] comment), now reached from a real, captured
    [Fixpoint] instead of a hand-built [ERec] -- applied immediately to
    a fresh parameter [l], unlike [fall_until_landed] (which still
    needs ["a"]/["dt"] closed over *before* it can be called on a
    state), so this one is callable directly, in a single step. *)
Compute py_function "any_true" ["l"] (translate (EApp any_true_expr (EVar "l"))).

(** Run for real:

    [[
    >>> any_true((False, (False, (True, ()))))
    True
    ]]
*)
