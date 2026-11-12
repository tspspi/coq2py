(** NaturalCoq.v

    Closes the loop RealIR.v opens: genuine, human-style Coq
    [Definition]s -- the kind of thing chapter 2 of a book like
    *Certified Programming with Dependent Types* writes without a
    second thought -- carried all the way through to real, running
    Python, via [RealIR.v]'s [real_to_expr] and then this project's
    already-proven [Translate.v]/[Json.v]/[PyPrint.v] pipeline. Three
    examples: [clamp_nonneg] (Z/bool arithmetic and [if]),
    [head_or_zero] (a real list pattern match), and [swap_pair] (real
    pair construction/projection).

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
