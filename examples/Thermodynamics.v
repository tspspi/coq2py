(** Thermodynamics.v

    A second running-example domain for coq2py, alongside
    Kinematics.v's motion examples: classifying the phase of a
    substance from its temperature -- a first-principles
    thermodynamics check (solid below the melting point, liquid
    between the melting and boiling points, gas above), expressed
    entirely in the already-proven [expr] subset. No new Gallina
    feature is introduced here; the point of this file is breadth of
    *domain*, not of language -- the same [EIf]/comparisons/[EStrConst]
    this project already proves correct, applied outside kinematics.

    Temperatures are plain [Z] (whole-degree Celsius), the same
    "integers standing in for a continuous quantity" choice
    Kinematics.v's Examples 1/2 make for position/velocity -- exact
    enough to demonstrate the control-flow shape, not a claim that
    temperature should be integer-valued in general. *)

From Coq Require Import ZArith String List Bool Lia.
Import ListNotations.
Require Import Lang.
Require Import PyLang.
Require Import Translate.
Require Import Json.
Require Import PyPrint.
Open Scope Z_scope.
Open Scope string_scope.

Lemma string_app_nil_r : forall s : string, s ++ "" = s.
Proof.
  induction s as [| c s' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Ltac json_roundtrip_corollary e Hvalid :=
  unfold parse_expr_top;
  let H := fresh "H" in
  pose proof (parse_print_roundtrip e Hvalid
                (String.length (print_expr e) + 1)
                ltac:(vm_compute; lia) "") as H;
  rewrite string_app_nil_r in H;
  exact H.

(* ----------------------------------------------------------------- *)
(** * Example 1: classifying the phase of water by temperature *)

(** Water freezes at 0 deg C and boils at 100 deg C (at standard
    pressure -- this is deliberately the simplest possible version of
    the check, not a full phase diagram): solid at or below freezing,
    gas at or above boiling, liquid in between. *)
Definition water_phase_expr : expr :=
  EIf (ELe (EVar "tC") (EConst 0))
      (EStrConst "solid")
      (EIf (ELt (EVar "tC") (EConst 100))
           (EStrConst "liquid")
           (EStrConst "gas")).

Theorem water_phase_idents_valid :
  expr_idents_valid is_valid_ident water_phase_expr = true.
Proof. reflexivity. Qed.

(** The three phases, plus both boundaries (freezing counts as solid;
    boiling counts as gas, matching the [ELe]/[ELt] asymmetry above). *)
Example water_phase_solid :
  eval 10 [("tC", VZ (-5))] water_phase_expr = Some (VStr "solid").
Proof. reflexivity. Qed.

Example water_phase_freezing_point :
  eval 10 [("tC", VZ 0)] water_phase_expr = Some (VStr "solid").
Proof. reflexivity. Qed.

Example water_phase_liquid :
  eval 10 [("tC", VZ 50)] water_phase_expr = Some (VStr "liquid").
Proof. reflexivity. Qed.

Example water_phase_boiling_point :
  eval 10 [("tC", VZ 100)] water_phase_expr = Some (VStr "gas").
Proof. reflexivity. Qed.

Example water_phase_gas :
  eval 10 [("tC", VZ 150)] water_phase_expr = Some (VStr "gas").
Proof. reflexivity. Qed.

Compute print_expr water_phase_expr.
Compute parse_expr_top (print_expr water_phase_expr).

Corollary water_phase_json_roundtrip :
  parse_expr_top (print_expr water_phase_expr) = Some (water_phase_expr, "").
Proof. json_roundtrip_corollary water_phase_expr water_phase_idents_valid. Qed.

Corollary water_phase_translation_correct :
  forall fuel rho,
    peval fuel (env_to_pyenv rho) (translate water_phase_expr)
      = option_map value_to_pyvalue (eval fuel rho water_phase_expr).
Proof. intros fuel rho. apply translate_preserves_semantics. Qed.

Compute py_function "water_phase" ["tC"] (translate water_phase_expr).

(** Run for real:

    [[
    >>> water_phase(-5)
    'solid'
    >>> water_phase(0)
    'solid'
    >>> water_phase(50)
    'liquid'
    >>> water_phase(100)
    'gas'
    >>> water_phase(150)
    'gas'
    ]]
*)
