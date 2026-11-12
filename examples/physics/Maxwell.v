(** Maxwell.v

    Maxwell's equations in vacuum and the electromagnetic wave equation --
    third module of a larger worked example built on Minkowski.v and
    Calculus.v (see docs/roadmap.md).

    * On the hypothesis set

    Maxwell's equations are introduced here as a hypothesis set (Gauss's
    law for E and B, Faraday's law, the Ampere-Maxwell law in vacuum),
    not derived from a symmetry principle via a Lagrangian and the
    Euler-Lagrange equations -- that is a substantially larger piece of
    variational calculus, not attempted here. Lorentz covariance of the
    field tensor's algebraic shape is established separately, in
    Minkowski.v.

    A real subtlety shows up when deriving the wave equation from these
    hypotheses: [Calculus.v]'s [feval] interprets a field expression
    relative to an arbitrary assignment of real numbers to each
    (atom name, multi-index) pair, with no built-in relationship between
    an atom's value and its "derivative" multi-index beyond what
    [pderiv]'s recursive structure already enforces combinatorially. That
    structure is enough to prove algebraic identities that hold for every
    possible assignment (e.g. [pderiv_comm], [curl_curl]) by induction.
    It is *not* enough to let you differentiate a hypothesis: knowing
    [feval assign (fx (curl E)) = feval assign (fx (vscale (-1) (vderiv CT B)))]
    for one fixed [assign] says nothing about [assign]'s values at the
    further-bumped multi-indices that a derivative of that equation would
    need, because [assign] is an arbitrary lookup table, not something
    known to come from actual differentiable functions of (t, x, y, z).

    Physically, Maxwell's equations hold at every point of a smooth field
    configuration, so differentiating both sides is valid -- but that
    fact is a statement about real multivariable calculus on genuine
    functions, outside what this symbolic layer represents (see
    Calculus.v's header). Rather than silently relying on it, every
    "already differentiated" fact the derivation below needs is stated as
    its own explicit hypothesis, alongside the base, zero-order law it
    corresponds to:

    - [gauss_E_grad] / [gauss_B_grad]: that the spatial gradient of
      [div E] / [div B] vanishes (not just [div E] / [div B] itself).
    - [curl_faraday]: Faraday's law with [curl] applied to both sides.
    - [ampere_dt]: the Ampere-Maxwell law differentiated once in time.
    - [curl_ampere] / [faraday_dt]: the same two moves, needed for the
      symmetric derivation of the wave equation for B.

    Each of these is the kind of fact that follows immediately once E and
    B are known to be smooth functions of space and time -- which is
    exactly the physical situation Maxwell's equations describe -- so
    assuming them here is a precise, local restatement of "the fields are
    smooth", not an unrelated or ad hoc addition. *)

From Coq Require Import Reals String Lra.
Require Import Calculus.
Open Scope R_scope.

Definition zero3 : vfield := mkvfield (FConst 0) (FConst 0) (FConst 0).

Section Maxwell.
  Variable c : R.
  Hypothesis c_nonzero : c <> 0.
  Variable E B : vfield.
  Variable assign : assign_t.

  (* Maxwell's equations in vacuum, zero-order (pointwise) form. *)
  Hypothesis gauss_E : feval assign (div E) = 0.
  Hypothesis gauss_B : feval assign (div B) = 0.
  Hypothesis faraday : veq assign (curl E) (vscale (-1) (vderiv CT B)).
  Hypothesis ampere : veq assign (curl B) (vscale (1 / (c * c)) (vderiv CT E)).

  (* The differentiated/closed forms the derivation below actually uses;
     see the module header for why these are hypothesized directly
     rather than derived from the equations above. *)
  Hypothesis gauss_E_grad : veq assign (grad (div E)) zero3.
  Hypothesis gauss_B_grad : veq assign (grad (div B)) zero3.
  Hypothesis curl_faraday : veq assign (curl (curl E)) (vscale (-1) (vderiv CT (curl B))).
  Hypothesis curl_ampere : veq assign (curl (curl B)) (vscale (1 / (c * c)) (vderiv CT (curl E))).
  Hypothesis ampere_dt : veq assign (vderiv CT (curl B)) (vscale (1 / (c * c)) (vderiv CT (vderiv CT E))).
  Hypothesis faraday_dt : veq assign (vderiv CT (curl E)) (vscale (-1) (vderiv CT (vderiv CT B))).

  (** Each component E satisfies the scalar wave equation with speed [c]:
      [partial_t^2 E = c^2 laplacian E]. Derived from [curl_faraday]
      (giving [curl (curl E)] in terms of [B]'s second time-derivative via
      [ampere_dt]) equated with [curl_curl] + [gauss_E_grad] (giving
      [curl (curl E)] in terms of [E]'s Laplacian) -- the standard
      textbook derivation, mechanized. *)
  Theorem wave_equation_E :
    veq assign (vderiv CT (vderiv CT E)) (vscale (c * c) (vlaplacian E)).
  Proof.
    pose proof (curl_curl assign E) as Hcc.
    unfold veq in Hcc, gauss_E_grad, curl_faraday, ampere_dt |- *.
    unfold zero3, vsub, grad, div, vlaplacian, vscale, vderiv in *; simpl in *.
    destruct Hcc as [Hccx [Hccy Hccz]].
    destruct gauss_E_grad as [Hgx [Hgy Hgz]].
    destruct curl_faraday as [Hfx [Hfy Hfz]].
    destruct ampere_dt as [Hax [Hay Haz]].
    apply (Rmult_eq_compat_l (c * c)) in Hax.
    apply (Rmult_eq_compat_l (c * c)) in Hay.
    apply (Rmult_eq_compat_l (c * c)) in Haz.
    field_simplify in Hax; [| exact c_nonzero].
    field_simplify in Hay; [| exact c_nonzero].
    field_simplify in Haz; [| exact c_nonzero].
    repeat split; nra.
  Qed.

  (** The symmetric statement for B, via [curl_ampere] and [faraday_dt]. *)
  Theorem wave_equation_B :
    veq assign (vderiv CT (vderiv CT B)) (vscale (c * c) (vlaplacian B)).
  Proof.
    pose proof (curl_curl assign B) as Hcc.
    unfold veq in Hcc, gauss_B_grad, curl_ampere, faraday_dt |- *.
    unfold zero3, vsub, grad, div, vlaplacian, vscale, vderiv in *; simpl in *.
    destruct Hcc as [Hccx [Hccy Hccz]].
    destruct gauss_B_grad as [Hgx [Hgy Hgz]].
    destruct curl_ampere as [Hfx [Hfy Hfz]].
    destruct faraday_dt as [Hax [Hay Haz]].
    apply (Rmult_eq_compat_l (c * c)) in Hfx.
    apply (Rmult_eq_compat_l (c * c)) in Hfy.
    apply (Rmult_eq_compat_l (c * c)) in Hfz.
    field_simplify in Hfx; [| exact c_nonzero].
    field_simplify in Hfy; [| exact c_nonzero].
    field_simplify in Hfz; [| exact c_nonzero].
    repeat split; nra.
  Qed.
End Maxwell.
