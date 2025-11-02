(*
  FisherClean.v
  Paper mapping (Structural Triad, PDF):
  - [Activity] Section 3: For time-independent local generators, the quantum Fisher
    information satisfies F = 4 (ΔH)^2, which yields √F ≤ 2 ΔH used in the π-baseline.
  - This module records the identity (as an axiomatically provided equality) and
    exposes it for substitution in the activity functional.
*)
From Coq Require Import Reals Unicode.Utf8 Psatz.
Open Scope R_scope.

Section FisherClean.

Variable dimA : nat.

Variable VarH : nat -> R.
Variable Fisher : nat -> R.

Hypothesis time_indep_H : True.
Hypothesis fisher_identity_all : forall k, Fisher k = 4 * (VarH k)^2.

(* Paper cross-ref [Activity]: F = 4 Var^2 ⇒ √F ≤ 2 ΔH. *)
Lemma fisher_is_four_var :
  Fisher dimA = 4 * (VarH dimA)^2.
Proof.
  apply fisher_identity_all.
Qed.

End FisherClean. 