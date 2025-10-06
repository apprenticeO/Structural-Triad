(*
  ESSEList.v
  Paper mapping (hyppo_esse_derivation.tex):
  - [Constructive] Section 6: Lift the per-subsystem bound ΔH·S^2 ≥ v0·c_lin^2·δ_A·τ_A^4
    to sums over A, and scale by (4/ħ) to obtain Π_sys ≥ C_sum (finite-sum floor).
  - This module provides the sum-lift and scaling, reused by ESSEUniversal and ESSEBoxed.
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.

Section ESSEList.

Variable A : Type.
Variable hbar : R. Hypothesis hbar_pos : 0 < hbar.

(* Per-subsystem quantities *)
Variable deltaH : A -> R.
Variable S : A -> R.

(* Averaging-derived constants: δ_A and τ_A^4 *)
Variable deltaA : A -> R.
Variable tau4 : A -> R.

(* Proven per-subsystem combined lower bound: ΔH·S^2 ≥ v0·c_lin^2·δ_A·τ_A^4 *)
Variable v0 : A -> R.
Variable c_lin : R.
Hypothesis v0_pos : forall a, 0 < v0 a.
Hypothesis c_lin_pos : 0 < c_lin.
Hypothesis per_bound : forall a, deltaH a * (S a * S a) >= v0 a * (c_lin * c_lin) * (deltaA a * tau4 a).

Definition termLHS (a:A) : R := deltaH a * (S a * S a).
Definition termRHS (a:A) : R := (v0 a) * (c_lin * c_lin) * (deltaA a * tau4 a).

Definition Pi_sys (L:list A) : R := (4 / hbar) * fold_right Rplus 0 (map termLHS L).
Definition C_sum (L:list A) : R := (4 / hbar) * fold_right Rplus 0 (map termRHS L).

(* Paper cross-ref [Constructive]: Σ termRHS ≤ Σ termLHS *)
Lemma sum_map_le: forall L,
  fold_right Rplus 0 (map termRHS L) <= fold_right Rplus 0 (map termLHS L).
Proof.
  induction L as [|a L0 IH]; simpl; [lra|].
  apply Rplus_le_compat.
  - apply Rge_le, per_bound.
  - exact IH.
Qed.

(* Paper cross-ref [Constructive]: Π_sys ≥ C_sum by monotone scaling with (4/ħ). *)
Lemma Pi_sys_lower_sum : forall L,
  Pi_sys L >= C_sum L.
Proof.
  intro L. unfold Pi_sys, C_sum.
  set (c := 4 / hbar).
  assert (Hcpos: 0 <= c) by (unfold c; apply Rlt_le, Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos]).
  pose proof (sum_map_le L) as Hsum.
  assert (Hmul: c * fold_right Rplus 0 (map termRHS L) <= c * fold_right Rplus 0 (map termLHS L)).
  { apply Rmult_le_compat_l; [exact Hcpos| exact Hsum]. }
  apply Rle_ge in Hmul. exact Hmul.
Qed.

Theorem ESSE_list_boxed : forall L, L <> [] -> Pi_sys L >= C_sum L.
Proof.
  intros L _. apply Pi_sys_lower_sum.
Qed.

End ESSEList. 