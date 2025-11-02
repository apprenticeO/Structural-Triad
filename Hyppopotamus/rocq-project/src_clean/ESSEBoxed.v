(*/
  ESSEBoxed.v
  Paper mapping (Structural Triad, PDF):
  - [Activity]: π-baseline assembling ΔH_A and S_A via I=2S, √F ≤ 2ΔH (Sec. 3)
  - [Pinsker+Floor]+[PerA+Avg]: per_bound assumed upstream (Sec. 4–5)
  - [Constructive]: Π_sys ≥ C_sum (finite-sum floor) (Sec. 6, Eq. perC_total)
  - [Universal]: positivity/strictness corollaries when terms are strictly positive (Sec. 6)

  Proof motifs:
  - Lift pointwise perA inequality to sums (map/fold_right monotonicity)
  - Monotone scaling by (4/hbar)
  - Positivity of sums from strictly positive summands
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.

Section ESSEBoxed.

Variable A : Type.

(* Physical constants and positivity *)
Variable hbar : R. Hypothesis hbar_pos : 0 < hbar.

(* Per-subsystem ingredients *)
Variable deltaH : A -> R.           (* variance of H_A, abstracted *)
Variable S : A -> R.                (* entropy S_A, abstracted *)
Variable v0 : A -> R.               (* variance floor constant per A *)
Variable c_lin : R.                 (* linear Pinsker constant *)
Variable deltaA : A -> R.           (* density of good times per A *)
Variable tau4 : A -> R.             (* liminf of quartic trace-distance per A *)

Hypothesis v0_pos : forall a, 0 < v0 a.
Hypothesis c_lin_pos : 0 < c_lin.
Hypothesis deltaA_range : forall a, 0 <= deltaA a <= 1.
Hypothesis tau4_nonneg : forall a, 0 <= tau4 a.

(* Assumed textbook identities provided elsewhere: *)
Hypothesis purity_id : True.   (* I(A:Ā)=2S_A *)
Hypothesis fisher_id : True.   (* F(ρ_A,H_A)=4(ΔH_A)^2 *)

(* Paper cross-ref [Pinsker+Floor]+[PerA+Avg]: per_bound origin is upstream; here we only use its sum-lifted consequence. *)
(* Per-subsystem bound delivered by PerBoundClean + PinskerSquaredClean + GapFloorClean + AveragingPerA: *)
Hypothesis per_bound : forall a, deltaH a * (S a * S a) >= v0 a * (c_lin * c_lin) * (deltaA a * tau4 a).

(* [Activity]/[Constructive] LHS/RHS terms and global functionals Π_sys, C_sum. *)
Definition termLHS (a:A) : R := deltaH a * (S a * S a).
Definition termRHS (a:A) : R := v0 a * (c_lin * c_lin) * (deltaA a * tau4 a).
Definition Pi_sys (L:list A) : R := (4 / hbar) * fold_right Rplus 0 (map termLHS L).
Definition C_sum (L:list A) : R := (4 / hbar) * fold_right Rplus 0 (map termRHS L).

(* [Constructive] Sum-lift of per_bound: Σ termRHS ≤ Σ termLHS. *)
Lemma sum_map_le: forall L,
  fold_right Rplus 0 (map termRHS L) <= fold_right Rplus 0 (map termLHS L).
Proof.
  induction L as [|a L0 IH]; simpl; [lra|].
  apply Rplus_le_compat.
  - apply Rge_le, per_bound.
  - exact IH.
Qed.

(* [Constructive] Π_sys ≥ C_sum by monotone scaling with (4/hbar). *)
Theorem ESSE_boxed_finite_sum : forall L, Pi_sys L >= C_sum L.
Proof.
  intro L. unfold Pi_sys, C_sum.
  set (c := 4 / hbar).
  assert (Hcpos: 0 <= c) by (unfold c; apply Rlt_le, Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos]).
  pose proof (sum_map_le L) as Hsum.
  apply Rle_ge.
  apply Rmult_le_compat_l; [exact Hcpos|exact Hsum].
Qed.

(* [Universal] Strict positivity of sums from strictly positive summands. *)
Lemma sum_positive_of_strict_terms : forall (w:A->R) L,
  L <> [] -> (forall a, In a L -> 0 < w a) -> 0 < fold_right Rplus 0 (map w L).
Proof.
  intros w L Hne Hall.
  induction L as [|a L0 IH]; [contradiction|]. simpl.
  destruct L0 as [|b L1].
  - simpl. specialize (Hall a (or_introl eq_refl)). lra.
  - assert (Hhead: 0 < w a) by (apply Hall; left; reflexivity).
    assert (Htail_pos: 0 < fold_right Rplus 0 (map w (b::L1))).
    { apply IH.
      + discriminate.
      + intros x Hinx. apply Hall. right. exact Hinx. }
    apply Rplus_lt_0_compat; assumption.
Qed.

(* [Universal] Nonzero RHS gives strictly positive C_sum. *)
Corollary ESSE_boxed_strict_pos : forall L,
  L <> [] -> (forall a, In a L -> 0 < v0 a * (c_lin * c_lin) * (deltaA a * tau4 a)) -> 0 < C_sum L.
Proof.
  intros L Hne Hall.
  unfold C_sum.
  set (w := fun a => (v0 a * (c_lin * c_lin) * (deltaA a * tau4 a))).
  assert (Hsum_pos: 0 < fold_right Rplus 0 (map w L)).
  { apply (sum_positive_of_strict_terms w L Hne). intros a Hin. apply Hall; exact Hin. }
  assert (Hcpos: 0 < 4 / hbar) by (apply Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos]).
  apply Rmult_lt_0_compat; assumption.
Qed.

(* [Universal] If C_sum>0 and Π_sys ≥ C_sum, then Π_sys>0. *)
Corollary ESSE_boxed_Pi_sys_pos : forall L,
  L <> [] -> (forall a, In a L -> 0 < v0 a * (c_lin * c_lin) * (deltaA a * tau4 a)) -> 0 < Pi_sys L.
Proof.
  intros L Hne Hall.
  pose proof (ESSE_boxed_finite_sum L) as Hge.
  specialize (Hge).
  pose proof (ESSE_boxed_strict_pos L Hne Hall) as Hpos.
  (* C_sum L > 0 and C_sum L <= Pi_sys L implies Pi_sys L > 0 *)
  unfold C_sum, Pi_sys in *.
  (* Convert Pi_sys >= C_sum to C_sum <= Pi_sys *)
  assert (HCle: (4 / hbar) * fold_right Rplus 0 (map termRHS L) <= (4 / hbar) * fold_right Rplus 0 (map termLHS L)) by (apply Rge_le; exact Hge).
  eapply Rlt_le_trans; [exact Hpos|exact HCle].
Qed.

End ESSEBoxed. 