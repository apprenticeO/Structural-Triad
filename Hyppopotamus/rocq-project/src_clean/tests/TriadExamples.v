From Stdlib Require Import Reals Lists.List Lia.
From Stdlib Require Import micromega.Lra.
Require Import ESSEClean.theory.SystemSpec ESSEClean.theory.TriadSignals.

Import ListNotations.
Open Scope R_scope.

Module Dummy.
  (* Two toy cuts with small dimensions and opnorms *)
  Definition c1 : CutSpec := 
    {| dA := 2; 
       H_A := unit; 
       opnorm_HA := 1 
    |}.
  
  Definition c2 : CutSpec := 
    {| dA := 3; 
       H_A := unit; 
       opnorm_HA := 12/10 
    |}.

  (* Helper lemmas to fill Admissible fields without tactics inside the record *)
  Lemma cuts_ne : [c1;c2] <> [].
  Proof. discriminate. Qed.

  Lemma dmin_le_proof : forall c, In c [c1;c2] -> (2 <= dA c)%nat.
  Proof.
    intros c Hin.
    destruct Hin as [Hc|Hin2].
    - subst c. simpl. lia.
    - destruct Hin2 as [Hc2|Hin3].
      + subst c. simpl. lia.
      + contradiction.
  Qed.

  Lemma opnorm_le_proof : forall c, In c [c1;c2] -> 1 <= opnorm_HA c.
  Proof.
    intros c Hin.
    destruct Hin as [Hc|Hin2].
    - subst c. simpl. lra.
    - destruct Hin2 as [Hc2|Hin3].
      + subst c. simpl. lra.
      + contradiction.
  Qed.

  (* Simple admissible system over the two cuts *)
  Definition S : Admissible := {| 
    hbar := 1; 
    hbar_pos := Rlt_0_1;
    cuts := [c1;c2]; 
    cuts_nonempty := cuts_ne;
    dmin := 2;
    dmin_le := dmin_le_proof;
    dmin_ge_2 := le_n 2;
    opnorm_min := 1;
    opnorm_le := opnorm_le_proof;
    opnorm_min_pos := Rlt_0_1
  |}.

  (* Toy constant streams and good predicate for use with TriadSignals if needed *)
  Definition rA_t (_:CutSpec) (_:nat) : R := 1.
  Definition sA_t (c:CutSpec) (_:nat) : R := ln (INR (dA c)).
  Definition iA_t (_:CutSpec) (_:nat) : R := 1.
  Definition goodA_t (_:CutSpec) (_:nat) : bool := true.

  (* Verification lemmas to check our dummy system satisfies expected properties *)
  
  (* Verify INR conversions work as expected *)
  Lemma c1_dA_INR : INR (dA c1) = 2.
  Proof. simpl. lra. Qed.

  Lemma c2_dA_INR : INR (dA c2) = 3.
  Proof. simpl. lra. Qed.

  (* Verify dmin *)
  Lemma S_dmin_INR : INR (dmin S) = 2.
  Proof. simpl. lra. Qed.

  (* Verify opnorms are positive *)
  Lemma c1_opnorm_pos : 0 < opnorm_HA c1.
  Proof. simpl. lra. Qed.

  Lemma c2_opnorm_pos : 0 < opnorm_HA c2.
  Proof. simpl. lra. Qed.

  (* Verify ln(dA) is positive for both cuts *)
  Lemma c1_ln_dA_pos : 0 < ln (INR (dA c1)).
  Proof. 
    rewrite c1_dA_INR.
    assert (Hln1: ln 1 = 0) by apply ln_1.
    assert (Hlnlt: ln 1 < ln 2) by (apply ln_increasing; lra).
    rewrite Hln1 in Hlnlt. lra.
  Qed.

  Lemma c2_ln_dA_pos : 0 < ln (INR (dA c2)).
  Proof.
    rewrite c2_dA_INR.
    assert (Hln1: ln 1 = 0) by apply ln_1.
    assert (Hlnlt: ln 1 < ln 3) by (apply ln_increasing; lra).
    rewrite Hln1 in Hlnlt. lra.
  Qed.

  (* Verify ln(dmin) is positive *)
  Lemma S_ln_dmin_pos : 0 < ln (INR (dmin S)).
  Proof.
    rewrite S_dmin_INR.
    assert (Hln1: ln 1 = 0) by apply ln_1.
    assert (Hlnlt: ln 1 < ln 2) by (apply ln_increasing; lra).
    rewrite Hln1 in Hlnlt. lra.
  Qed.

  (* Verify 1 < INR(dA c) for both cuts *)
  Lemma c1_dA_gt_1 : 1 < INR (dA c1).
  Proof. rewrite c1_dA_INR. lra. Qed.

  Lemma c2_dA_gt_1 : 1 < INR (dA c2).
  Proof. rewrite c2_dA_INR. lra. Qed.

  (* Verify 1 < INR(dmin) *)
  Lemma S_dmin_gt_1 : 1 < INR (dmin S).
  Proof. rewrite S_dmin_INR. lra. Qed.

  (* Verify stream properties *)
  Lemma rA_nonneg : forall c t, 0 <= rA_t c t.
  Proof. intros. unfold rA_t. lra. Qed.

  Lemma sA_nonneg : forall c t, In c [c1;c2] -> 0 <= sA_t c t.
  Proof.
    intros c t Hin.
    unfold sA_t.
    destruct Hin as [Hc|Hin2].
    - subst c. apply Rlt_le. exact c1_ln_dA_pos.
    - destruct Hin2 as [Hc2|Hin3].
      + subst c. apply Rlt_le. exact c2_ln_dA_pos.
      + contradiction.
  Qed.

  Lemma iA_nonneg : forall c t, 0 <= iA_t c t.
  Proof. intros. unfold iA_t. lra. Qed.

  (* Verify sA_t satisfies the upper bound *)
  Lemma sA_bounded : forall c t, In c [c1;c2] -> sA_t c t <= ln (INR (dA c)).
  Proof.
    intros c t Hin. unfold sA_t. lra.
  Qed.

End Dummy.