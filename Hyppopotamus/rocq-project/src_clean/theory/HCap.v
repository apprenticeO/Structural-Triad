From Coq Require Import Reals Lists.List Psatz.
Import ListNotations. Open Scope R_scope.
Require Import ESSEClean.theory.SystemSpec ESSEClean.theory.Normalization ESSEClean.theory.Bridges.

(* Pointwise Hamiltonian-capped bridge: use (hbar/2) * sqrtFQ ≤ ΔE to lower-bound ΔE·S·I in terms of Psi_hat *)
Lemma hcap_pointwise:
  forall (S: Admissible) (c: CutSpec) (q s i dE: R),
    0 <= s -> 0 <= i -> 0 <= q ->
    (hbar S) > 0 ->
    (hbar S / 2) * q <= dE ->
    0 < opnorm_HA c -> 1 < INR (dA c) -> 1 < INR S.(dmin) ->
    dE * (s * i)
    >= (hbar S) * (opnorm_HA c) * (ln (INR (dA c))) * (2 * ln (INR S.(dmin))) *
       Psi_hat S q s i c.
Proof.
  intros S c q s i dE Hs0 Hi0 Hq0 Hh Hbound Hop HdimA Hdmin.
  (* Scale the inequality by nonnegative (s*i) *)
  assert (Hsip : 0 <= s * i) by (apply Rmult_le_pos; assumption).
  assert (Hscaled : ((hbar S) / 2) * q * (s * i) <= dE * (s * i)).
  { apply Rmult_le_compat_r; [exact Hsip| exact Hbound]. }
  (* Express (hbar/2)*q*s*i via Psi_hat definition *)
  unfold Psi_hat.
  (* Establish nonzero denominators for safe algebraic rewriting. *)
  set (A := opnorm_HA c).
  set (B := ln (INR (dA c))).
  set (C := ln (INR (dmin S))).
  assert (Apos: 0 < A) by (subst A; exact Hop).
  assert (Aneq: A <> 0) by (apply Rgt_not_eq; exact Apos).
  assert (Bpos: 0 < B).
  { subst B. assert (Hln1: ln 1 = 0) by apply ln_1.
    assert (Hgt: 1 < INR (dA c)) by exact HdimA.
    assert (Hlnlt: ln 1 < ln (INR (dA c))) by (apply ln_increasing; [lra|exact Hgt]).
    rewrite Hln1 in Hlnlt; lra. }
  assert (Bneq: B <> 0) by (apply Rgt_not_eq; exact Bpos).
  assert (Cpos: 0 < C).
  { subst C. assert (Hln1: ln 1 = 0) by apply ln_1.
    assert (Hgt: 1 < INR (dmin S)) by exact Hdmin.
    assert (Hlnlt: ln 1 < ln (INR (dmin S))) by (apply ln_increasing; [lra|exact Hgt]).
    rewrite Hln1 in Hlnlt; lra. }
  assert (Cneq: C <> 0) by (apply Rgt_not_eq; exact Cpos).
  (* Rewrite the left term into the Psi_hat-scaled form. *)
  replace (((hbar S) / 2) * q * (s * i))
    with ((hbar S) * A * B * (2 * C) * ((q / (2 * A)) * (s / B) * (i / (2 * C))))
    by (subst A B C; field; split; try exact Aneq; split; try exact Bneq; exact Cneq).
  lra.
Qed.

(* Averaged Hamiltonian-capped bound across cuts using minima *)
Lemma hcap_avg_bound_at_n :
  forall (S: Admissible)
         (dE s i q : CutSpec -> nat -> R) (n:nat),
    (forall c, In c S.(cuts) -> 0 <= s c n /\ 0 <= i c n /\ 0 <= q c n /\ 0 <= dE c n) ->
    (forall c, In c S.(cuts) -> (hbar S / 2) * q c n <= dE c n) ->
    avg_over_cuts S (fun c => dE c n * (s c n * i c n))
    >= (hbar S) * (opnorm_min S) * (ln (INR S.(dmin))) * (2 * ln (INR S.(dmin))) *
       avg_over_cuts S (fun c => Psi_hat S (q c n) (s c n) (i c n) c).
Proof.
  intros S dE s i q n Hnonneg Hrel.
  unfold avg_over_cuts.
  (* Build pointwise lower bound with local opnorm/logs, then replace by minima *)
  set (f := fun c => dE c n * (s c n * i c n)).
  set (g := fun c => (hbar S) * (opnorm_HA c) * (ln (INR (dA c))) * (2 * ln (INR S.(dmin))) *
                     Psi_hat S (q c n) (s c n) (i c n) c).
  (* Show sum f >= sum g by pointwise inequalities *)
  assert (Hpt: forall c, In c S.(cuts) -> f c >= g c).
  { intros c Hin.
    destruct (Hnonneg c Hin) as [Hs0 [Hi0 [Hq0 HdE0]]].
    (* derive denominators positivity from admissibility *)
    assert (Hop: 0 < opnorm_HA c).
    { (* opnorm_HA c >= opnorm_min > 0 *)
      pose proof (opnorm_le S c Hin) as Hle.
      pose proof (opnorm_min_pos S) as Hminpos.
      enough (opnorm_HA c > 0) by exact H.
      apply Rlt_le_trans with (r2:=opnorm_min S); [exact Hminpos| exact Hle]. }
    assert (HdimA: 1 < INR (dA c)).
    { (* from dA c >= dmin >= 2 *)
      assert (Hge2: (2 <= dA c)%nat) by (apply dA_ge_2 with (S:=S); exact Hin).
      replace 1 with (INR 1) by reflexivity.
      eapply Rlt_le_trans with (r2:=INR 2); [simpl; lra|].
      apply le_INR in Hge2; exact Hge2. }
    assert (Hdmin: 1 < INR (dmin S)).
    { replace 1 with (INR 1) by reflexivity.
      eapply Rlt_le_trans with (r2:=INR 2); [simpl; lra|].
      apply le_INR, (dmin_ge_2 S). }
    (* relate dE to q via (hbar/2) q ≤ dE, supplied in Hrel after rewriting *)
    have Hrel' : (hbar S / 2) * q c n <= dE c n by (apply Hrel; exact Hin).
    (* apply pointwise bridge *)
    apply Rle_ge.
    eapply Rle_trans.
    - (* g ≤ f by hcap_pointwise rearranged direction *)
      apply Rge_le.
      apply (hcap_pointwise S c (q c n) (s c n) (i c n) (dE c n)); try assumption; try lra.
    - (* trivial *) lra.
  }
  (* Sum and scale by positive 1/|E| *)
  assert (Hsum_ge: fold_right Rplus 0 (map f (cuts S)) >= fold_right Rplus 0 (map g (cuts S))).
  { clear -Hpt. induction (cuts S) as [|c cs IH]; simpl; [lra|].
    assert (Hc: f c >= g c) by (apply Hpt; left; reflexivity).
    specialize (IH (fun c' Hin' => Hpt c' (or_intror Hin'))).
    lra. }
  (* Replace opnorm_HA and ln dA by minima in the multiplier, using nonnegativity of the rest *)
  set (h := fun c => Psi_hat S (q c n) (s c n) (i c n) c).
  (* show nonnegativity of h and logs to justify monotone replacements *)
  assert (Hh_nonneg: forall c, In c S.(cuts) -> 0 <= h c).
  { intros c Hin.
    destruct (Hnonneg c Hin) as [Hs0 [Hi0 [Hq0 _]]].
    (* positivity witnesses *)
    assert (Hop: 0 < opnorm_HA c).
    { pose proof (opnorm_le S c Hin) as Hle.
      pose proof (opnorm_min_pos S) as Hminpos.
      apply Rlt_le_trans with (r2:=opnorm_min S) in Hminpos; [|exact Hle]. exact Hminpos. }
    assert (HdAgt1: 1 < INR (dA c)).
    { assert (Hge2: (2 <= dA c)%nat) by (apply dA_ge_2 with (S:=S); exact Hin).
      replace 1 with (INR 1) by reflexivity.
      eapply Rlt_le_trans with (r2:=INR 2); [simpl; lra|].
      apply le_INR in Hge2; exact Hge2. }
    assert (Hdmingt1: 1 < INR (dmin S)).
    { replace 1 with (INR 1) by reflexivity.
      eapply Rlt_le_trans with (r2:=INR 2); [simpl; lra|].
      apply le_INR, (dmin_ge_2 S). }
    apply Psi_hat_nonneg; try assumption.
  }
  (* For each c, replace (opnorm_HA c) ≥ opnorm_min and ln dA ≥ ln dmin inside g *)
  set (g' := fun c => (hbar S) * (opnorm_min S) * (ln (INR S.(dmin))) * (2 * ln (INR S.(dmin))) * h c).
  assert (Hg_ge: forall c, In c S.(cuts) -> g c >= g' c).
  { intros c Hin.
    unfold g, g'.
    (* the factor h is ≥ 0; ln(INR S.(dmin)) > 0 as well *)
    assert (Hlnpos: 0 < ln (INR S.(dmin))) by (apply ln_dmin_pos).
    assert (Hrest_nonneg: 0 <= (2 * ln (INR (dmin S))) * h c).
    { apply Rmult_le_pos; [apply Rlt_le; nra|]. apply Hh_nonneg; exact Hin. }
    (* replace by minima stepwise *)
    (* replace opnorm_HA by opnorm_min *)
    assert (Hop_le: (opnorm_min S) <= (opnorm_HA c)) by (apply opnorm_le; exact Hin).
    assert (Hstep1: (opnorm_min S) * ((ln (INR (dA c))) * ((2 * ln (INR (dmin S))) * h c))
                    <= (opnorm_HA c) * ((ln (INR (dA c))) * ((2 * ln (INR (dmin S))) * h c))).
    { apply Rmult_le_compat_r; [apply Rmult_le_pos; [apply Rlt_le; apply ln_dmin_pos| apply Hh_nonneg; exact Hin] | exact Hop_le]. }
    (* replace ln (INR dA c) by ln (INR dmin) *)
    assert (Hln_le: ln (INR S.(dmin)) <= ln (INR (dA c))) by (apply ln_dmin_le_lndA; exact Hin).
    assert (Hstep2: (ln (INR S.(dmin))) * ((2 * ln (INR (dmin S))) * h c)
                    <= (ln (INR (dA c))) * ((2 * ln (INR (dmin S))) * h c)).
    { apply Rmult_le_compat_r; [apply Rmult_le_pos; [apply Rlt_le; apply ln_dmin_pos| apply Hh_nonneg; exact Hin] | exact Hln_le]. }
    (* assemble with common positive scalar hbar S *)
    (* rearrange to show overall product inequality *)
    nra.
  }
  (* Now chain: sum f >= sum g >= sum g' *)
  assert (Hsum_ge_min: fold_right Rplus 0 (map g (cuts S)) >= fold_right Rplus 0 (map g' (cuts S))).
  { clear -Hg_ge. induction (cuts S) as [|c cs IH]; simpl; [lra|].
    assert (Hc: g c >= g' c) by (apply Hg_ge; left; reflexivity).
    specialize (IH (fun c' Hin' => Hg_ge c' (or_intror Hin'))). lra. }
  (* Divide by |E| (positive) and conclude *)
  replace (1 / E_card S) with (/ E_card S) by (unfold Rdiv; ring).
  apply Rmult_ge_compat_l.
  - apply Rlt_le, Rinv_0_lt_compat, E_card_pos.
  - eapply Rge_trans; [exact Hsum_ge| exact Hsum_ge_min].
Qed.

(* Simple eventual wrapper (kept compatible with previous skeleton signature) *)
Lemma hcap_bound_eventual :
  forall (S: Admissible)
         (dE s i sqrtFQ: CutSpec -> nat -> R),
  (forall c n, 0 <= dE c n /\ 0 <= s c n /\ 0 <= i c n /\ 0 <= sqrtFQ c n) ->
  (forall c n, sqrtFQ c n <= (2 / S.(hbar)) * dE c n) ->
  exists N1, forall n, (n >= N1)%nat ->
    avg_over_cuts S (fun c => dE c n * (s c n * i c n))
    >= (hbar S) * (opnorm_min S) * (ln (INR S.(dmin))) * (2 * ln (INR S.(dmin))) *
       avg_over_cuts S (fun c => Psi_hat S (sqrtFQ c n) (s c n) (i c n) c).
Proof.
  intros S dE s i q Hnn Hrel.
  exists 0%nat. intros n _.
  (* rewrite relational assumption into (hbar/2) q ≤ dE *)
  assert (Hrel' : forall c, In c S.(cuts) -> (hbar S / 2) * q c n <= dE c n).
  { intros c Hin.
    specialize (Hrel c n).
    (* sqrtFQ ≤ (2/ħ) dE ⇒ multiply both sides by ħ/2 > 0 *)
    replace ((hbar S) / 2) with (1 / (2 / (hbar S))) by (field; lra).
    apply Rle_mult_inv_pos; [apply Rmult_lt_0_compat; [lra|apply hbar_pos] | exact Hrel]. }
  (* unpack nonnegativity tuple for the required shape *)
  assert (Hnonneg': forall c, In c S.(cuts) -> 0 <= s c n /\ 0 <= i c n /\ 0 <= q c n /\ 0 <= dE c n).
  { intros c Hin. destruct (Hnn c n) as [HdE [Hs [Hi Hq]]]. auto. }
  eapply hcap_avg_bound_at_n; eauto.
Qed.
