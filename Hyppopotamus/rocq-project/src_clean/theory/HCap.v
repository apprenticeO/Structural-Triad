(*
  theory/HCap.v
  Paper mapping: Structural Triad (PDF)
  - Theorem: Hamiltonian‑Capped Structural Threshold (HCap)
    Uses normalization (Ψ̂), minima replacement (‖H‖_min, ln d_min), and a monotone lift to
    obtain an averaged inequality with hardware‑capped scales.
  - This file organizes the proof into numbered steps:
    1) Nonnegativity of the energy triad factor
    2) Log/opnorm positivity helpers (from SystemSpec)
    3) Nonnegativity of normalized division factors
    4) Averaging over cuts (monotone lift)
    5) Replace‑by‑minima product helper (ln, opnorm)
    6) Psi_hat scaling identity and regroupings
    7) Pointwise monotone lift
    8) Averaged pointwise lift over cuts
    9) Final averaged inequality with minima replacement
*)
From Coq Require Import Reals Psatz Lists.List.
Require Import Coq.setoid_ring.Ring.
From Stdlib Require Import Field.
Open Scope R_scope.

(* Step 1: Minimal, compiling lemma — basic nonnegativity of the energy triad factor *)
Lemma hcap_pointwise_nonneg:
  forall s i dE : R,
    0 <= s -> 0 <= i -> 0 <= dE ->
    0 <= dE * (s * i).
Proof.
  intros s i dE Hs Hi HdE.
  apply Rmult_le_pos; [assumption | apply Rmult_le_pos; assumption].
Qed.

(* Step 2: Log/opnorm positivity helpers, one by one *)
Require Import ESSEClean.theory.SystemSpec ESSEClean.theory.Normalization.

Lemma ln_dA_pos :
  forall (S:Admissible) (c:CutSpec), In c S.(cuts) -> 0 < ln (INR (dA c)).
Proof.
  intros S c Hin.
  (* From dA >= 2 we get 1 < INR dA, then ln 1 < ln (INR dA) *)
  assert (HdA2 : (2 <= dA c)%nat) by (apply dA_ge_2 with (S:=S); exact Hin).
  assert (Hgt1 : 1 < INR (dA c)).
  { replace 1 with (INR 1) by reflexivity.
    eapply Rlt_le_trans with (r2:=INR 2); [simpl; lra|].
    apply le_INR in HdA2; exact HdA2. }
  assert (Hln1: ln 1 = 0) by apply ln_1.
  assert (Hlnlt: ln 1 < ln (INR (dA c))) by (apply ln_increasing; [lra|exact Hgt1]).
  rewrite Hln1 in Hlnlt. lra.
Qed.

Lemma opnorm_HA_pos_from_min :
  forall (S:Admissible) (c:CutSpec), In c S.(cuts) -> 0 < opnorm_HA c.
Proof.
  intros S c Hin.
  (* opnorm_HA c >= opnorm_min > 0 ⇒ opnorm_HA c > 0 *)
  pose proof (opnorm_le S c Hin) as Hle.
  pose proof (opnorm_min_pos S) as Hminpos.
  eapply Rlt_le_trans; [exact Hminpos| exact Hle].
Qed.

(* Step 3: Each normalized factor is nonnegative under admissibility *)
Lemma hcap_div_factors_nonneg :
  forall (S:Admissible) (c:CutSpec) (q s i:R),
    In c S.(cuts) -> 0 <= q -> 0 <= s -> 0 <= i ->
    0 <= q / (2 * opnorm_HA c)
    /\ 0 <= s / ln (INR (dA c))
    /\ 0 <= i / (2 * ln (INR S.(dmin))).
Proof.
  intros S c q s i Hin Hq Hs Hi.
  (* denominators are positive by admissibility *)
  assert (Hop : 0 < opnorm_HA c) by (apply (opnorm_HA_pos_from_min S); exact Hin).
  assert (HlnA : 0 < ln (INR (dA c))) by (apply (ln_dA_pos S); exact Hin).
  assert (HlnD : 0 < ln (INR S.(dmin))) by apply (ln_dmin_pos S).
  (* Inverse/quotient positivity *)
  assert (Hden1 : 0 < 2 * opnorm_HA c) by (apply Rmult_lt_0_compat; [lra| exact Hop]).
  assert (Hden3 : 0 < 2 * ln (INR S.(dmin))) by (apply Rmult_lt_0_compat; [lra| exact HlnD]).
  split.
  - unfold Rdiv. apply Rmult_le_pos; [exact Hq| apply Rlt_le, Rinv_0_lt_compat; exact Hden1].
  - split.
    + unfold Rdiv. apply Rmult_le_pos; [exact Hs| apply Rlt_le, Rinv_0_lt_compat; exact HlnA].
    + unfold Rdiv. apply Rmult_le_pos; [exact Hi| apply Rlt_le, Rinv_0_lt_compat; exact Hden3].
Qed.

(* Step 4: Average over cuts is nonnegative if the integrand is nonnegative *)
Lemma avg_over_cuts_nonneg_local :
  forall (S:Admissible) (f: CutSpec -> R),
    (forall c, In c S.(cuts) -> 0 <= f c) ->
    0 <= avg_over_cuts S f.
Proof.
  intros S f Hnonneg.
  unfold avg_over_cuts.
  (* (1/|E|) > 0 *)
  assert (Hscale_nonneg: 0 <= / E_card S) by (apply Rlt_le, Rinv_0_lt_compat, E_card_pos).
  (* sum of nonnegatives is nonnegative *)
  assert (Hsum_nonneg: 0 <= fold_right Rplus 0 (map f S.(cuts))).
  { induction (cuts S) as [|c cs IH]; simpl; [lra|].
    assert (Hc: 0 <= f c) by (apply Hnonneg; left; reflexivity).
    specialize (IH (fun c' Hin' => Hnonneg c' (or_intror Hin'))).
    lra. }
  replace (1 / E_card S) with (/ E_card S) by (unfold Rdiv; ring).
  apply Rmult_le_pos; assumption.
Qed.

(* Step 5: Replace-by-minima product helper (opnorm and log) *)
Lemma replace_by_min_product :
  forall (S:Admissible) (c:CutSpec) (x y:R),
    In c S.(cuts) -> 0 <= x -> 0 <= y ->
    (opnorm_min S) * (ln (INR S.(dmin))) * (x * y)
    <= (opnorm_HA c) * (ln (INR (dA c))) * (x * y).
Proof.
  intros S c x y Hin Hx Hy.
  set (t1 := (ln (INR S.(dmin))) * (x * y)).
  set (t2 := (ln (INR (dA c))) * (x * y)).
  (* Both x,y are nonnegative, hence t1,t2 are well-formed for monotone scaling *)
  assert (Hxy_nonneg: 0 <= x * y) by (apply Rmult_le_pos; assumption).
  (* ln dmin * (x*y) ≤ ln dA * (x*y) *)
  assert (have_ln: t1 <= t2).
  { unfold t1, t2. apply replace_by_min_ln; assumption. }
  (* Scale by opnorm_min ≥ 0 *)
  assert (Hmin_nonneg: 0 <= opnorm_min S) by (apply Rlt_le, opnorm_min_pos).
  assert (Hstep1: (opnorm_min S) * t1 <= (opnorm_min S) * t2)
    by (apply Rmult_le_compat_l; [exact Hmin_nonneg| exact have_ln]).
  (* Replace opnorm_min by opnorm_HA on the right, with nonnegative multiplier t2 *)
  assert (HlnA_pos: 0 < ln (INR (dA c))) by (apply (ln_dA_pos S); exact Hin).
  assert (Ht2_nonneg: 0 <= t2).
  { unfold t2. apply Rmult_le_pos; [apply Rlt_le; exact HlnA_pos| exact Hxy_nonneg]. }
  assert (Hstep2: (opnorm_min S) * t2 <= (opnorm_HA c) * t2)
    by (apply replace_by_min_opnorm; [exact Ht2_nonneg| exact Hin]).
  (* Chain steps; normalize associativity to match goal shape *)
  replace ((opnorm_min S) * (ln (INR S.(dmin))) * (x * y))
    with ((opnorm_min S) * (ln (INR S.(dmin)) * (x * y))) by ring.
  replace ((opnorm_HA c) * (ln (INR (dA c))) * (x * y))
    with ((opnorm_HA c) * (ln (INR (dA c)) * (x * y))) by ring.
  eapply Rle_trans; [exact Hstep1| exact Hstep2].
Qed.

(* Step 6a: Psi_hat scaling identity (split into two small lemmas) *)

Lemma psi_hat_pairs_collapse :
  forall A B C q s i : R,
    A <> 0 -> B <> 0 -> C <> 0 ->
    (A * (q / (2 * A))) * (B * (s / B)) * ((2 * C) * (i / (2 * C)))
    = (q / 2) * s * i.
Proof.
  intros A B C q s i Aneq Bneq Cneq.
  (* collapse each pair *)
  assert (E1: A * (q / (2 * A)) = q / 2).
  { unfold Rdiv. field; try lra; try exact Aneq. }
  assert (E2: B * (s / B) = s) by (unfold Rdiv; field; exact Bneq).
  assert (E3: (2 * C) * (i / (2 * C)) = i).
  { unfold Rdiv. field; try lra; try exact Cneq. }
  rewrite E1, E2, E3. ring.
Qed.

Lemma regroup_half :
  forall h q s i : R,
    h * ((q / 2) * s * i) = (h / 2) * q * (s * i).
Proof.
  intros h q s i. unfold Rdiv. ring.
Qed.

Lemma regroup_for_pairs :
  forall (t a b c x y z : R),
    t * a * b * (2 * c) * (x * y * z)
    = t * ((a * x) * (b * y) * ((2 * c) * z)).
Proof. intros; ring. Qed.
Lemma psi_hat_scaling_identity :
  forall (S:Admissible) (c:CutSpec) (q s i:R),
    In c S.(cuts) ->
    (hbar S) > 0 ->
    (hbar S) * (opnorm_HA c) * (ln (INR (dA c))) * (2 * ln (INR S.(dmin))) *
      Psi_hat S q s i c
    = (hbar S / 2) * q * (s * i).
Proof.
  intros S c q s i Hin Hh.
  unfold Psi_hat.
  set (A := opnorm_HA c).
  set (B := ln (INR (dA c))).
  set (C := ln (INR S.(dmin))).
  assert (Apos: 0 < A) by (apply (opnorm_HA_pos_from_min S); exact Hin).
  assert (Bpos: 0 < B) by (apply (ln_dA_pos S); exact Hin).
  assert (Cpos: 0 < C) by (apply (ln_dmin_pos S)).
  assert (Aneq: A <> 0) by (apply Rgt_not_eq; exact Apos).
  assert (Bneq: B <> 0) by (apply Rgt_not_eq; exact Bpos).
  assert (Cneq: C <> 0) by (apply Rgt_not_eq; exact Cpos).
  (* Regroup to match psi_hat_pairs_collapse *)
  set (X := q / (2 * A)).
  set (Y := s / B).
  set (Z := i / (2 * C)).
  rewrite (regroup_for_pairs (hbar S) A B C X Y Z).
  subst X Y Z.
  rewrite (psi_hat_pairs_collapse A B C q s i Aneq Bneq Cneq).
  (* Turn h * ((q/2)*s*i) into (h/2)*q*(s*i) *)
  unfold Rdiv. ring.
Qed.


(* Step 6: Pointwise monotone lift without Psi_hat *)
Lemma hcap_pointwise_mono :
  forall (S:Admissible) (q s i dE:R),
    0 <= s -> 0 <= i -> 0 <= q ->
    (hbar S) > 0 ->
    (hbar S / 2) * q <= dE ->
    (hbar S / 2) * q * (s * i) <= dE * (s * i).
Proof.
  intros S q s i dE Hs Hi Hq Hh Hle.
  assert (Hsi_nonneg: 0 <= s * i) by (apply Rmult_le_pos; assumption).
  apply Rmult_le_compat_r; [exact Hsi_nonneg | exact Hle].
Qed.

(* Step 7: Averaged monotone lift across cuts *)
Lemma hcap_avg_pointwise_mono :
  forall (S:Admissible) (q s i dE: CutSpec -> R),
    (forall c, In c S.(cuts) -> 0 <= s c /\ 0 <= i c /\ 0 <= q c /\ (hbar S / 2) * q c <= dE c) ->
    0 < hbar S ->
    avg_over_cuts S (fun c => (hbar S / 2) * q c * (s c * i c))
    <= avg_over_cuts S (fun c => dE c * (s c * i c)).
Proof.
  intros S q s i dE Hpt Hhpos.
  set (f := fun c => (hbar S / 2) * q c * (s c * i c)).
  set (g := fun c => dE c * (s c * i c)).
  eapply (avg_mono_nonneg S) with (f:=f) (g:=g).
  intros c Hin.
  destruct (Hpt c Hin) as [Hs [Hi [Hq Hle]]].
  (* f c nonneg *)
  assert (Hkpos: 0 < (hbar S) / 2) by lra.
  assert (Hkge: 0 <= (hbar S) / 2) by (apply Rlt_le; exact Hkpos).
  assert (Hsi: 0 <= s c * i c) by (apply Rmult_le_pos; assumption).
  split.
  { unfold f. apply Rmult_le_pos; [apply Rmult_le_pos; [exact Hkge| exact Hq] | exact Hsi]. }
  { unfold f, g. apply (hcap_pointwise_mono S (q c) (s c) (i c) (dE c)); try assumption. }
Qed.

(* Step 8: Pointwise HCap inequality using Psi_hat scaling + monotone lift *)
Lemma hcap_pointwise_with_psi :
  forall (S:Admissible) (c:CutSpec) (q s i dE:R),
    In c S.(cuts) -> 0 <= s -> 0 <= i -> 0 <= q ->
    (hbar S) > 0 ->
    (hbar S / 2) * q <= dE ->
    dE * (s * i)
    >= (hbar S) * (opnorm_HA c) * (ln (INR (dA c))) * (2 * ln (INR S.(dmin))) *
       Psi_hat S q s i c.
Proof.
  intros S c q s i dE Hin Hs Hi Hq Hh Hle.
  rewrite (psi_hat_scaling_identity S c q s i Hin Hh).
  apply Rle_ge.
  apply (hcap_pointwise_mono S q s i dE); assumption.
Qed.


(* Step 9: Averaged HCap inequality with Psi_hat and minima replacement *)
Lemma hcap_avg_with_psi_minima :
  forall (S:Admissible) (q s i dE: CutSpec -> R),
    0 < hbar S ->
    (forall c, In c S.(cuts) -> 0 <= s c /\ 0 <= i c /\ 0 <= q c /\ (hbar S / 2) * q c <= dE c) ->
    avg_over_cuts S (fun c => dE c * (s c * i c))
    >= avg_over_cuts S (fun c => (hbar S) * (opnorm_min S) * (ln (INR S.(dmin))) * (2 * ln (INR S.(dmin))) *
                               Psi_hat S (q c) (s c) (i c) c).
Proof.
  intros S q s i dE Hhpos Hpt.
  set (K := (hbar S) * (opnorm_min S) * (ln (INR S.(dmin))) * (2 * ln (INR S.(dmin)))).
  set (f := fun c => K * Psi_hat S (q c) (s c) (i c) c).
  set (g := fun c => dE c * (s c * i c)).
  (* We want avg g >= avg f *)
  apply Rle_ge.
  eapply (avg_mono_nonneg S) with (f:=f) (g:=g).
  intros c Hin.
  destruct (Hpt c Hin) as [Hs [Hi [Hq Hle]]].
  (* 0 <= f c *)
  assert (Hmin_nonneg: 0 <= opnorm_min S) by (apply Rlt_le, opnorm_min_pos).
  assert (HlnD_pos: 0 < ln (INR S.(dmin))) by apply (ln_dmin_pos S).
  assert (HlnD_nonneg: 0 <= ln (INR S.(dmin))) by (apply Rlt_le; exact HlnD_pos).
  assert (Hhbar_nonneg: 0 <= hbar S) by (apply Rlt_le; exact Hhpos).
  (* Psi_hat nonneg from factor nonnegativities *)
  assert (Hpsi_nonneg: 0 <= Psi_hat S (q c) (s c) (i c) c).
  { unfold Psi_hat.
    (* factors: q/(2*opnorm_HA c), s/ln dA, i/(2*ln dmin) are nonnegative *)
    destruct (hcap_div_factors_nonneg S c (q c) (s c) (i c) Hin Hq Hs Hi) as [Hq' [Hs' Hi']].
    apply Rmult_le_pos; [apply Rmult_le_pos; [exact Hq'| exact Hs'] | exact Hi'].
  }
  assert (Hf_nonneg: 0 <= f c).
  { unfold f, K. repeat (apply Rmult_le_pos; try assumption). apply Rlt_le. lra. }
  (* f c <= g c by chaining minima replacement with pointwise with_psi *)
  assert (Hchain: f c <= (hbar S) * (opnorm_HA c) * (ln (INR (dA c))) * (2 * ln (INR S.(dmin))) *
                          Psi_hat S (q c) (s c) (i c) c).
  { (* Use replace_by_min_product with x=y=1 to get A1 <= A2, then scale in monotone steps *)
    set (A1 := (opnorm_min S) * (ln (INR S.(dmin)))).
    set (A2 := (opnorm_HA c) * (ln (INR (dA c)))).
    assert (Hx1: 0 <= 1) by lra.
    assert (Hy1: 0 <= 1) by lra.
    pose proof (replace_by_min_product S c 1 1 Hin Hx1 Hy1) as Hmin.
    simpl in Hmin. unfold A1, A2 in Hmin.
    (* strip *(1*1) to A1 <= A2 *)
    assert (Hmin0: A1 <= A2).
    { replace A1 with (A1 * (1 * 1)) by ring.
      replace A2 with (A2 * (1 * 1)) by ring.
      exact Hmin. }
    (* scale by 2 ln dmin > 0, then by Psi_hat ≥ 0, then by hbar ≥ 0 *)
    assert (Hy_pos: 0 < 2 * ln (INR S.(dmin))) by lra.
    assert (Hstep1: A1 * (2 * ln (INR S.(dmin))) <= A2 * (2 * ln (INR S.(dmin))))
      by (apply Rmult_le_compat_r; [apply Rlt_le; exact Hy_pos| exact Hmin0]).
    assert (Hstep2: A1 * (2 * ln (INR S.(dmin))) * Psi_hat S (q c) (s c) (i c) c
                    <= A2 * (2 * ln (INR S.(dmin))) * Psi_hat S (q c) (s c) (i c) c)
      by (apply Rmult_le_compat_r; [exact Hpsi_nonneg| exact Hstep1]).
    assert (Hstep3: (hbar S) * (A1 * (2 * ln (INR S.(dmin))) * Psi_hat S (q c) (s c) (i c) c)
                    <= (hbar S) * (A2 * (2 * ln (INR S.(dmin))) * Psi_hat S (q c) (s c) (i c) c))
      by (apply Rmult_le_compat_l; [exact Hhbar_nonneg| exact Hstep2]).
    (* reshape to f c and RHS target *)
    unfold f, K.
    replace ((hbar S) * (opnorm_min S) * ln (INR (dmin S)) * (2 * ln (INR (dmin S))) *
              Psi_hat S (q c) (s c) (i c) c)
      with ((hbar S) * (A1 * (2 * ln (INR S.(dmin))) * Psi_hat S (q c) (s c) (i c) c)) by (unfold A1; ring).
    replace ((hbar S) * (opnorm_HA c) * ln (INR (dA c)) * (2 * ln (INR (dmin S))) *
              Psi_hat S (q c) (s c) (i c) c)
      with ((hbar S) * (A2 * (2 * ln (INR S.(dmin))) * Psi_hat S (q c) (s c) (i c) c)) by (unfold A2; ring).
    exact Hstep3. }
  assert (Hmono: (hbar S) * (opnorm_HA c) * (ln (INR (dA c))) * (2 * ln (INR S.(dmin))) *
                   Psi_hat S (q c) (s c) (i c) c
                 <= g c).
  { unfold g.
    apply Rge_le.
    apply (hcap_pointwise_with_psi S c (q c) (s c) (i c) (dE c)); try assumption.
  }
  split; [exact Hf_nonneg | eapply Rle_trans; [exact Hchain | exact Hmono]].
Qed.

