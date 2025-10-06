From Coq Require Import Reals Lists.List Psatz.
Require Import ESSEClean.theory.SystemSpec.
Require Import Coquelicot.Rcomplements.
Open Scope R_scope.

Definition Psi_hat (S: Admissible)
  (sqrtFQ SA IA: R) (c: CutSpec) : R :=
  (sqrtFQ / (2 * opnorm_HA c)) * (SA / ln (INR (dA c))) * (IA / (2 * ln (INR S.(dmin)))).

(* ---------- 1) Nonnegativity ---------- *)

Lemma Psi_hat_nonneg : forall S sqrtFQ SA IA c,
  0 <= sqrtFQ -> 0 <= SA -> 0 <= IA ->
  0 < opnorm_HA c -> 1 < INR (dA c) -> 1 < INR S.(dmin) ->
  0 <= Psi_hat S sqrtFQ SA IA c.
Proof.
  intros S q s i c Hq Hs Hi Hop HdA Hdmin.
  unfold Psi_hat.
  (* factor 1: q / (2‖H‖) >= 0 *)
  assert (D1pos: 0 < 2 * opnorm_HA c) by (apply Rmult_lt_0_compat; [lra| exact Hop]).
  assert (Inv1pos: 0 < / (2 * opnorm_HA c)) by (apply Rinv_0_lt_compat; exact D1pos).
  assert (H1: 0 <= q * (/ (2 * opnorm_HA c)))
    by (apply Rmult_le_pos; [exact Hq | apply Rlt_le; exact Inv1pos]).
  (* factor 2: s / ln dA >= 0 *)
  assert (LnApos: 0 < ln (INR (dA c))) by (assert (Hln1: ln 1 = 0) by apply ln_1; assert (Hlnlt: ln 1 < ln (INR (dA c))) by (apply ln_increasing; [lra|exact HdA]); rewrite Hln1 in Hlnlt; lra).
  assert (Inv2pos: 0 < / ln (INR (dA c))) by (apply Rinv_0_lt_compat; exact LnApos).
  assert (H2: 0 <= s * (/ ln (INR (dA c))))
    by (apply Rmult_le_pos; [exact Hs | apply Rlt_le; exact Inv2pos]).
  (* factor 3: i / (2 ln dmin) >= 0 *)
  assert (Lndminpos: 0 < ln (INR S.(dmin))) by (assert (Hln1: ln 1 = 0) by apply ln_1; assert (Hlnlt: ln 1 < ln (INR S.(dmin))) by (apply ln_increasing; [lra|exact Hdmin]); rewrite Hln1 in Hlnlt; lra).
  assert (D3pos: 0 < 2 * ln (INR S.(dmin))) by (apply Rmult_lt_0_compat; [lra| exact Lndminpos]).
  assert (Inv3pos: 0 < / (2 * ln (INR S.(dmin)))) by (apply Rinv_0_lt_compat; exact D3pos).
  assert (H3: 0 <= i * (/ (2 * ln (INR S.(dmin)))))
    by (apply Rmult_le_pos; [exact Hi | apply Rlt_le; exact Inv3pos]).
  (* conclude *)
  (* Build the triple product step by step *)
  assert (H12: 0 <= (q * / (2 * opnorm_HA c)) * (s * / ln (INR (dA c)))) by (apply Rmult_le_pos; [exact H1|exact H2]).
  apply Rmult_le_pos; [exact H12|exact H3].
Qed.

(* ---------- 2) Upper bound by 1 (need nonnegativity of numerators) ---------- *)

Lemma Psi_hat_le_1 : forall S sqrtFQ SA IA c,
  0 <= sqrtFQ -> 0 <= SA -> 0 <= IA ->
  sqrtFQ <= 2 * opnorm_HA c ->
  SA     <= ln (INR (dA c)) ->
  IA     <= 2 * ln (INR S.(dmin)) ->
  0 < opnorm_HA c -> 1 < INR (dA c) -> 1 < INR S.(dmin) ->
  Psi_hat S sqrtFQ SA IA c <= 1.
Proof.
  intros S q s i c Hq0 Hs0 Hi0 Hq Hs Hi Hop HdA Hdmin.
  unfold Psi_hat.
  (* denominators & inverses positive *)
  assert (D1pos: 0 < 2 * opnorm_HA c) by (apply Rmult_lt_0_compat; [lra| exact Hop]).
  assert (Inv1pos: 0 < / (2 * opnorm_HA c)) by (apply Rinv_0_lt_compat; exact D1pos).
  assert (LnApos: 0 < ln (INR (dA c))) by (assert (Hln1: ln 1 = 0) by apply ln_1; assert (Hlnlt: ln 1 < ln (INR (dA c))) by (apply ln_increasing; [lra|exact HdA]); rewrite Hln1 in Hlnlt; lra).
  assert (Inv2pos: 0 < / ln (INR (dA c))) by (apply Rinv_0_lt_compat; exact LnApos).
  assert (Lndminpos: 0 < ln (INR S.(dmin))) by (assert (Hln1: ln 1 = 0) by apply ln_1; assert (Hlnlt: ln 1 < ln (INR S.(dmin))) by (apply ln_increasing; [lra|exact Hdmin]); rewrite Hln1 in Hlnlt; lra).
  assert (D3pos: 0 < 2 * ln (INR S.(dmin))) by (apply Rmult_lt_0_compat; [lra| exact Lndminpos]).
  assert (Inv3pos: 0 < / (2 * ln (INR S.(dmin)))) by (apply Rinv_0_lt_compat; exact D3pos).
  (* normalize: use products not divisions *)
  set (a := (/ (2 * opnorm_HA c)) * q).
  set (b := (/ ln (INR (dA c))) * s).
  set (d := (/ (2 * ln (INR S.(dmin)))) * i).
  (* 0 ≤ a,b,d *)
  assert (a_ge0: 0 <= a) by (subst a; apply Rmult_le_pos; [apply Rlt_le; exact Inv1pos| exact Hq0]).
  assert (b_ge0: 0 <= b) by (subst b; apply Rmult_le_pos; [apply Rlt_le; exact Inv2pos| exact Hs0]).
  assert (d_ge0: 0 <= d) by (subst d; apply Rmult_le_pos; [apply Rlt_le; exact Inv3pos| exact Hi0]).
  (* a ≤ 1 *)
  assert (a_le1: a <= 1).
  { subst a.
    assert (Hstep: / (2 * opnorm_HA c) * q <= / (2 * opnorm_HA c) * (2 * opnorm_HA c)).
    { apply Rmult_le_compat_l; [apply Rlt_le; exact Inv1pos| exact Hq]. }
    rewrite Rinv_l in Hstep; [exact Hstep | lra]. }
  (* b ≤ 1 *)
  assert (b_le1: b <= 1).
  { subst b.
    assert (Hstep: / ln (INR (dA c)) * s <= / ln (INR (dA c)) * ln (INR (dA c))).
    { apply Rmult_le_compat_l; [apply Rlt_le; exact Inv2pos| exact Hs]. }
    rewrite Rinv_l in Hstep; [exact Hstep | lra]. }
  (* d ≤ 1 *)
  assert (d_le1: d <= 1).
  { subst d.
    assert (Hstep: / (2 * ln (INR (dmin S))) * i <= / (2 * ln (INR (dmin S))) * (2 * ln (INR (dmin S)))).
    { apply Rmult_le_compat_l; [apply Rlt_le; exact Inv3pos| exact Hi]. }
    rewrite Rinv_l in Hstep; [exact Hstep | lra]. }
  (* chain: a*b ≤ 1, then (a*b)*d ≤ 1 *)
  assert (ab_le1 : a * b <= 1).
  { assert (Hstep1 : a * b <= 1 * b) by (apply Rmult_le_compat_r; [exact b_ge0| exact a_le1]).
    replace (1 * b) with b in Hstep1 by ring.
    eapply Rle_trans; [exact Hstep1| exact b_le1]. }
  assert (abd_le1 : (a * b) * d <= 1).
  { assert (Hstep2 : (a * b) * d <= 1 * d) by (apply Rmult_le_compat_r; [exact d_ge0| exact ab_le1]).
    replace (1 * d) with d in Hstep2 by ring.
    eapply Rle_trans; [exact Hstep2| exact d_le1]. }
  (* convert back to divisions and conclude *)
  unfold Rdiv; simpl.
  (* Rewrite the goal to match a * b * d *)
  assert (Hgoal: q * / (2 * opnorm_HA c) * (s * / ln (INR (dA c))) * (i * / (2 * ln (INR (dmin S)))) = a * b * d).
  { subst a b d. ring. }
  rewrite Hgoal.
  exact abd_le1.
Qed.