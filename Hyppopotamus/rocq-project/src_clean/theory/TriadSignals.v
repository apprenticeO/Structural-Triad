(*
  theory/TriadSignals.v
  Paper mapping: Structural Triad (PDF)
  - Section 2 (Quantum Structural Triad: Definition): discrete-time triad signals rA,sA,iA
    and the per-cut good-epoch predicate.
  - Technical Lemmas (density-to-time-average): used via TimeAvgClean to obtain
    eventual lower bounds from positive-density good epochs.
  - Role: Modular, system-agnostic shell for per-cut triad signals with leg-wise floors
    (epsR0, epsS0, epsI0) and a density floor delta_cut, yielding an eventual average
    lower bound for the product signal PsiA_triad on each admissible cut.
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.
Require Import ESSEClean.TimeAvgClean.
Require Import ESSEClean.theory.SystemSpec.

Section TriadSignals.
Context (S: Admissible).

Variable rA_t sA_t iA_t : CutSpec -> nat -> R.
Variable goodA_t : CutSpec -> nat -> bool.

Variable epsR0 epsS0 epsI0 : CutSpec -> R.
Variable delta_cut : CutSpec -> R.

Hypothesis rA_nonneg : forall c n, 0 <= rA_t c n.
Hypothesis sA_nonneg : forall c n, 0 <= sA_t c n.
Hypothesis iA_nonneg : forall c n, 0 <= iA_t c n.
Hypothesis epsR_nonneg : forall c, 0 <= epsR0 c.
Hypothesis epsS_nonneg : forall c, 0 <= epsS0 c.
Hypothesis epsI_nonneg : forall c, 0 <= epsI0 c.
Hypothesis deltaA_range : forall c, 0 <= delta_cut c <= 1.

Hypothesis good_lower_r : forall c n, goodA_t c n = true -> rA_t c n >= epsR0 c.
Hypothesis good_lower_s : forall c n, goodA_t c n = true -> sA_t c n >= epsS0 c.
Hypothesis good_lower_i : forall c n, goodA_t c n = true -> iA_t c n >= epsI0 c.

Hypothesis density_lower_eventual : forall c, exists N0:nat, forall n:nat, (n >= N0)%nat ->
  INR (ESSEClean.TimeAvgClean.count_good (fun k => goodA_t c k) n) >= (delta_cut c) * INR n.

Definition PsiA_triad (c:CutSpec) (n:nat) : R := rA_t c n * (sA_t c n * iA_t c n).

Lemma psi_triad_lower_on_good : forall c n, goodA_t c n = true ->
  PsiA_triad c n >= (epsR0 c) * (epsS0 c * epsI0 c).
Proof.
  intros c n Hg. unfold PsiA_triad.
  pose proof (good_lower_r c n Hg) as Hr.
  pose proof (good_lower_s c n Hg) as Hs.
  pose proof (good_lower_i c n Hg) as Hi.
  pose proof (rA_nonneg c n) as Hr0.
  pose proof (sA_nonneg c n) as Hs0.
  pose proof (iA_nonneg c n) as Hi0.
  apply Rle_ge.
  assert (HstepA : (epsR0 c) * (epsS0 c * epsI0 c) <= rA_t c n * (epsS0 c * epsI0 c)).
  { apply Rmult_le_compat_r.
    - apply Rmult_le_pos; [apply epsS_nonneg | apply epsI_nonneg].
    - apply Rge_le; exact Hr. }
  assert (HB1 : (epsS0 c) * (epsI0 c) <= sA_t c n * (epsI0 c)).
  { apply Rmult_le_compat_r; [apply epsI_nonneg | apply Rge_le; exact Hs]. }
  assert (HB2 : sA_t c n * (epsI0 c) <= sA_t c n * iA_t c n).
  { apply Rmult_le_compat_l; [exact Hs0| apply Rge_le; exact Hi]. }
  assert (HstepB : (epsS0 c) * (epsI0 c) <= sA_t c n * iA_t c n) by (eapply Rle_trans; [exact HB1|exact HB2]).
  assert (HstepB2 : rA_t c n * (epsS0 c * epsI0 c) <= rA_t c n * (sA_t c n * iA_t c n)).
  { apply Rmult_le_compat_l; [exact Hr0| exact HstepB]. }
  eapply Rle_trans; [exact HstepA| exact HstepB2].
Qed.

Lemma triad_avg_eventual_lower_perA : forall c,
  exists N1:nat, forall n, (n >= N1)%nat ->
    ESSEClean.TimeAvgClean.avg (fun k => PsiA_triad c k) n >= (delta_cut c) * ((epsR0 c) * (epsS0 c * epsI0 c)).
Proof.
  intro c. set (x := fun k => PsiA_triad c k). set (g := fun k => goodA_t c k). set (cc := (epsR0 c) * (epsS0 c * epsI0 c)).
  assert (Hx_nonneg : forall n, 0 <= x n).
  { intro n. unfold x, PsiA_triad. apply Rmult_le_pos; [apply rA_nonneg|]. apply Rmult_le_pos; [apply sA_nonneg|apply iA_nonneg]. }
  assert (Hc_nonneg : 0 <= cc).
  { unfold cc. apply Rmult_le_pos; [apply epsR_nonneg|]. apply Rmult_le_pos; [apply epsS_nonneg|apply epsI_nonneg]. }
  assert (Hgood_lower : forall n, g n = true -> x n >= cc) by (intros n Hg; unfold x, cc; apply psi_triad_lower_on_good; exact Hg).
  destruct (density_lower_eventual c) as [N0 Hd].
  eapply ESSEClean.TimeAvgClean.avg_eventual_lower with (x:=x) (good:=g) (c:=cc) (delta:=(delta_cut c)). all: eauto.
Qed.

End TriadSignals.
