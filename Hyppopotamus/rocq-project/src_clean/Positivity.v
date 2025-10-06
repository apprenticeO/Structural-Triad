(*
  Positivity.v
  Paper mapping (hyppo_esse_derivation.tex):
  - [Constructive] Section 6: Illustrative positivity scaffold where per-term
    factors are manifestly positive (gap and entropy proxies), implying the
    scaled sum Π_lower > 0 for nonempty lists.
  - Used as a simple sanity/illustrative layer alongside the formal boxed and
    universal results.
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.

Section Positivity.
Variable A : Type.
Variable deltaE_min epsilon : A -> R.
Variable hbar : R. Hypothesis hbar_pos : 0 < hbar.
Hypothesis gap_pos : forall a:A, 0 < deltaE_min a.
Hypothesis ent_pos : forall a:A, 0 < epsilon a.

Definition term (a:A) : R := (1/4) * deltaE_min a * epsilon a * epsilon a.
Definition sum_terms (L:list A) : R := fold_right Rplus 0 (map term L).
Definition Pi_lower (L:list A) : R := (4 / hbar) * sum_terms L.

Lemma term_pos a : 0 < term a.
Proof. unfold term; repeat (apply Rmult_lt_0_compat); try lra;
 [apply gap_pos | apply ent_pos | apply ent_pos]. Qed.

Lemma sum_terms_pos : forall L, L <> [] -> 0 < sum_terms L.
Proof. induction L as [|a L0 IH]; [easy|]. intros _. 
  unfold sum_terms; cbn [map fold_right].
  assert (Tpos:0 < term a) by apply term_pos.
  destruct L0 as [|b L']; cbn [map fold_right].
  - now rewrite Rplus_0_r.
  - assert (IH':0 < sum_terms (b::L')) by (apply IH; discriminate).
    unfold sum_terms in IH'; cbn [map fold_right] in IH'.
    apply Rplus_lt_0_compat; assumption. Qed.

Lemma Pi_lower_pos : forall L, L <> [] -> 0 < Pi_lower L.
Proof. intros L Hne. unfold Pi_lower.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos].
  - apply sum_terms_pos; exact Hne. Qed.

End Positivity.
