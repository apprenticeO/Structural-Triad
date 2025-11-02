(*
  PiClean.v
  Paper mapping (Structural Triad, PDF):
  - [Activity] Section 3: Π_sys(t) = (4/ħ) Σ_A ΔH_A(t) · S_A(t)^2 (π-baseline via I=2S and √F ≤ 2ΔH).
  - This module packages positivity claims for Π_sys given ΔH_A>0 and S_A>0.

  Notes:
  - Π_sys here is an abstract instantaneous form (no time integration). The time-averaged
    version in the derivation uses liminf and Section 5 averaging to obtain sustained floors.
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.

Section PiClean.

Variable A : Type.
Variable deltaH : A -> R.
Variable S : A -> R.
Variable hbar : R.
Hypothesis hbar_pos : 0 < hbar.
Hypothesis deltaH_pos : forall a, 0 < deltaH a.
Hypothesis S_pos : forall a, 0 < S a.

(* Paper cross-ref [Activity]: term corresponds to ΔH_A · S_A^2. *)
Definition term (a:A) : R := deltaH a * (S a * S a).
(* Π_sys: (4/ħ) scaling of the per-A sum. *)
Definition Pi_sys (L:list A) : R := (4 / hbar) * fold_right Rplus 0 (map term L).

Lemma term_pos a : 0 < term a.
Proof.
  unfold term.
  apply Rmult_lt_0_compat.
  - apply deltaH_pos.
  - (* (S a)*(S a) > 0 *)
    apply Rmult_lt_0_compat; apply S_pos.
Qed.

(* Paper cross-ref [Activity]: if each term is strictly positive, the sum and Π_sys are. *)
Lemma sum_terms_pos : forall L, L <> [] -> 0 < fold_right Rplus 0 (map term L).
Proof.
  induction L as [|a L0 IH]; [easy|]. intros _. simpl.
  assert (Tpos:0 < term a) by apply term_pos.
  destruct L0 as [|b L']; simpl.
  - now rewrite Rplus_0_r.
  - assert (IH': 0 < fold_right Rplus 0 (map term (b::L'))) by (apply IH; discriminate).
  simpl in IH'. apply Rplus_lt_0_compat; assumption.
Qed.

Lemma Pi_sys_pos : forall L, L <> [] -> 0 < Pi_sys L.
Proof.
  intros L Hne. unfold Pi_sys.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [lra| apply Rinv_0_lt_compat; exact hbar_pos].
  - apply sum_terms_pos; exact Hne.
Qed.

End PiClean. 