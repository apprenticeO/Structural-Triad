(*
  theory/SystemSpec.v
  Paper mapping: Structural Triad (PDF)
  - Role: System interface for admissible cut-sets and hardware scales used by
    normalization and Hamiltonian-capped results.
  - Sections:
    * Normalized Intensive Triad (§ Intensive Formulation): uses dA, dmin, opnorm_HA.
    * Hamiltonian‑Capped Structural Threshold (Thm. HCap): "replace by minima" and
      cut‑set averaging appear here as helpers (E_card, ln monotonicity, opnorm minima).
  - Provides: records CutSpec and Admissible; average over cuts; log/opnorm monotonicity
    lemmas; and small utilities for minima replacement.
*)
From Coq Require Import Reals Lists.List Lia Ranalysis1 Rfunctions Arith.PeanoNat Arith.

From Coq Require Import micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* ---------- Structures ---------- *)

Record CutSpec := {
  dA : nat;                  (* local Hilbert dim d_A *)
  H_A : Type;                (* opaque witness for local generator *)
  opnorm_HA : R              (* ‖H_A‖_op *)
}.

Record Admissible := {
  hbar             : R;              hbar_pos       : 0 < hbar;
  cuts             : list CutSpec;   cuts_nonempty  : cuts <> [];
  dmin             : nat;            dmin_le        : forall c, In c cuts -> (dmin <= dA c)%nat;
  dmin_ge_2        : (2 <= dmin)%nat;                           (* ensures ln(INR dmin) > 0 *)
  opnorm_min       : R;              opnorm_le      : forall c, In c cuts -> opnorm_min <= opnorm_HA c;
  opnorm_min_pos   : 0 < opnorm_min                             (* positive scale for normalization *)
}.

(* ---------- Convenience defs & immediate consequences ---------- *)

Definition E_card (S: Admissible) : R := INR (length S.(cuts)).

(* prefer remember/case_eq to destruct S.(cuts) directly *)
Lemma INR_S_pos (n:nat) : 0 < INR (S n).
Proof. rewrite S_INR. assert (0 <= INR n) by apply pos_INR. lra. Qed.

Lemma E_card_pos : forall S: Admissible, 0 < E_card S.
Proof.
  intros S. unfold E_card.
  remember (cuts S) as L eqn:HL. destruct L as [|c cs].
  - exfalso. apply (cuts_nonempty S). now rewrite HL.
  - apply INR_S_pos.
Qed.

Lemma dA_ge_2 : forall (S:Admissible) c, In c S.(cuts) -> (2 <= dA c)%nat.
Proof.
  intros S c Hin.
  apply Nat.le_trans with (m := S.(dmin)); [apply S.(dmin_ge_2)|apply S.(dmin_le); assumption].
Qed.

(* ---------- Log-monotonicity helpers ---------- *)

Lemma ln_INR_monotone :
  forall m n, (2 <= m)%nat -> (m <= n)%nat -> ln (INR m) <= ln (INR n).
Proof.
  intros m n Hm2 Hmn.
  destruct (Rtotal_order (INR m) (INR n)) as [Hlt | [Heq | Hgt]].
  + (* INR m < INR n *)
    assert (Hlnlt: ln (INR m) < ln (INR n)).
    { apply ln_increasing.
      - assert (0 < INR m) by (apply lt_0_INR; lia). exact H.
      - exact Hlt. }
    apply Rlt_le; exact Hlnlt.
  + (* INR m = INR n *)
    rewrite Heq. apply Rle_refl.
  + (* INR m > INR n contradicts m <= n *)
    exfalso. apply le_INR in Hmn. apply Rlt_not_le in Hgt. apply Hgt. exact Hmn.
Qed.

Lemma ln_dmin_le_lndA :
  forall (S:Admissible) c, In c S.(cuts) -> ln (INR S.(dmin)) <= ln (INR (dA c)).
Proof.
  intros S c Hin. apply ln_INR_monotone; [apply S.(dmin_ge_2)|].
  apply S.(dmin_le); exact Hin.
Qed.

Lemma ln_dmin_pos : forall S:Admissible, 0 < ln (INR S.(dmin)).
Proof.
  intro S.
  assert (Hdmin2 : (2 <= S.(dmin))%nat) by apply S.(dmin_ge_2).
  assert (Hgt1 : 1 < INR S.(dmin)).
  { replace 1 with (INR 1) by reflexivity.
    eapply Rlt_le_trans with (r2:=INR 2); [simpl; lra|].
    apply le_INR in Hdmin2; exact Hdmin2. }
  assert (Hln1: ln 1 = 0) by apply ln_1.
  assert (Hlnlt: ln 1 < ln (INR S.(dmin))) by (apply ln_increasing; [lra|exact Hgt1]).
  rewrite Hln1 in Hlnlt. lra.
Qed.
(* ---------- “Replace by minima” one-liners ---------- *)

Lemma replace_by_min_opnorm :
  forall (S:Admissible) c (x:R),
    0 <= x -> In c S.(cuts) ->
    opnorm_min S * x <= opnorm_HA c * x.
Proof.
  intros S c x Hx Hin.
  apply Rmult_le_compat_r; [assumption|].
  apply S.(opnorm_le); exact Hin.
Qed.

Lemma replace_by_min_ln :
  forall (S:Admissible) c (x:R),
    0 <= x -> In c S.(cuts) ->
    (ln (INR S.(dmin))) * x <= (ln (INR (dA c))) * x.
Proof.
  intros S c x Hx Hin.
  apply Rmult_le_compat_r; [assumption|].
  apply ln_dmin_le_lndA; exact Hin.
Qed.

(* ---------- Small utilities for destructing cuts S safely ---------- *)

Lemma cuts_cons_or_nil S :
  (exists c cs, cuts S = c :: cs) \/ cuts S = [].
Proof. destruct (cuts S) as [|c cs]; [right; reflexivity | left; eauto]. Qed.

(* ---------- Example instance to sanity-check obligations ---------- *)

Program Definition c1 : CutSpec := {| dA := 2; H_A := unit; opnorm_HA := 1 |}.
Program Definition c2 : CutSpec := {| dA := 3; H_A := unit; opnorm_HA := 1.5 |}.

Definition S_ex : Admissible.
refine {| hbar := 1; hbar_pos := _;
          cuts := [c1; c2]; cuts_nonempty := _;
          dmin := 2; dmin_le := _; dmin_ge_2 := _;
          opnorm_min := 1; opnorm_le := _; opnorm_min_pos := _ |}.
- lra.
- intro H; discriminate.
- intros c Hin. simpl in Hin. destruct Hin as [Hc1 | [Hc2 | []]]; subst; simpl; lia.
- lia.
- intros c Hin. simpl in Hin. destruct Hin as [Hc1 | [Hc2 | []]]; subst; simpl; lra.
- lra.
Defined.

(* ---------- Average over cuts & monotone lifting ---------- *)

Definition avg_over_cuts (S:Admissible) (f: CutSpec -> R) : R :=
  (1 / E_card S) * fold_right Rplus 0 (map f S.(cuts)).

Lemma avg_mono_nonneg :
  forall S f g,
    (forall c, In c S.(cuts) -> 0 <= f c /\ f c <= g c) ->
    avg_over_cuts S f <= avg_over_cuts S g.
Proof.
  intros S f g H. unfold avg_over_cuts.
  apply Rmult_le_compat_l.
  - (* (1 / |E|) >= 0 *)
    replace (1 / E_card S) with (/ E_card S) by (unfold Rdiv; ring).
    apply Rlt_le, Rinv_0_lt_compat, E_card_pos.
  - (* sum monotonicity under pointwise bounds *)
    revert H. induction (cuts S) as [|c cs IH]; intros H; simpl.
    + lra.
    + assert (Hc : 0 <= f c /\ f c <= g c) by (apply H; left; reflexivity).
      destruct Hc as [Hf Hle].
      specialize (IH (fun c' Hin' => H c' (or_intror Hin'))).
      lra.
Qed.

(* ---------- Optional notation ---------- *)

Notation "‖H_A‖ₘᵢₙ" := (opnorm_min) (at level 10).
Notation "|E|" := (E_card) (at level 10).
