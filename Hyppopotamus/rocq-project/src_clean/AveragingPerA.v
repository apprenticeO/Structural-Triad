(*
  AveragingPerA.v (legacy constructive averaging)
  Paper mapping: Structural Triad (PDF) Sec. 5 (Operational Metrics and Averaging): δ_A and τ_A^4 schema.
  - Role: converts pointwise lower bounds at good indices into Cesàro average floors.
*)
From Coq Require Import Reals Arith Psatz Lia.
Open Scope R_scope.

Section AveragingPerA.

(* Paper cross-ref [PerA+Avg]: x is the per-sample contribution proxy; good marks good times. *)
Variable x : nat -> R.
Variable good : nat -> bool.
Variable tauA : R.
Variable deltaA : R.

Hypothesis x_nonneg : forall n, 0 <= x n.
Hypothesis tauA_nonneg : 0 <= tauA.
Hypothesis deltaA_range : 0 <= deltaA <= 1.
Hypothesis good_lower : forall n, good n = true -> x n >= tauA.

(* Recurrences for prefix sums and counts of good indices. *)
Fixpoint sum_prefix (n:nat) : R :=
  match n with
  | O => 0
  | S k => sum_prefix k + x k
  end.

Fixpoint count_good (n:nat) : nat :=
  match n with
  | O => 0
  | S k => count_good k + (if good k then 1 else 0)
  end.

(* Paper cross-ref [PerA+Avg]: Lower bound sum_prefix by tauA times count_good. *)
Lemma sum_prefix_lower: forall n,
  sum_prefix n >= tauA * INR (count_good n).
Proof.
  induction n as [|k IH]; simpl; [lra|].
  destruct (good k) eqn:Gk.
  - assert (Hxk: x k >= tauA) by (apply good_lower; exact Gk).
    replace (INR (count_good k + 1)) with (INR (count_good k) + 1) by (rewrite plus_INR; simpl; lra).
    lra.
  - assert (Hxk0: 0 <= x k) by apply x_nonneg.
    replace (INR (count_good k + 0)) with (INR (count_good k)) by (rewrite plus_INR; simpl; lra).
    lra.
Qed.

(* Cesàro average definition for prefixes. *)
Definition avg (n:nat) : R :=
  match n with
  | O => 0
  | S k => sum_prefix (S k) / INR (S k)
  end.

(* Paper cross-ref [PerA+Avg]: Hypothesis that density of good indices ≥ deltaA eventually. *)
Hypothesis density_lower_eventual : exists N0:nat, forall n:nat, (n >= N0)%nat ->
  INR (count_good n) >= deltaA * INR n.

(* Paper cross-ref [PerA+Avg]: Eventual average lower bound avg(n) ≥ deltaA * tauA. *)
Lemma avg_eventual_lower_perA : exists N1:nat, forall n, (n >= N1)%nat -> avg n >= deltaA * tauA.
Proof.
  destruct density_lower_eventual as [N0 Hdens].
  exists (Nat.max N0 1). intros n Hn.
  destruct n as [|k].
  - lia.
  - assert (Hn': (S k >= N0)%nat) by (apply Nat.le_trans with (m:=Nat.max N0 1); [lia|exact Hn]).
    specialize (Hdens (S k) Hn').
    unfold avg. simpl.
    set (den := INR (S k)).
    assert (Hden_pos: 0 < den) by (unfold den; apply lt_0_INR; lia).
    assert (Hsum_ge: sum_prefix (S k) >= tauA * INR (count_good (S k))) by apply sum_prefix_lower.
    assert (Hsum_le: tauA * INR (count_good (S k)) <= sum_prefix (S k)) by (apply Rge_le; exact Hsum_ge).
    assert (Hdens_le: deltaA * den <= INR (count_good (S k))) by (apply Rge_le; exact Hdens).
    (* Divide by den > 0 *)
    assert (Hsum_div_le: tauA * (INR (count_good (S k)) * / den) <= sum_prefix (S k) * / den).
    { apply Rle_trans with (r2 := (tauA * INR (count_good (S k))) * / den).
      - right. rewrite Rmult_assoc. reflexivity.
      - apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact Hden_pos|exact Hsum_le]. }
    assert (Hdens_div_le: deltaA <= INR (count_good (S k)) * / den).
    { apply Rle_trans with (r2 := (deltaA * den) * / den).
      - right. field; lra.
      - apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact Hden_pos|exact Hdens_le]. }
    (* Chain: deltaA*tauA <= tauA*(INR/den) <= sum_prefix/den *)
    assert (Hdc_le_cfrac: deltaA * tauA <= tauA * (INR (count_good (S k)) * / den)).
    { rewrite Rmult_comm. exact (Rmult_le_compat_l _ _ _ tauA_nonneg Hdens_div_le). }
    apply Rle_ge.
    eapply Rle_trans; [exact Hdc_le_cfrac|].
    replace (sum_prefix (S k) / den) with (sum_prefix (S k) * / den) by (unfold Rdiv; lra).
    eapply Rle_trans; [exact Hsum_div_le|].
    apply Rle_refl.
Qed.

(* Note: deltaA corresponds to lower density of good times for A, and tauA to a sustained lower magnitude on those times, as in the paper's density/infimum construction on K. *)
End AveragingPerA. 