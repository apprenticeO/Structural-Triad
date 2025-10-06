(*
  TimeAvgClean.v (legacy constructive averaging)
  - Paper mapping: Sec. 5 (Operational Metrics and Averaging): δ_A density and sustained contributions.
  - Role: generic Cesàro averaging pattern used in the ΔH·S^2 route; reused by triad variant.
*)
From Coq Require Import Reals Arith Psatz.
From Coq Require Import Lia.
Open Scope R_scope.

Section TimeAvgClean.

(* Abstract sequence x(n) and a boolean predicate good(n) for “good times”. *)
Variable x : nat -> R.
Variable good : nat -> bool.
Variable c delta : R.

Hypothesis x_nonneg : forall n, 0 <= x n.
Hypothesis c_nonneg : 0 <= c.
Hypothesis delta_range : 0 <= delta <= 1.
Hypothesis good_lower : forall n, good n = true -> x n >= c.

(* Prefix sum and count of good indices. *)
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

(* Paper cross-ref [PerA+Avg]: sum_prefix ≥ c · (# good), pointwise-to-sum step. *)
Lemma sum_prefix_lower: forall n,
  sum_prefix n >= c * INR (count_good n).
Proof.
  induction n as [|k IH]; simpl; [lra|].
  destruct (good k) eqn:Gk.
  - (* good k = true: use good_lower to inject c at index k *)
    assert (Hxk: x k >= c) by (apply good_lower; exact Gk).
    replace (INR (count_good k + 1)) with (INR (count_good k) + 1) by (rewrite plus_INR; simpl; lra).
    lra.
  - (* good k = false: contribute only nonnegativity of x k *)
    assert (Hxk0: 0 <= x k) by apply x_nonneg.
    replace (INR (count_good k + 0)) with (INR (count_good k)) by (rewrite plus_INR; simpl; lra).
    lra.
Qed.

(* Cesàro average over prefixes. *)
Definition avg (n:nat) : R :=
  match n with
  | O => 0
  | S k => sum_prefix (S k) / INR (S k)
  end.

(* Paper cross-ref [PerA+Avg]: density hypothesis — asymptotic frequency of good indices ≥ δ. *)
Hypothesis density_lower_eventual : exists N0:nat, forall n:nat, (n >= N0)%nat ->
  INR (count_good n) >= delta * INR n.

(* Paper cross-ref [PerA+Avg]: eventual average lower bound avg(n) ≥ δ · c. *)
Lemma avg_eventual_lower: exists N1:nat, forall n, (n >= N1)%nat -> avg n >= delta * c.
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
    assert (Hsum_ge: sum_prefix (S k) >= c * INR (count_good (S k))) by apply sum_prefix_lower.
    assert (Hsum_le: c * INR (count_good (S k)) <= sum_prefix (S k)) by (apply Rge_le; exact Hsum_ge).
    assert (Hdens_le: delta * den <= INR (count_good (S k))) by (apply Rge_le; exact Hdens).
    (* Divide both inequalities by den > 0 and chain *)
    assert (Hsum_div_le: c * (INR (count_good (S k)) * / den) <= sum_prefix (S k) * / den).
    { apply Rle_trans with (r2 := (c * INR (count_good (S k))) * / den).
      - right. rewrite Rmult_assoc. reflexivity.
      - apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact Hden_pos|exact Hsum_le]. }
    assert (Hdens_div_le: delta <= INR (count_good (S k)) * / den).
    { apply Rle_trans with (r2 := (delta * den) * / den).
      - right. field; lra.
      - apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact Hden_pos|exact Hdens_le]. }
    (* Chain: delta*c ≤ c*(INR/den) ≤ sum_prefix/den *)
    assert (Hdc_le_cfrac: delta * c <= c * (INR (count_good (S k)) * / den)).
    { rewrite Rmult_comm. exact (Rmult_le_compat_l _ _ _ c_nonneg Hdens_div_le). }
    apply Rle_ge.
    eapply Rle_trans; [exact Hdc_le_cfrac|].
    replace (sum_prefix (S k) / den) with (sum_prefix (S k) * / den) by (unfold Rdiv; lra).
    eapply Rle_trans; [exact Hsum_div_le|].
    apply Rle_refl.
Qed.

End TimeAvgClean. 