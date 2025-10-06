(*
  PinskerSquaredClean.v (legacy constructive building block)
  - Paper mapping: Sec. 4.1 (square-and-align step under nats; I=2S used upstream).
  - Role: packages S_A^2 ≥ (c_lin^2) · ||·||_1^4 for ΔH·S^2 route.
*)
From Coq Require Import Reals Unicode.Utf8 Psatz.
Open Scope R_scope.

Section PinskerSquaredClean.

Variable A : Type.
Variable S : A -> R.
Variable d : A -> R.
Variable c_lin : R.

Hypothesis c_lin_pos : 0 < c_lin.
Hypothesis pinsker_linear : forall a, S a >= c_lin * (d a * d a).
Hypothesis d_nonneg : forall a, 0 <= d a.

Lemma sq_monotone_nonneg : forall x y, 0 <= x -> x <= y -> x*x <= y*y.
Proof.
  intros x y Hx Hxy.
  assert (Hxxy : x*x <= x*y) by (apply Rmult_le_compat_l; [exact Hx|exact Hxy]).
  assert (Hxyy : x*y <= y*y).
  { apply Rmult_le_compat_r.
    - eapply Rle_trans; [exact Hx| exact Hxy].
    - exact Hxy.
  }
  lra.
Qed.

Lemma pinsker_squared : forall a,
  (c_lin * c_lin) * (d a * d a * (d a * d a)) <= S a * S a.
Proof.
  intro a.
  set (d2 := d a * d a).
  assert (Hd2_nonneg : 0 <= d2) by (unfold d2; apply Rmult_le_pos; [apply d_nonneg | apply d_nonneg]).
  assert (Hcld_nonneg : 0 <= c_lin * d2) by (apply Rmult_le_pos; [apply Rlt_le, c_lin_pos | exact Hd2_nonneg]).
  assert (Hle : c_lin * d2 <= S a) by (unfold d2; apply Rge_le, pinsker_linear).
  (* Square monotonicity on nonnegative side *)
  assert (Hsq : (c_lin * d2) * (c_lin * d2) <= S a * S a) by (apply sq_monotone_nonneg; [exact Hcld_nonneg | exact Hle]).
  (* Align left shape by ring and conclude *)
  replace ((c_lin * c_lin) * (d a * d a * (d a * d a))) with ((c_lin * c_lin) * (d2 * d2)) by (unfold d2; ring).
  replace ((c_lin * c_lin) * (d2 * d2)) with ((c_lin * d2) * (c_lin * d2)) by ring.
  exact Hsq.
Qed.

End PinskerSquaredClean. 