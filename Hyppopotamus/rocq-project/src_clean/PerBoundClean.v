(*
  PerBoundClean.v (legacy constructive building block)
  - Paper mapping: Sec. 4–6; packages per‑A bounds used to assemble Π_sys ≥ C_sum.
  - Role: collects per‑subsystem inequalities (ΔH, Pinsker, floors) for the ΔH·S^2 route.
  - Legacy note: kept for constructive path; modular triad uses theory/ modules instead.
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.

Section PerBoundClean.

Variable A : Type.

Variable deltaH : A -> R.
Variable S : A -> R.
Variable d : A -> R.

Variable v0 : A -> R.
Variable c_lin : R.

Hypothesis v0_pos : forall a, 0 < v0 a.
Hypothesis c_lin_pos : 0 < c_lin.

(* The variance floor can be supplied by GapFloorClean.variance_gap_floor when a spectral gap is available. *)
Hypothesis var_floor : forall a, deltaH a >= v0 a.
Hypothesis pinsker_linear : forall a, S a >= c_lin * ((d a) * (d a)).
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

Lemma per_bound_le : forall a,
  v0 a * (c_lin * c_lin) * (((d a)*(d a))*((d a)*(d a)))
  <= deltaH a * ((S a)*(S a)).
Proof.
  intro a.
  set (d2 := d a * d a).

  assert (Hd2_nonneg : 0 <= d2).
  { unfold d2; apply Rmult_le_pos; [apply d_nonneg | apply d_nonneg]. }

  assert (Hcld_nonneg : 0 <= c_lin * d2).
  { apply Rmult_le_pos; [apply Rlt_le, c_lin_pos | exact Hd2_nonneg]. }

  assert (Hle : c_lin * d2 <= S a).
  { unfold d2; apply Rge_le; apply pinsker_linear. }

  assert (HS_nonneg : 0 <= S a).
  { eapply Rle_trans; [exact Hcld_nonneg | exact Hle]. }

  (* (c_lin*d2)^2 ≤ (S a)^2 by monotonicity of squaring on nonnegatives *)
  assert (Hsq_le : (c_lin * d2) * (c_lin * d2) <= (S a) * (S a)).
  { apply sq_monotone_nonneg; [exact Hcld_nonneg | exact Hle]. }

  (* Convert left to (c_lin^2)*(d2^2) to match the goal's structure *)
  assert (Hleft_shape : (c_lin * c_lin) * (d2 * d2) <= (S a) * (S a)).
  { replace ((c_lin * c_lin) * (d2 * d2)) with ((c_lin * d2) * (c_lin * d2)) by ring.
    exact Hsq_le. }

  (* Scale by v0 and lift deltaH ≥ v0 *)
  assert (HS2_nonneg : 0 <= (S a) * (S a)).
  { apply Rmult_le_pos; [exact HS_nonneg | exact HS_nonneg]. }

  assert (Hstep1 : v0 a * ((c_lin * c_lin) * (d2 * d2)) <= v0 a * ((S a) * (S a))).
  { apply Rmult_le_compat_l; [apply Rlt_le, v0_pos | exact Hleft_shape]. }

  assert (Hstep2 : v0 a * ((S a) * (S a)) <= deltaH a * ((S a) * (S a))).
  { apply Rmult_le_compat_r; [exact HS2_nonneg | apply Rge_le, var_floor]. }

  (* Reassociate the goal's left side and chain the two monotone steps *)
  rewrite Rmult_assoc.
  eapply Rle_trans; [exact Hstep1 | exact Hstep2].
Qed.

(* Optional linkage: derive var_floor from a gap floor with v0 a = (1/4)*gap a *)
Section GapLink.
  Variable gap : A -> R.
  Hypothesis variance_gap_floor : forall a, deltaH a >= (1/4) * gap a.
  Hypothesis v0_is_quarter_gap : forall a, v0 a = (1/4) * gap a.
  Lemma var_floor_from_gap : forall a, deltaH a >= v0 a.
  Proof.
    intro a. rewrite v0_is_quarter_gap. apply variance_gap_floor.
  Qed.
End GapLink.

End PerBoundClean. 