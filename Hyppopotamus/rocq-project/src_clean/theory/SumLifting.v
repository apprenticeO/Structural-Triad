(*
  theory/SumLifting.v
  Paper mapping: Structural Triad (PDF)
  - Role: General monotone product lift used throughout (triple-product monotonicity).
  - Appears in constructive/universal chains and in Hamiltonian‑capped steps when
    replacing factors by smaller ones under nonnegativity (technical helper lemma).
*)
From Stdlib Require Import Reals Lists.List.
Import ListNotations. Open Scope R_scope.

Lemma mono_prod_3 :
  forall x1 x2 y1 y2 z1 z2,
    0 <= y1 -> 0 <= z1 -> 0 <= x2 -> 0 <= y2 -> 0 <= z2 ->
    x1 >= x2 -> y1 >= y2 -> z1 >= z2 ->
    x1*y1*z1 >= x2*y2*z2.
Proof.
  intros x1 x2 y1 y2 z1 z2 Hy1 Hz1 Hx2 Hy2 Hz2 Hx Hy Hz.
  (* Step 1: scale Hx by y1*z1 >= 0 *)
  assert (Hy1z1_nonneg: 0 <= y1 * z1) by (apply Rmult_le_pos; [exact Hy1| exact Hz1]).
  assert (Hy1z1_nonneg_ge: y1 * z1 >= 0) by (apply Rle_ge; exact Hy1z1_nonneg).
  assert (Hstep1: x1 * (y1 * z1) >= x2 * (y1 * z1)) by (apply Rmult_ge_compat_r; [exact Hy1z1_nonneg_ge|exact Hx]).
  (* Step 2: replace y1 by y2 with x2,z1 nonneg *)
  assert (Hxy: x2 * y1 >= x2 * y2) by (apply Rmult_ge_compat_l; [apply Rle_ge; exact Hx2|exact Hy]).
  assert (Hz1_ge: z1 >= 0) by (apply Rle_ge; exact Hz1).
  assert (Hstep2: (x2 * y1) * z1 >= (x2 * y2) * z1) by (apply Rmult_ge_compat_r; [exact Hz1_ge|exact Hxy]).
  (* Step 3: replace z1 by z2 with x2*y2 nonneg *)
  assert (Hx2y2_nonneg: 0 <= x2 * y2) by (apply Rmult_le_pos; [exact Hx2| exact Hy2]).
  assert (Hx2y2_nonneg_ge: x2 * y2 >= 0) by (apply Rle_ge; exact Hx2y2_nonneg).
  assert (Hstep3: (x2 * y2) * z1 >= (x2 * y2) * z2) by (apply Rmult_ge_compat_l; [exact Hx2y2_nonneg_ge|exact Hz]).
  (* Chain and reassociate *)
  replace (x1 * y1 * z1) with (x1 * (y1 * z1)) by ring.
  replace (x2 * y2 * z2) with ((x2 * y2) * z2) by ring.
  eapply Rge_trans; [exact Hstep1|].
  replace (x2 * (y1 * z1)) with ((x2 * y1) * z1) by ring.
  eapply Rge_trans; [exact Hstep2|]. exact Hstep3.
Qed.
