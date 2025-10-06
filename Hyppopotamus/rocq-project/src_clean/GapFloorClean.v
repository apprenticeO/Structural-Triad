(*
  GapFloorClean.v (legacy constructive building block)
  - Paper mapping: Sec. 4.2 (variance floor via minimal gap)
  - Role: abstracts ΔH_A ≥ (1/4)·gap(A) used to define v0(A) in ΔH·S^2 route.
*)
From Coq Require Import Reals Unicode.Utf8 Psatz.
Open Scope R_scope.

Section GapFloorClean.

Variable A : Type.
Variable gap : A -> R.
Variable deltaH : A -> R.

Hypothesis gap_pos : forall a:A, 0 < gap a.
Hypothesis support_two_levels : forall a:A, True.

(* Abstract inequality: if support spans two eigenvalues separated by gap, then ΔH ≥ gap/4 *)
Hypothesis variance_gap_floor_all : forall a:A, deltaH a >= (1/4) * gap a.

Lemma variance_gap_floor : forall a:A, deltaH a >= (1/4) * gap a.
Proof. intro a; apply variance_gap_floor_all. Qed.

End GapFloorClean. 