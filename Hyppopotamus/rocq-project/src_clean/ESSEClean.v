(*
  ESSEClean.v (legacy scaffold)
  - Paper mapping: Sec. 5 (Averaging/Cesàro arguments used operationally)
  - Role: generic averaging lemma (per_a_avg_lower) used by the ΔH·S^2 constructive route
           (see ESSEUniversal.v) and compatible with the state-agnostic triad variant.
  - State dependence: this file itself is state-agnostic; pure-state identities live in PurityClean.v.
  - Legacy note: kept for the constructive ΔH·S^2 path; modular triad lives under theory/.
*)
From Coq Require Import Reals Psatz.
Open Scope R_scope.

Require Import ESSEClean.TimeAvgClean.

Section ESSEClean.

Variable A : Type.
Variable hbar : R.
Hypothesis hbar_pos : 0 < hbar.

(* Abstract per-subsystem data *)
Variable v0 : A -> R.
Variable c_lin : R.
Variable tau4 : A -> R.
Variable delt : A -> R.  (* density of good times per subsystem *)

Hypothesis v0_pos : forall a, 0 <= v0 a.
Hypothesis c_lin_pos : 0 <= c_lin.
Hypothesis tau4_pos : forall a, 0 <= tau4 a.
Hypothesis delt_in01 : forall a, 0 <= delt a <= 1.

(* Discrete-time per-subsystem signal *)
Variable d4 : A -> nat -> R.     (* proxy for ||...||^4 per time *)
Variable goodA : A -> nat -> bool.  (* times fulfilling both hypotheses *)

Hypothesis d4_nonneg : forall a n, 0 <= d4 a n.
Hypothesis goodA_lower : forall a n, goodA a n = true -> d4 a n >= tau4 a.

Hypothesis density_a : forall a, exists N0, forall n, (n >= N0)%nat ->
  INR (ESSEClean.TimeAvgClean.count_good (fun k => goodA a k) n) >= (delt a) * INR n.

Lemma per_a_avg_lower : forall a,
  exists N1, forall n, (n >= N1)%nat ->
    ESSEClean.TimeAvgClean.avg (fun k => d4 a k) n >= (delt a) * (tau4 a).
Proof.
  intro a.
  set (x := fun k => d4 a k).
  set (g := fun k => goodA a k).
  destruct (density_a a) as [N0 HdA].
  assert (Hx : forall n, 0 <= x n) by (intros n; unfold x; exact (d4_nonneg a n)).
  assert (Hc : 0 <= tau4 a) by apply tau4_pos.
  assert (Hd : 0 <= delt a <= 1) by apply delt_in01.
  assert (Hg : forall n, g n = true -> x n >= tau4 a).
  { intros n Hgn. unfold x, g in *. now apply goodA_lower. }
  assert (Hdens : exists N0, forall n, (n >= N0)%nat ->
                   INR (ESSEClean.TimeAvgClean.count_good g n) >= (delt a) * INR n).
  { exists N0. intros n Hn. specialize (HdA n Hn). exact HdA. }
  eapply ESSEClean.TimeAvgClean.avg_eventual_lower with (x:=x) (good:=g) (c:=tau4 a) (delta:=(delt a)).
  - exact Hx.
  - exact Hc.
  - exact Hg.
  - exact Hdens.
Qed.

End ESSEClean. 