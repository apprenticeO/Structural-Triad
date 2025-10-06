(*
  ESSEUniversal.v (legacy constructive ΔH·S^2 route)
  - Paper mapping: Sec. 3–6 (Activity, Pinsker, Variance floor, Averaging, Constructive & Universal floors)
  - Role: builds Π_sys ≥ C_sum via ΔH_A · S_A^2 with Pinsker and minima witnesses.
  - State dependence: relies on pure-state identity I=2 S_A upstream (see PurityClean.v) and √F ≤ 2ΔH.
  - Legacy note: kept for the constructive path; the state-agnostic triad lives in ESSEUniversal_structure.v and theory/ modules.
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.

Require Import ESSEClean.ESSEList.

Section ESSEUniversal.

Variable A : Type.
Variable hbar : R. Hypothesis hbar_pos : 0 < hbar.

(* Paper cross-ref [Notation/System]: Sections 1–2. *)
(* A: subsystem index type; hbar: reduced Planck constant. *)

(* Per-subsystem quantities as in ESSEList *)
Variable deltaH : A -> R.
Variable S : A -> R.
Variable v0 : A -> R.
Variable c_lin : R.
Variable deltaA : A -> R.
Variable tau4 : A -> R.

Hypothesis v0_pos : forall a, 0 < v0 a.
Hypothesis c_lin_pos : 0 < c_lin.
Hypothesis deltaA_range : forall a, 0 <= deltaA a <= 1.
Hypothesis tau4_nonneg : forall a, 0 <= tau4 a.

(* Paper cross-ref [Pinsker+Floor]: Eq. (4.2) perA-combined.
   per_bound encodes ΔH_A · S_A^2 ≥ v0(A)·c_lin^2·(δ_A·τ_A^4),
   where in nats one may take c_lin = 1/4 so c_lin^2 = 1/16 (Pinsker with I=2S),
   v0(A)=δE_min(A)/4, and (δ_A, τ_A^4) from averaging. *)
Hypothesis per_bound : forall a, deltaH a * (S a * S a) >= v0 a * (c_lin * c_lin) * (deltaA a * tau4 a).

(* Paper cross-ref [Activity]: Eq. (3.2) π-baseline via purity I=2S and √F ≤ 2ΔH. *)
Definition termLHS (a:A) : R := deltaH a * (S a * S a).
(* Paper cross-ref [Pinsker+Floor]+[PerA+Avg]: RHS building blocks matching perA-combined. *)
Definition termRHS (a:A) : R := v0 a * (c_lin * c_lin) * (deltaA a * tau4 a).
(* Π_sys: Section 3 aggregation over A; C_sum: Section 6 sum form. *)
Definition Pi_sys (L:list A) : R := (4 / hbar) * fold_right Rplus 0 (map termLHS L).
Definition C_sum (L:list A) : R := (4 / hbar) * fold_right Rplus 0 (map termRHS L).

Lemma termRHS_nonneg : forall a, 0 <= termRHS a.
Proof.
  intro a. unfold termRHS.
  (* Gather nonnegativities *)
  assert (Hv0 : 0 <= v0 a) by (apply Rlt_le, v0_pos).
  assert (Hcl2 : 0 <= c_lin * c_lin) by (apply Rmult_le_pos; apply Rlt_le; exact c_lin_pos).
  destruct (deltaA_range a) as [Hdel _].
  assert (Htau : 0 <= tau4 a) by apply tau4_nonneg.
  (* Build product nonnegativity step by step *)
  assert (H12 : 0 <= v0 a * (c_lin * c_lin)) by (apply Rmult_le_pos; assumption).
  assert (H123 : 0 <= (v0 a * (c_lin * c_lin)) * deltaA a) by (apply Rmult_le_pos; [assumption|exact Hdel]).
  assert (H1234 : 0 <= (v0 a * (c_lin * c_lin) * deltaA a) * tau4 a) by (apply Rmult_le_pos; [exact H123|exact Htau]).
  replace (v0 a * (c_lin * c_lin) * (deltaA a * tau4 a)) with ((v0 a * (c_lin * c_lin) * deltaA a) * tau4 a) by ring.
  exact H1234.
Qed.

Lemma sum_termRHS_nonneg : forall L, 0 <= fold_right Rplus 0 (map termRHS L).
Proof.
  induction L as [|a L0 IH]; simpl; [lra|].
  assert (Ha: 0 <= termRHS a) by apply termRHS_nonneg.
  lra.
Qed.

Lemma sum_map_acc_shift : forall (l:list A) (i:R),
  fold_right Rplus i (map termRHS l) = fold_right Rplus 0 (map termRHS l) + i.
Proof.
  induction l as [|a l' IH]; intros i; simpl; [ring|].
  rewrite IH. ring.
Qed.

(* Monotone product chain: if all right factors are nonnegative and each component decreases, the triple product decreases *)
Lemma mono_chain : forall x1 x2 y1 y2 z1 z2,
  0 <= y1 -> 0 <= z1 -> 0 <= x2 -> 0 <= y2 -> 0 <= z2 ->
  x1 >= x2 -> y1 >= y2 -> z1 >= z2 ->
  x1 * y1 * z1 >= x2 * y2 * z2.
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

Lemma fold_map_termRHS_ge_acc : forall (l:list A) (b:R),
  fold_right Rplus b (map termRHS l) >= b.
Proof.
  intros l b. induction l as [|a l' IH]; simpl; [lra|].
  assert (Ha_nonneg: 0 <= termRHS a) by apply termRHS_nonneg.
  (* IH: sum_l' >= b; add termRHS a to both sides *)
  assert (Haug: termRHS a + fold_right Rplus b (map termRHS l') >= termRHS a + b)
    by (apply Rplus_ge_compat_l; exact IH).
  (* termRHS a + b >= b by nonnegativity *)
  lra.
Qed.

Lemma sum_map_termRHS_ge_singleton : forall (L:list A) (a0:A), In a0 L ->
  termRHS a0 <= fold_right Rplus 0 (map termRHS L).
Proof.
  intros L a0 Hin.
  destruct (in_split a0 L Hin) as [l1 [l2 Heq]]. subst L.
  simpl. rewrite map_app.
  (* fold_right over append specialized to Rplus and base 0 *)
  rewrite fold_right_app. simpl.
  set (b0 := fold_right Rplus 0 (map termRHS (a0 :: l2))).
  (* Now LHS is fold_right Rplus b0 (map termRHS l1) *)
  (* Show fold_right ... >= b0 by nonnegativity of terms *)
  assert (Hge_b0: fold_right Rplus b0 (map termRHS l1) >= b0) by (apply fold_map_termRHS_ge_acc).
  (* And b0 >= termRHS a0 since b0 = termRHS a0 + sum(l2) and sum(l2) >= 0 *)
  assert (Hsum_l2_nonneg: 0 <= fold_right Rplus 0 (map termRHS l2)) by apply sum_termRHS_nonneg.
  unfold b0 in Hge_b0. simpl in Hge_b0.
  (* Chain: (termRHS a0 + sum_l2) >= termRHS a0 *)
  assert (Hb0_ge: termRHS a0 + fold_right Rplus 0 (map termRHS l2) >= termRHS a0) by lra.
  apply Rle_trans with (r2 := b0).
  apply Rge_le; exact Hb0_ge.
  apply Rge_le; exact Hge_b0.
Qed.

Lemma C_sum_ge_singleton : forall (L:list A) (a0:A), In a0 L ->
  C_sum L >= (4 / hbar) * termRHS a0.
Proof.
  intros L a0 Hin. unfold C_sum.
  set (c := 4 / hbar).
  assert (Hcpos: 0 <= c) by (unfold c; apply Rlt_le, Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos]).
  (* Scale the raw sum inequality by c ≥ 0 *)
  apply Rle_ge.
  apply Rmult_le_compat_l; [exact Hcpos|].
  apply sum_map_termRHS_ge_singleton; exact Hin.
Qed.

(* Paper cross-ref [Constructive]: Lift per-bound pointwise to sums → Π_sys ≥ C_sum. *)
Lemma Pi_ge_C_sum : forall L, Pi_sys L >= C_sum L.
Proof.
  intro L. unfold Pi_sys, C_sum.
  set (c := 4 / hbar).
  assert (Hcpos: 0 <= c) by (unfold c; apply Rlt_le, Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos]).
  (* pointwise per_bound lifts to sum inequality *)
  assert (Hsum: fold_right Rplus 0 (map termRHS L) <= fold_right Rplus 0 (map termLHS L)).
  { induction L as [|a L0 IH]; simpl; [lra|]. apply Rplus_le_compat.
    - apply Rge_le, per_bound.
    - exact IH.
  }
  apply Rle_ge. apply Rmult_le_compat_l; [exact Hcpos| exact Hsum].
Qed.

(* Uniform, system-independent lower bounds and a witness a0 in the list *)
Variable v0_min delta_min tau_min : R.
Hypothesis v0_min_pos : 0 < v0_min.
Hypothesis delta_min_pos : 0 < delta_min <= 1.
Hypothesis tau_min_nonneg : 0 <= tau_min.

Hypothesis witness_in : forall (L:list A), L <> [] -> exists a0, In a0 L /\
  v0 a0 >= v0_min /\ deltaA a0 >= delta_min /\ tau4 a0 >= tau_min.

(* Paper cross-ref [Constructive]: k = (4/hbar)·c_lin^2 as in Section 6. *)
Definition k := (4 / hbar) * (c_lin * c_lin).
Lemma k_nonneg : 0 <= k.
Proof.
  unfold k. apply Rmult_le_pos.
  - apply Rlt_le, Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos].
  - apply Rmult_le_pos; apply Rlt_le; exact c_lin_pos.
Qed.

(* Paper cross-ref [PerA+Avg]: perRHS(A) = v0(A)·δ_A·τ_A^4; Σ perRHS appears in Eq. (6.2) perC_total. *)
Definition perRHS (a:A) : R := v0 a * deltaA a * tau4 a.

Lemma perRHS_nonneg : forall a, 0 <= perRHS a.
Proof.
  intro a. unfold perRHS.
  apply Rmult_le_pos; [|apply tau4_nonneg].
  apply Rmult_le_pos; [apply Rlt_le, v0_pos|].
  destruct (deltaA_range a) as [H _]; exact H.
Qed.

Lemma sum_perRHS_nonneg : forall L, 0 <= fold_right Rplus 0 (map perRHS L).
Proof.
  induction L as [|a L0 IH]; simpl; [lra|].
  assert (Ha: 0 <= perRHS a) by apply perRHS_nonneg. lra.
Qed.

Lemma fold_map_perRHS_ge_acc : forall (l:list A) (b:R),
  b <= fold_right Rplus b (map perRHS l).
Proof.
  intros l b; induction l as [|a l' IH]; simpl.
  - apply Rle_refl.
  - assert (Ha: 0 <= perRHS a) by apply perRHS_nonneg.
    assert (H1: b + 0 <= b + perRHS a) by (apply Rplus_le_compat_l; exact Ha).
    rewrite Rplus_0_r in H1.
    assert (H2: b + perRHS a <= fold_right Rplus b (map perRHS l') + perRHS a)
      by (apply Rplus_le_compat_r; exact IH).
    replace (fold_right Rplus b (map perRHS l') + perRHS a)
      with (perRHS a + fold_right Rplus b (map perRHS l')) in H2 by ring.
    eapply Rle_trans; [exact H1| exact H2].
Qed.

(* Paper cross-ref [Constructive]: Σ termRHS = (c_lin^2) Σ perRHS (algebraic factorization). *)
Lemma map_termRHS_scaled : forall L,
  map termRHS L = map (fun a => (c_lin * c_lin) * perRHS a) L.
Proof.
  intro L. apply map_ext. intro a.
  unfold termRHS, perRHS. ring.
Qed.

Lemma sum_map_scaled : forall (c:R) (f:A->R) L,
  fold_right Rplus 0 (map (fun a => c * f a) L) = c * fold_right Rplus 0 (map f L).
Proof.
  intros c f L. induction L as [|a L0 IH]; simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma sum_termRHS_factor : forall L,
  fold_right Rplus 0 (map termRHS L)
  = (c_lin * c_lin) * fold_right Rplus 0 (map perRHS L).
Proof.
  intro L. rewrite map_termRHS_scaled. apply sum_map_scaled.
Qed.

(* perRHS_sum_cons_ge_head helper removed (unused) *)
 
Lemma sum_ge_singleton_perRHS : forall L a0, In a0 L ->
  fold_right Rplus 0 (map perRHS L) >= perRHS a0.
Proof.
  intros L a0 Hin.
  destruct (in_split a0 L Hin) as [l1 [l2 Heq]]. subst L.
  simpl. rewrite map_app. rewrite fold_right_app. simpl.
  set (b0 := fold_right Rplus 0 (map perRHS (a0 :: l2))).
  (* base: perRHS a0 <= b0 since sum l2 >= 0 *)
  assert (HS2: 0 <= fold_right Rplus 0 (map perRHS l2)) by apply sum_perRHS_nonneg.
  assert (Hbase: perRHS a0 <= b0).
  { unfold b0. rewrite <- Rplus_0_r at 1. apply Rplus_le_compat_l. exact HS2. }
  (* monotone: b0 <= fold_right _ b0 (map perRHS l1) *)
  assert (Hmono: b0 <= fold_right Rplus b0 (map perRHS l1)) by apply fold_map_perRHS_ge_acc.
  apply Rle_ge. eapply Rle_trans; [exact Hbase| exact Hmono].
Qed.

(* Paper cross-ref [Constructive]: Eq. (6.2) Π ≥ perC_total with k = (4/hbar)·c_lin^2. *)
Lemma ESSE_constructive_floor : forall L, L <> [] ->
  Pi_sys L >= k * fold_right Rplus 0 (map perRHS L).
Proof.
  intro L. intro Hne.
  unfold Pi_sys, k.
  (* Use Pi_ge_C_sum, then factor sum termRHS *)
  set (c := 4 / hbar).
  pose proof (Pi_ge_C_sum L) as Hge.
  (* Pi_sys L >= C_sum L = c * sum termRHS *)
  apply Rge_trans with (r2 := c * fold_right Rplus 0 (map termRHS L)).
  { exact Hge. }
  (* Replace sum termRHS by (c_lin^2) * sum perRHS and regroup into k *)
  rewrite sum_termRHS_factor.
  replace (c * ((c_lin * c_lin) * fold_right Rplus 0 (map perRHS L)))
    with (((4 / hbar) * (c_lin * c_lin)) * fold_right Rplus 0 (map perRHS L)) by (unfold c; ring).
  unfold k. reflexivity.
Qed.

(* Paper cross-ref [Universal]: Using Eq. (6.3) uniform minima to get class-wide floor Eq. (6.4). *)
Corollary ESSE_universal_floor_via_constructive : forall L, L <> [] ->
  (exists a0, In a0 L /\ v0 a0 >= v0_min /\ deltaA a0 >= delta_min /\ tau4 a0 >= tau_min) ->
  Pi_sys L >= k * v0_min * delta_min * tau_min.
Proof.
  intros L Hne [a0 [Hin [Hv0m [Hdm Htm]]]].
  (* From constructive: Pi_sys L >= k * sum perRHS L, and sum ≥ perRHS a0 *)
  pose proof (ESSE_constructive_floor L Hne) as Hconst.
  assert (Hsum_ge: fold_right Rplus 0 (map perRHS L) >= perRHS a0) by (apply sum_ge_singleton_perRHS; exact Hin).
  eapply Rge_trans; [exact Hconst|].
  (* Middle step: k * sum >= k * perRHS a0 *)
  eapply Rge_trans with (r2 := k * perRHS a0).
  { apply Rmult_ge_compat_l; [apply Rle_ge; exact k_nonneg| exact Hsum_ge]. }
  (* Final step: k * perRHS a0 >= k * (v0_min * delta_min * tau_min) *)
  (* perRHS a0 >= v0_min*delta_min*tau_min by mono_chain *)
  assert (Hcore: perRHS a0 >= v0_min * delta_min * tau_min).
  { unfold perRHS. apply (mono_chain (v0 a0) v0_min (deltaA a0) delta_min (tau4 a0) tau_min);
    [ destruct (deltaA_range a0) as [H _]; exact H
    | apply tau4_nonneg
    | apply Rlt_le; exact v0_min_pos
    | apply Rlt_le; exact (proj1 delta_min_pos)
    | exact tau_min_nonneg
    | exact Hv0m
    | exact Hdm
    | exact Htm ]. }
  replace (k * v0_min * delta_min * tau_min) with (k * (v0_min * delta_min * tau_min)) by ring.
  apply Rmult_ge_compat_l; [apply Rle_ge; exact k_nonneg| exact Hcore].
Qed.

(* Paper cross-ref [Universal] (alternate path): C_sum ≥ witness term ≥ class-wide constant. *)
Theorem ESSE_universal_floor : forall L, L <> [] ->
  Pi_sys L >= (4 / hbar) * v0_min * (c_lin * c_lin) * (delta_min * tau_min).
Proof.
  intros L Hne.
  destruct (witness_in L Hne) as [a0 [Hin [Hv0 [Hdel Htau]]]].
  pose proof (Pi_ge_C_sum L) as Hge. unfold Pi_sys, C_sum in Hge.
  (* Lower bound C_sum by the single witness term *)
  assert (HCsum_ge: (4 / hbar) * fold_right Rplus 0 (map termRHS L) >= (4 / hbar) * termRHS a0).
  { apply Rle_ge. apply Rmult_le_compat_l; [apply Rlt_le, Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos]|].
    apply sum_map_termRHS_ge_singleton; exact Hin. }
  (* Chain: Pi_sys >= C_sum >= singleton >= constant with mins *)
  eapply Rge_trans; [exact Hge|].
  eapply Rge_trans; [exact HCsum_ge|].
  (* Prove (4/hbar)*termRHS a0 >= (4/hbar)*v0_min*(c_lin^2)*(delta_min*tau_min) *)
  assert (Hsingleton_ge_const: (4 / hbar) * termRHS a0 >= (4 / hbar) * (v0_min * (c_lin * c_lin) * (delta_min * tau_min))).
  { (* Name a constant k for scaling *)
    set (k := (4 / hbar) * (c_lin * c_lin)).
    assert (Hk_nonneg: 0 <= k).
    { unfold k. apply Rmult_le_pos; [apply Rlt_le, Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact hbar_pos]|].
      apply Rmult_le_pos; apply Rlt_le; exact c_lin_pos. }
    unfold termRHS.
    (* Use mono_chain on the triple (v0, deltaA, tau4) against (v0_min, delta_min, tau_min) *)
    assert (HdeltaA_nonneg: 0 <= deltaA a0) by (destruct (deltaA_range a0) as [H _]; exact H).
    assert (Htau4_nonneg: 0 <= tau4 a0) by apply tau4_nonneg.
    (* Build the core inequality without constants *)
    assert (Hcore: v0 a0 * (deltaA a0) * (tau4 a0) >= v0_min * delta_min * tau_min).
    { apply (mono_chain (v0 a0) v0_min (deltaA a0) delta_min (tau4 a0) tau_min);
      [ exact HdeltaA_nonneg
      | exact Htau4_nonneg
      | apply Rlt_le; exact v0_min_pos
      | apply Rlt_le; exact (proj1 delta_min_pos)
      | exact tau_min_nonneg
      | exact Hv0
      | exact Hdel
      | exact Htau ]. }
    (* Scale by k >= 0 *)
    replace ((4 / hbar) * (v0 a0 * (c_lin * c_lin) * (deltaA a0 * tau4 a0)))
      with (k * (v0 a0 * deltaA a0 * tau4 a0)) by (unfold k; ring).
    replace ((4 / hbar) * (v0_min * (c_lin * c_lin) * (delta_min * tau_min)))
      with (k * (v0_min * delta_min * tau_min)) by (unfold k; ring).
    apply Rle_ge. apply Rmult_le_compat_l; [exact Hk_nonneg|]. apply Rge_le. exact Hcore.
  }
  replace ((4 / hbar) * v0_min * (c_lin * c_lin) * (delta_min * tau_min))
    with ((4 / hbar) * (v0_min * (c_lin * c_lin) * (delta_min * tau_min))) by ring.
  exact Hsingleton_ge_const.
Qed.
 
End ESSEUniversal. 