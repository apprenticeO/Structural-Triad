(*
  ESSEUniversal_structure.v
  - Paper mapping: Elephant_final_full.tex "The Quantum Structural Triad"
  - Depends on: TimeAvgClean.v (density-of-good-times and averaging lemmas)
  - Proof strategy: Discrete-time triad signals with good-time predicates
  - Nonnegativity-based proofs (no circularity), Witness/minima lemmas
*)

(*
  ESSEUniversal.v
  - Depends on:
    * ESSEList.v (sum lifting Pi_sys >= C_sum)
    * PerBoundClean.v (per-subsystem bound patterns and monotonicity steps)
    * PinskerClean.v, PinskerSquaredClean.v (provide c_lin context, via per_bound upstream)
    * TimeAvgClean.v, AveragingPerA.v (deltaA, tau4 metrics and averaging lemmas used upstream)
  - Proof strategy motifs:
    * sum_map_termRHS_ge_singleton: in_split + fold_right_app + nonnegativity
    * Rplus/Rmult monotonicity with nonnegative factors
    * Chain inequalities using Rge_trans/Rle_trans consistently
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
Import ListNotations. Open Scope R_scope.

Require Import ESSEClean.TimeAvgClean.

(* BEGIN_DEPRECATED: pure-state ΔH·S^2 path; not used *)
(*
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
*)
(* END_DEPRECATED *)


(* State-agnostic note: The triad section below is mixed/pure agnostic; no purity-specific identities are used. *) 


(* Notes (state-agnostic, comment-only):
   - Vanishing characterizations (paper):
     F_Q(ρ_A;H_A)=0 ↔ [ρ_A,H_A]=0; S_A=0 ↔ ρ_A pure; I(A:Ā)=0 ↔ ρ_AB=ρ_A⊗ρ_B.
   - QSL (Bures-length): ∫_0^T (1/2)√F_Q ≥ L_B(ρ_A(0),ρ_A(T)); hence (1/T)∫√F_Q ≥ (2/T)L_B.
   - Continuity of √F_Q under piecewise-C^1 dynamics in finite dimension (SLD continuity argument).
   - Lieb–Robinson witness: existence of a positive-measure set with I>0 and non-commutativity across a cut → uniform floors on a closed K.
   - Sufficiency: H1–H3 ⇒ ON via the witness; ON ⇒ H2–H3 under product preparation.
   - Liminf wrapper: if ∃N1 s.t. avg f(n) ≥ c for all n≥N1, then liminf avg ≥ c.
   - Normalization: list-level normalization scales bounds by 1/|L| and preserves positivity. *)

(* ============================================================================ *)
(* MAIN FORMALIZATION: ElephantTriad Section                                   *)
(* Paper Section 2: Quantum Structural Triad Definition                       *)
(* - Discrete-time formalization of Π_A(t) = √F_Q(ρ_A;H_A) · S_A · I(A:Ā)   *)
(* - State-agnostic: works for both pure and mixed states                     *)
(* - Maps to Eq. (1) in paper                                                 *)
(* ============================================================================ *)

Section ElephantTriad.

Variable A : Type.

(* Per-subsystem discrete-time triad signals (state-agnostic) *)
Variable rA sA iA : A -> nat -> R.
(* Paper Section 2: Per-subsystem discrete-time triad signals
   - rA: fluctuation signal (maps to √F_Q(ρ_A;H_A))
   - sA: entropy signal (maps to S_A)
   - iA: correlation signal (maps to I(A:Ā))
   - goodA: predicate for "good epochs" where signals exceed floors *)
Variable goodA : A -> nat -> bool.

(* Floors and density (map to ε_F, ε_S, ε_I and \underline d(K)) *)
Variable epsR epsS epsI : A -> R.
Variable deltaA : A -> R.

Hypothesis rA_nonneg : forall a n, 0 <= rA a n.
Hypothesis sA_nonneg : forall a n, 0 <= sA a n.
Hypothesis iA_nonneg : forall a n, 0 <= iA a n.

(* MODIFIED: Replace strict positivity with nonnegativity *)
Hypothesis epsR_nonneg : forall a, 0 <= epsR a.
Hypothesis epsS_nonneg : forall a, 0 <= epsS a.
Hypothesis epsI_nonneg : forall a, 0 <= epsI a.

Hypothesis deltaA_range : forall a, 0 <= deltaA a <= 1.

Hypothesis good_lower_r : forall a n, goodA a n = true -> rA a n >= epsR a.
Hypothesis good_lower_s : forall a n, goodA a n = true -> sA a n >= epsS a.
Hypothesis good_lower_i : forall a n, goodA a n = true -> iA a n >= epsI a.

Hypothesis density_lower_eventual : forall a, exists N0:nat, forall n:nat, (n >= N0)%nat ->
  INR (ESSEClean.TimeAvgClean.count_good (fun k => goodA a k) n) >= (deltaA a) * INR n.

Definition PsiA_triad (a:A) (n:nat) : R := rA a n * (sA a n * iA a n).
(* Paper Section 2: Definition of quantum structural triad
   - PsiA_triad a n = rA a n * (sA a n * iA a n)
   - Discrete-time version of Π_A(t) = √F_Q(ρ_A;H_A) · S_A · I(A:Ā) *)

Lemma psi_triad_lower_on_good : forall a n, goodA a n = true ->
  PsiA_triad a n >= (epsR a) * (epsS a * epsI a).
Proof.
  intros a n Hg. unfold PsiA_triad.
  pose proof (good_lower_r a n Hg) as Hr.
  pose proof (good_lower_s a n Hg) as Hs.
  pose proof (good_lower_i a n Hg) as Hi.
  pose proof (rA_nonneg a n) as Hr0.
  pose proof (sA_nonneg a n) as Hs0.
  pose proof (iA_nonneg a n) as Hi0.
  (* Work in ≤ then flip to ≥ at the end *)
  apply Rle_ge.
  (* Goal: epsR*epsS*epsI ≤ rA*(sA*iA) *)
  (* Step A: epsR*(epsS*epsI) ≤ rA*(epsS*epsI) by Hr and nonneg (epsS*epsI) *)
  assert (HstepA : (epsR a) * (epsS a * epsI a) <= rA a n * (epsS a * epsI a)).
  { apply Rmult_le_compat_r.
    - apply Rmult_le_pos; [apply epsS_nonneg | apply epsI_nonneg].
    - apply Rge_le; exact Hr. }
  (* Step B1: epsS*epsI ≤ sA*epsI by sA≥epsS and epsI≥0 *)
  assert (HB1 : (epsS a) * (epsI a) <= sA a n * (epsI a)).
  { apply Rmult_le_compat_r; [apply epsI_nonneg | apply Rge_le; exact Hs]. }
  (* Step B2: sA*epsI ≤ sA*iA by iA≥epsI and sA≥0 *)
  assert (HB2 : sA a n * (epsI a) <= sA a n * iA a n).
  { apply Rmult_le_compat_l.
    - exact Hs0.
    - apply Rge_le; exact Hi. }
  assert (HstepB : (epsS a) * (epsI a) <= sA a n * iA a n) by (eapply Rle_trans; [exact HB1|exact HB2]).
  (* Lift Step B by nonneg rA *)
  assert (HstepB2 : rA a n * (epsS a * epsI a) <= rA a n * (sA a n * iA a n)).
  { apply Rmult_le_compat_l; [exact Hr0| exact HstepB]. }
  eapply Rle_trans; [exact HstepA| exact HstepB2].
Qed.

Lemma triad_avg_eventual_lower_perA : forall a,
  exists N1:nat, forall n, (n >= N1)%nat ->
    ESSEClean.TimeAvgClean.avg (fun k => PsiA_triad a k) n >= (deltaA a) * ((epsR a) * (epsS a * epsI a)).
Proof.
  intro a.
  set (x := fun k => PsiA_triad a k).
  set (g := fun k => goodA a k).
  set (c := (epsR a) * (epsS a * epsI a)).
  assert (Hx_nonneg : forall n, 0 <= x n).
  { intro n. unfold x, PsiA_triad.
    apply Rmult_le_pos; [apply rA_nonneg|]. apply Rmult_le_pos; [apply sA_nonneg|apply iA_nonneg]. }
  (* MODIFIED: Use nonnegativity instead of strict positivity *)
  assert (Hc_nonneg : 0 <= c).
  { unfold c. apply Rmult_le_pos; [apply epsR_nonneg|].
    apply Rmult_le_pos; [apply epsS_nonneg|apply epsI_nonneg]. }
  assert (Hgood_lower : forall n, g n = true -> x n >= c).
  { intros n Hg. unfold x, c. apply psi_triad_lower_on_good; exact Hg. }
  destruct (density_lower_eventual a) as [N0 Hdens].
  assert (Hdens' : exists N0, forall n, (n >= N0)%nat ->
            INR (ESSEClean.TimeAvgClean.count_good g n) >= (deltaA a) * INR n).
  { exists N0. intros n Hn. apply Hdens; exact Hn. }
  eapply ESSEClean.TimeAvgClean.avg_eventual_lower with (x:=x) (good:=g) (c:=c) (delta:=(deltaA a)).
  all: eauto.
Qed.

(* Witness with class minima: uniform positive floor *)
Variable epsR_min epsS_min epsI_min delta_min : R.
Hypothesis epsR_min_pos : 0 < epsR_min.
Hypothesis epsS_min_pos : 0 < epsS_min.
Hypothesis epsI_min_pos : 0 < epsI_min.
Hypothesis delta_min_pos : 0 < delta_min <= 1.

Hypothesis witness_in : forall (L:list A), L <> [] -> exists a0, In a0 L /\
  epsR a0 >= epsR_min /\ epsS a0 >= epsS_min /\ epsI a0 >= epsI_min /\ deltaA a0 >= delta_min.

Lemma Triad_witness_floor_minima : forall (L:list A), L <> [] ->
  exists a0 N1, In a0 L /\ forall n, (n >= N1)%nat ->
    ESSEClean.TimeAvgClean.avg (fun k => PsiA_triad a0 k) n >= delta_min * (epsR_min * (epsS_min * epsI_min)).
Proof.
  intros L Hne. destruct (witness_in L Hne) as [a0 [Hin [HeR [HeS [HeI Hd]]]]].
  destruct (triad_avg_eventual_lower_perA a0) as [N1 Havg].
  exists a0, N1. split; [exact Hin|].
  intros n Hn. specialize (Havg n Hn).
  assert (Hdel_ge : deltaA a0 >= delta_min) by exact Hd.
  assert (HeRge : epsR a0 >= epsR_min) by exact HeR.
  assert (HeSge : epsS a0 >= epsS_min) by exact HeS.
  assert (HeIge : epsI a0 >= epsI_min) by exact HeI.
  assert (HeRle : epsR_min <= epsR a0) by (apply Rge_le; exact HeRge).
  assert (HeSle : epsS_min <= epsS a0) by (apply Rge_le; exact HeSge).
  assert (HeIle : epsI_min <= epsI a0) by (apply Rge_le; exact HeIge).
  assert (Hprod_eps_ge : epsR a0 * (epsS a0 * epsI a0) >= epsR_min * (epsS_min * epsI_min)).
  { apply Rle_ge.
    (* Build epsR_min*(epsS_min*epsI_min) <= epsR a0*(epsS a0*epsI a0) by chaining *)
    (* P0 ≤ P1 *)
    assert (H1 : epsR_min * (epsS_min * epsI_min) <= epsR a0 * (epsS_min * epsI_min)).
    { apply Rmult_le_compat_r.
      - apply Rmult_le_pos; apply Rlt_le; [apply epsS_min_pos|apply epsI_min_pos].
      - exact HeRle. }
    (* P1 ≤ P2: replace epsS_min by epsS a0 *)
    assert (H2' : epsS_min * epsI_min <= epsS a0 * epsI_min).
    { apply Rmult_le_compat_r; [apply Rlt_le, epsI_min_pos| exact HeSle]. }
    (* MODIFIED: Use nonnegativity instead of strict positivity *)
    assert (H2 : epsR a0 * (epsS_min * epsI_min) <= epsR a0 * (epsS a0 * epsI_min)).
    { apply Rmult_le_compat_l; [apply epsR_nonneg | exact H2']. }
    (* P2 ≤ P3: replace epsI_min by epsI a0 *)
    assert (H3' : epsS a0 * epsI_min <= epsS a0 * epsI a0).
    { apply Rmult_le_compat_l; [apply epsS_nonneg | exact HeIle]. }
    assert (H3 : epsR a0 * (epsS a0 * epsI_min) <= epsR a0 * (epsS a0 * epsI a0)).
    { apply Rmult_le_compat_l; [apply epsR_nonneg | exact H3']. }
    eapply Rle_trans; [exact H1|]. eapply Rle_trans; [exact H2| exact H3]. }
  eapply Rge_trans; [exact Havg|].
  (* Chain via two monotone steps to reach delta_min * minima product *)
  assert (MinProd_nonneg: 0 <= epsR_min * (epsS_min * epsI_min)).
  { apply Rmult_le_pos; [apply Rlt_le, epsR_min_pos|]. apply Rmult_le_pos; apply Rlt_le; [apply epsS_min_pos|apply epsI_min_pos]. }
  assert (StepA: deltaA a0 * (epsR a0 * (epsS a0 * epsI a0)) >= deltaA a0 * (epsR_min * (epsS_min * epsI_min))).
  { apply Rmult_ge_compat_l.
    - apply Rle_ge. destruct (deltaA_range a0) as [H _]. exact H.
    - exact Hprod_eps_ge. }
  assert (StepB: deltaA a0 * (epsR_min * (epsS_min * epsI_min)) >= delta_min * (epsR_min * (epsS_min * epsI_min))).
  { apply Rmult_ge_compat_r; [apply Rle_ge; exact MinProd_nonneg| exact Hdel_ge]. }
  eapply Rge_trans; [exact StepA| exact StepB].
Qed.

(* Operational Nontriviality (state-agnostic, per A) *)
Definition ON_A (a:A) : Prop := deltaA a > 0.

(* Intensive normalization for the triad across a fixed list of cuts. *)
Definition Triad_norm (L:list A) (n:nat) : R :=
  match L with
  | [] => 0
  | _ => (1 / INR (length L)) * fold_right Rplus 0 (map (fun a => PsiA_triad a n) L)
  end.

End ElephantTriad.

