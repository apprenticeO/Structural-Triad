(*
  EntropyClean.v
  Paper mapping (Structural Triad, PDF):
  - [Notation/System] Section 1: S_list is a simple entropy functional over lists of probabilities.
  - Utilities here support nonnegativity arguments used when relating entropy terms
    and trace norms (e.g., ensuring S_A ≥ 0 and handling ln behavior on [0,1]).
  - Pinsker-related quantitative steps are encoded elsewhere; this file provides
    generic real-inequality helpers used in those arguments.
*)
From Coq Require Import Reals Lists.List Unicode.Utf8 Psatz.
From Coquelicot Require Import Rcomplements.
Import ListNotations. Open Scope R_scope.

Section EntropyClean.

(* Basic list entropy on probabilities *)
Definition safe_log (x:R) := if Rle_dec x 0 then 0 else ln x.

Definition S_list (l:list R) : R :=
  - fold_right Rplus 0 (map (fun lam => lam * safe_log lam) l).

(* Helpers for nonnegativity and in-list comparisons. *)
Lemma sum_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= fold_right Rplus 0 l.
Proof.
  induction l as [|x l IH]; intro H; simpl; [lra|].
  inversion H as [|x' l' Hx Hl]; subst; specialize (IH Hl); lra.
Qed.

Lemma in_le_sum_nonneg : forall l, Forall (fun x => 0 <= x) l ->
  forall x, In x l -> x <= fold_right Rplus 0 l.
Proof.
  induction l as [|y l IH]; intros H x Hin; [inversion Hin|].
  simpl in *. inversion H as [|y' l' Hy Hl]; subst.
  destruct Hin as [->|Hin].
  - pose proof (sum_nonneg l Hl); lra.
  - specialize (IH Hl x Hin). lra.
Qed.

(* Paper cross-ref: on [0,1], x ln x ≤ 0, used to show S_list ≥ 0 under normalization. *)
Lemma mul_safe_log_le_0 : forall x, 0 <= x <= 1 -> x * safe_log x <= 0.
Proof.
  intros x [Hx0 Hx1]. unfold safe_log.
  destruct (Rle_dec x 0) as [Hle|Hgt0].
  - assert (x = 0) by lra. subst. simpl. lra.
  - assert (Hxpos: 0 < x) by lra.
    destruct (Rtotal_order x 1) as [Hlt | [Heq | Hgt]].
    + (* x < 1 *)
      assert (Hlnlt: ln x < ln 1) by (apply ln_increasing; lra).
      rewrite ln_1 in Hlnlt.
      assert (Hxge0: 0 <= x) by (apply Rlt_le; exact Hxpos).
      assert (Hprod: x * ln x <= x * 0) by (apply Rmult_le_compat_l; [exact Hxge0|apply Rlt_le; exact Hlnlt]).
      rewrite Rmult_0_r in Hprod. exact Hprod.
    + (* x = 1 *)
      subst x. simpl. rewrite ln_1. lra.
    + (* x > 1 contradicts x <= 1 *)
      exfalso. lra.
Qed.

(* Main: entropy non-negativity for probability lists *)
Lemma S_list_ge0 : forall l,
  Forall (fun lam => 0 <= lam) l -> fold_right Rplus 0 l = 1 -> 0 <= S_list l.
Proof.
  intros l Hnn Hsum.
  unfold S_list.
  assert (Hterms_nonpos : Forall (fun t => t <= 0) (map (fun lam => lam * safe_log lam) l)).
  { apply Forall_forall. intros x Hinx.
    apply in_map_iff in Hinx as [lam [Hx Hin]]. subst x.
    apply mul_safe_log_le_0. split.
    - (* 0 <= lam from Hnn and Hin *)
      pose proof (proj1 (Forall_forall (fun lam => 0 <= lam) l) Hnn) as Hforall.
      exact (Hforall lam Hin).
    - rewrite <- Hsum. apply in_le_sum_nonneg; assumption.
  }
  assert (fold_right Rplus 0 (map (fun lam => lam * safe_log lam) l) <= 0).
  { clear Hsum Hnn. induction l as [|x l IH]; simpl.
    - lra.
    - inversion Hterms_nonpos as [|x' l' Hx Hl]; subst. specialize (IH Hl). lra.
  }
  lra.
Qed.

End EntropyClean. 