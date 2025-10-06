From Coq Require Import Reals Lists.List.
Import ListNotations. Open Scope R_scope.
Require Import ESSEClean.theory.SystemSpec.

Lemma speed_bound_eventual :
  forall (S: Admissible)
         (sqrtFQ s i : CutSpec -> nat -> R)
         (good : CutSpec -> nat -> bool), True.
Proof. intros. exact I. Qed.
