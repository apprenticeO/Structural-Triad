From Coq Require Import Reals Lists.List.
Require Import ESSEClean.TimeAvgClean.
Require Import ESSEClean.theory.SystemSpec.
Open Scope R_scope.

Section LegFloors.
Context (S: Admissible).
Variable rA_t sA_t iA_t : CutSpec -> nat -> R.
Variable goodA_t : CutSpec -> nat -> bool.

Variable H1_locality    : Prop.
Variable H2_cross_couple: Prop.
Variable H3_nonstation  : Prop.

Hypothesis Floors_from_H123 :
  H1_locality -> H2_cross_couple -> H3_nonstation ->
  exists epsR_min epsS_min epsI_min delta_min : R,
    0 < epsR_min /\ 0 < epsS_min /\ 0 < epsI_min /\
    0 < delta_min <= 1 /\
    (forall c n, In c S.(cuts) -> goodA_t c n = true ->
       rA_t c n >= epsR_min /\ sA_t c n >= epsS_min /\ iA_t c n >= epsI_min) /\
    (forall c, In c S.(cuts) -> exists N0, forall n, (n >= N0)%nat ->
       INR (ESSEClean.TimeAvgClean.count_good (fun k => goodA_t c k) n)
          >= delta_min * INR n).
End LegFloors.
