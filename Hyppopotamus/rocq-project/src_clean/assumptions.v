(*
  Assumptions printer (Structural Triad, PDF mapping)
  - Manuscript: v3_A_Quantum_Structural_Triad__Fluctuations__Entropy__and_Correlations_as_Interdependent_Primitives_Tataru_.pdf
  - Purpose: print logical assumptions behind the boxed finite-sum, positivity,
    and averaged constructive results, for traceability to the paper sections.
*)
From ESSEClean Require Import ESSEBoxed ESSEList PerBoundClean PinskerClean PinskerSquaredClean GapFloorClean AveragingPerA PiClean Positivity PurityClean FisherClean EntropyClean TimeAvgClean.

(* Print assumptions for boxed finite-sum and positivity statements *)
Print Assumptions ESSE_boxed_finite_sum.
Print Assumptions ESSE_boxed_strict_pos.
Print Assumptions ESSE_boxed_Pi_sys_pos.

(* Per-term bound and averaging lemmas *)
Print Assumptions PerBoundClean.per_bound_le.
Print Assumptions AveragingPerA.avg_eventual_lower_perA.

(* Clean shells: specific lemmas *)
Print Assumptions PurityClean.mutual_info_pure_global.
Print Assumptions FisherClean.fisher_is_four_var. 