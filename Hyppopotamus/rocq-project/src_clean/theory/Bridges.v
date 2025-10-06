From Coq Require Import Reals.
Open Scope R_scope.
Axiom QFI_var_upper : forall (dE ℏ FQ: R), 0 < ℏ -> 0 <= dE -> 0 <= FQ ->
  FQ <= 4 * (dE * dE) / (ℏ * ℏ).  (* [Braunstein & Caves, 1994] *)
Axiom Bures_speed_unitary : forall FQ: R, 0 <= FQ ->
  exists Ldot: R, Ldot = (/2) * sqrt FQ. (* [Taddei et al., 2013] *)
