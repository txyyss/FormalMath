Require Import Coq.Reals.Reals.
Require Import FormalMath.Topology.TopologicalSpace.

Local Open Scope R_scope.

Class Metric {A: Type} (d: A -> A -> R): Prop :=
  {
    metric_nonneg: forall x y, 0 <= d x y;
    metric_zero_iff: forall x y, d x y = 0 <-> x = y;
    metric_sym: forall x y, d x y = d y x;
    matric_tri_ineq: forall x y z, d x z <= d x y + d y z
  }.
