Require Import FormalMath.Algebra.Group.

Section UNIT_GROUP.

  #[export] Instance unitEquiv: Equiv unit := (==).
  #[export] Instance unitBinOp: BinOp unit := fun _ _ => tt.
  #[export] Instance unitGrUnit: GrUnit unit := tt.
  #[export] Instance unitNegate: Negate unit := fun _ => tt.
  #[export] Instance unitSetoid: Setoid unit.
  Proof.
    constructor; repeat intro; destruct x; [easy | now destruct y | now destruct z].
  Qed.

  #[export] Instance unitGroup: Group unit.
  Proof.
    constructor; try apply _; repeat intro; destruct x;
      [destruct y, z|..]; now vm_compute.
  Qed.

End UNIT_GROUP.
