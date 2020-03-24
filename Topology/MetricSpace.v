Generalizable All Variables.

Require Import Coq.Reals.Reals.
Require Import FormalMath.Topology.TopologicalSpace.

Local Open Scope R_scope.

Class DistanceFunc (A: Type) := d: A -> A -> R.
Typeclasses Transparent DistanceFunc.

Class Metric (A: Type) {DF: DistanceFunc A}: Prop :=
  {
    metric_nonneg: forall x y, 0 <= d x y;
    metric_zero_iff: forall x y, d x y = 0 <-> x = y;
    metric_sym: forall x y, d x y = d y x;
    metric_trig_ineq: forall x y z, d x z <= d x y + d y z
  }.

Section METRIC_TOPOLOGY.

  Context `{M: Metric A}.

  Lemma metric_zero: forall x, d x x = 0.
  Proof. intros. now rewrite metric_zero_iff. Qed.

  Definition openBall (x: A) (epsl: R): Ensemble A := fun y => d x y < epsl.

  Lemma openBall_In_nest: forall x y r,
      In (openBall x r) y -> exists r', 0 < r' /\
                                        Included (openBall y r') (openBall x r).
  Proof.
    intros. exists (r - d x y). split.
    - hnf in H. now apply Rlt_Rminus.
    - repeat intro. hnf in H0 |- *. apply (Rplus_lt_compat_l (d x y)) in H0.
      rewrite Rplus_minus in H0. apply Rle_lt_trans with (r2 := d x y + d y x0); auto.
      apply metric_trig_ineq.
  Qed.

  Lemma openBall_In_pos: forall x y r, In (openBall x r) y -> 0 < r.
  Proof.
    intros. hnf in H. pose proof (metric_nonneg x y). apply (Rle_lt_trans _ _ _ H0 H).
  Qed.

  Lemma openBall_nonpos: forall x r, r <= 0 -> openBall x r = Empty_set.
  Proof.
    intros. apply Extensionality_Ensembles. split; red; intros.
    - apply openBall_In_pos in H0. exfalso. apply Rle_not_lt in H. now apply H.
    - inversion H0.
  Qed.

  Lemma openBall_Included: forall x r1 r2,
      r1 <= r2 -> Included (openBall x r1) (openBall x r2).
  Proof.
    intros. intros y ?. hnf in H0 |- *. now apply Rlt_le_trans with (r2 := r1).
  Qed.

  Inductive openBallBasis: Family A :=
    openBallBasis_intro: forall x r, In openBallBasis (openBall x r).

  Lemma openBallBasis_topology_basis: topology_basis openBallBasis.
  Proof.
    split; intros.
    - exists (openBall x 1). split.
      + constructor.
      + hnf. rewrite metric_zero. apply Rlt_0_1.
    - destruct H as [x1 ?]. destruct H0 as [x2 ?]. rename r into r1. rename r0 into r2.
      destruct H1. apply openBall_In_nest in H. apply openBall_In_nest in H0.
      destruct H as [r1' [? ?]]. destruct H0 as [r2' [? ?]].
      exists (openBall x (Rmin r1' r2')). repeat split.
      + hnf. rewrite metric_zero. now apply Rmin_glb_lt.
      + apply H1. apply (openBall_Included _ (Rmin r1' r2')); auto. apply Rmin_l.
      + apply H2. apply (openBall_Included _ (Rmin r1' r2')); auto. apply Rmin_r.
  Qed.

  Global Instance metricOpenSet: OpenSet A := basis_to_open openBallBasis.

  Global Instance metricTopology: TopologicalSpace A.
  Proof. apply topology_basis_TopologicalSpace, openBallBasis_topology_basis. Qed.

  Definition metric_bounded (S: Ensemble A): Prop :=
    exists M, forall a1 a2, In S a1 -> In S a2 -> d a1 a2 <= M.

  Lemma metric_open_In: forall (x: A) (U: Ensemble A),
      open U -> In U x -> exists r, 0 < r /\ Included (openBall x r) U.
  Proof.
    intros. unfold open, metricOpenSet, basis_to_open in H. specialize (H _ H0).
    destruct H as [b [[y ?] [? ?]]]. apply openBall_In_nest in H.
    destruct H as [r' [? ?]]. exists r'. split; auto.
    apply Inclusion_is_transitive with (openBall y r); auto.
  Qed.

  Lemma openBall_open: forall x r, open (openBall x r).
  Proof.
    intros. unfold open, metricOpenSet, basis_to_open. intros y ?.
    exists (openBall x r). split; [|split]; auto.
    - constructor.
    - auto with sets.
  Qed.

  Lemma metric_isolated_in_set: forall (x: A) (S: Ensemble A),
      isolated_in_set x S <->
      exists eta: R, Intersection (openBall x eta) S = Singleton x.
  Proof.
    intros. split; intros.
    - red in H. destruct H as [? [U [? ?]]].
      assert (In U x). {
        pose proof (In_singleton _ x). rewrite <- H1 in H2. now destruct H2. }
      destruct (metric_open_In _ _ H0 H2) as [r [? ?]]. exists r.
      apply Extensionality_Ensembles. split.
      + rewrite <- H1. repeat intro. destruct H5. split; auto.
      + repeat intro. inversion H5. subst x0. split; auto. unfold openBall. red.
        now rewrite metric_zero.
    - destruct H as [eta ?]. red. split.
      + assert (Included (Singleton x) (Intersection (openBall x eta) S)) by
            (rewrite H; auto with sets). now destruct (H0 _ (In_singleton _ x)).
      + exists (openBall x eta). split; auto. apply openBall_open.
  Qed.

End METRIC_TOPOLOGY.
