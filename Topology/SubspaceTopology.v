Generalizable All Variables.

Require Import FormalMath.Topology.TopologicalSpace.
Require Import Coq.Logic.ClassicalChoice.

Section SUBSPACE_TOPOLOGY.

  Context `{T: TopologicalSpace A}.

  Definition subspace_open (S: Ensemble A): OpenSet {x: A | In S x} :=
    Im open (fun O y => In O (proj1_sig y)).

  Lemma subspace_topology:
    forall (S: Ensemble A), @TopologicalSpace {x: A | In S x} (subspace_open S).
  Proof.
    intros. split; unfold open; intros.
    - exists Full_set.
      + apply full_open.
      + apply Extensionality_Ensembles. split; repeat intro; constructor.
    - exists (FamilyUnion (fun O => open O /\
                                    In (Im f (fun x => Im x (@proj1_sig A S)))
                                       (Intersection S O))).
      + apply any_union_open. intros. red in H0. now destruct H0.
      + apply Extensionality_Ensembles. split; repeat intro.
        * destruct H0. red. destruct x as [x ?]. red. simpl. specialize (H S0 H0).
          red in H. destruct H as [O ?]. exists O.
          -- red. split; auto. exists y; auto. apply Extensionality_Ensembles.
             split; repeat intro.
             ++ destruct H3. exists (exist _ x0 H3). 2: now simpl. subst y.
                red. now simpl.
             ++ destruct H3. destruct x0 as [y1 ?]. simpl in H4. subst y1.
                split; auto. subst y. red in H3. now simpl in H3.
          -- subst y. red in H1. now simpl in H1.
        * red in H0. destruct x as [x ?]. simpl in H0. destruct H0 as [O ?]. red in H0.
          destruct H0. inversion H2. subst. exists x0; auto.
          pose proof (Intersection_intro A S O x i H1). rewrite H4 in H5.
          inversion H5. subst. destruct x1 as [x ?]. simpl in *.
          replace i with i0; auto. apply proof_irrelevance.
    - unfold subspace_open in *. inversion H. subst. rename x into O1. clear H.
      inversion H0. subst. rename x into O2. clear H0. exists (Intersection O1 O2).
      + now apply intersection_open.
      + apply Extensionality_Ensembles. split; repeat intro.
        * destruct x as [x ?]. inversion H0. subst. clear H0. red in H2, H3 |- *.
          simpl in *. now split.
        * destruct x as [x ?]. red in H0. simpl in H0.
          destruct H0. now split; red; simpl.
  Qed.

  Definition connected_subspace (U: Ensemble A): Prop :=
    @connected {x: A | In U x} (subspace_open U).

  Definition compact_subspace (U: Ensemble A): Prop :=
    @compact {x: A | In U x} (subspace_open U).

  Definition isolated_in_subspace (x: A) (U: Ensemble A) (H: In U x): Prop :=
    @isolated {y: A | In U y} (subspace_open U) (exist _ x H).

  Lemma compact_subspace_set_iff: forall (S: Ensemble A),
      compact_subspace S <-> compact_set S.
  Proof.
    intros. split; intros; red in H |- *.
    - red in H. intros. specialize (H (FamilyIntersectSet C S)).
      assert (forall U : Ensemble {x : A | In S x},
                 In (FamilyIntersectSet C S) U ->
                 @open {x : A | @In A S x} (subspace_open S) U). {
        intros. unfold open. inversion H2. subst. rename x into U. clear H2.
        exists U; auto. now apply H0. } specialize (H H2). clear H2.
      assert (FamilyUnion (FamilyIntersectSet C S) = @Full_set {x : A | In S x}). {
        apply Extensionality_Ensembles. split; repeat intro. 1: constructor.
        rewrite union_FIS. destruct x as [x ?]. clear H2. unfold interSum.
        red. simpl. auto. } specialize (H H2). clear H2. destruct H as [fCS [? [? ?]]].
      assert (forall su: { x | In fCS x},
                 exists f, In C f /\ proj1_sig su = interSum f S). {
        intros. destruct su as [x ?]. specialize (H2 x i). simpl. inversion H2. subst.
        exists x0. split; auto. } clear H2.
      destruct (choice _ H4) as [func ?]. clear H4. exists (imageFamily func).
      split; [|split].
      + unfold imageFamily. apply finite_image.
        now rewrite finite_sig_iff, <- finite_type_full_iff, <- finite_sig_iff.
      + unfold imageFamily. repeat intro. inversion H4. subst. specialize (H2 x0).
        now destruct H2.
      + unfold imageFamily. repeat intro.
        assert (In (@Full_set {x: A | In S x}) (exist _ x H4)) by constructor.
        rewrite <- H3 in H5. inversion H5. subst. specialize (H2 (exist _ S0 H6)).
        simpl in H2. destruct H2. exists (func (exist (In fCS) S0 H6)).
        * exists (exist _ S0 H6); auto. constructor.
        * rewrite H8 in H7. unfold interSum in H7. red in H7. now simpl in H7.
    - red. intros.
      remember (fun O => open O /\ In C (interSum O S)) as CC.
      assert (forall U, In CC U -> open U). {
        intros. subst. red in H2. now destruct H2. }
      assert (Included S (FamilyUnion CC)). {
        rewrite HeqCC. repeat intro.
        assert (In (FamilyUnion C) (exist _ x H3)) by (rewrite H1; constructor).
        inversion H4. subst x0. specialize (H0 _ H5). hnf in H0. inversion H0. subst y.
        subst S0. red in H6. simpl in H6. rename x0 into O. exists O; auto. red.
        split; auto. } specialize (H _ H2 H3). clear H2 H3.
      destruct H as [fCF [? [? ?]]]. exists (FamilyIntersectSet fCF S). repeat split.
      + now apply finite_image.
      + repeat intro. unfold FamilyIntersectSet in H4. inversion H4. subst. clear H4.
        specialize (H2 x0 H5). red in H2. destruct H2. apply H4.
      + rewrite union_FIS. apply Extensionality_Ensembles. split; repeat intro.
        1: constructor. unfold interSum. red. destruct x as [x ?]. simpl; auto.
  Qed.

End SUBSPACE_TOPOLOGY.

Lemma isolated_in_subspace_in_set:
  forall {A} {Ao: OpenSet A} (x: A) (S: Ensemble A) (H: In S x),
    isolated_in_subspace x S H -> isolated_in_set x S.
Proof.
  intros. red in H0 |- *. red in H0. split; auto. unfold open, subspace_open in H0.
  inversion H0. subst. clear H0. rename x0 into O. exists O. split; auto.
  apply Extensionality_Ensembles.
  assert (Included (@Singleton {y : A | In S y} (exist (In S) x H))
                   (@Singleton {y : A | In S y} (exist (In S) x H))) by
      now repeat intro. split; repeat intro.
  - destruct H3. rewrite H2 in H0 at 1. red in H0.
    specialize (H0 (exist _ x0 H4) H3). inversion H0. constructor.
  - inversion H3. subst x0. split; auto. rewrite H2 in H0 at 2.
    specialize (H0 (exist _ x H)). red in H0. simpl in H0. apply H0. constructor.
Qed.

Lemma isolated_in_set_in_subspace:
  forall {A} {Ao: OpenSet A} (x: A) (S: Ensemble A) (H: isolated_in_set x S),
      isolated_in_subspace x S (proj1 H).
Proof.
  intros. pose proof H. red in H0 |- *. destruct H0 as [? [U [? ?]]]. red.
  unfold open, subspace_open. exists U; auto. apply Extensionality_Ensembles.
  assert (Included (Singleton x) (Singleton x)) by now repeat intro.
  split; repeat intro.
  - inversion H4. subst x0. red. simpl. rewrite <- H2 in H3 at 2.
    specialize (H3 x (In_singleton A x)). now destruct H3.
  - red in H4. destruct x0 as [y ?]. simpl in H4. rewrite <- H2 in H3 at 1.
    specialize (H3 _ (Intersection_intro A _ _ _ H4 i)). inversion H3. subst y.
    replace i with (proj1 H). 1: constructor. apply proof_irrelevance.
Qed.
