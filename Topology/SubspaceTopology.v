Generalizable All Variables.

Require Import FormalMath.Topology.TopologicalSpace.
Require Import Coq.Logic.ClassicalChoice.

Section SUBSPACE_TOPOLOGY.

  Context `{T: TopologicalSpace A}.

  Definition subspace_open (S: Ensemble A): OpenSet {x: A | In S x} :=
    fun u => exists (O: Ensemble A),
        open O /\ Im u (@proj1_sig A _) = Intersection S O.

  Lemma subspace_topology:
    forall (S: Ensemble A), @TopologicalSpace {x: A | In S x} (subspace_open S).
  Proof.
    intros. split; unfold open, subspace_open; intros.
    - exists Full_set. split.
      + apply full_open.
      + apply Extensionality_Ensembles. split; repeat intro; destruct H.
        * destruct x as [x ?]. simpl in *. subst. split; easy.
        * exists (exist _ x H); easy.
    - assert (forall m: {s : Ensemble {x : A | In S x} | In f s},
                 exists O: Ensemble A,
                   open O /\ Im (proj1_sig m) (@proj1_sig A _) = Intersection S O). {
        intros [? ?]. apply H. now simpl. }
      destruct (choice _ H0) as [func ?]. clear H H0. exists (IndexedUnion func).
      split.
      + rewrite indexed_to_family_union. apply any_union_open. intros.
        unfold imageFamily in H. destruct H.
        specialize (H1 x). destruct H1. now rewrite H0.
      + rewrite intersection_indexed_union, indexed_to_family_union.
        rewrite image_family_union. f_equal. unfold imageFamily.
        apply Extensionality_Ensembles. split; repeat intro; destruct H.
        * specialize (H1 (exist _ x H)). destruct H1. simpl in H2.
          exists (exist _ x H). 1: constructor. now subst y.
        * specialize (H1 x). destruct H1. destruct x as [s ?]. simpl in *.
          exists s. auto. now subst y.
    - destruct H as [O1 [? ?]]. destruct H0 as [O2 [? ?]].
      exists (Intersection O1 O2). split.
      + now apply intersection_open.
      + rewrite injective_image_intersection.
        * rewrite intersection_distr. f_equal; auto.
        * repeat intro. destruct x as [x ?]. destruct y as [y ?]. simpl in H3. subst.
          f_equal. apply proof_irrelevance.
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
        intros. unfold open, subspace_open. destruct H2 as [f [? ?]].
        exists f. split. 1: now apply H0. subst U. apply Extensionality_Ensembles.
        split; repeat intro.
        - destruct H3. unfold interSum in H3. red in H3. destruct x as [x ?].
          simpl in *. subst y. now constructor.
        - destruct H3. exists (exist _ x H3). 2: now simpl. unfold interSum. red.
          now simpl. } specialize (H H2). clear H2.
      assert (FamilyUnion (FamilyIntersectSet C S) = @Full_set {x : A | In S x}). {
        apply Extensionality_Ensembles. split; repeat intro. 1: constructor.
        rewrite union_FIS. destruct x as [x ?]. clear H2. unfold interSum.
        red. simpl. auto. } specialize (H H2). clear H2. destruct H as [fCS [? [? ?]]].
      assert (forall su: { x | In fCS x},
                 exists f, In C f /\ proj1_sig su = interSum f S). {
        intros. destruct su as [x ?]. specialize (H2 x i).
        destruct H2 as [f' [? ?]]. simpl. exists f'. now split. } clear H2.
      destruct (choice _ H4) as [func ?]. clear H4. exists (imageFamily func).
      split; [|split].
      + unfold imageFamily. apply finite_image.
        now rewrite finite_sig_iff, <- finite_type_full_iff, <- finite_sig_iff.
  Abort.

End SUBSPACE_TOPOLOGY.

Lemma isolated_in_subspace_in_set:
  forall {A} {Ao: OpenSet A} (x: A) (S: Ensemble A) (H: In S x),
    isolated_in_subspace x S H -> isolated_in_set x S.
Proof.
  intros. red in H0 |- *. red in H0. split; auto. unfold open, subspace_open in H0.
  destruct H0 as [O [? ?]]. exists O. split; auto. rewrite Intersection_commutative.
  rewrite <- H1. apply Extensionality_Ensembles. split; repeat intro.
  - destruct H2. inversion H2. subst x0. simpl in H3. subst y. constructor.
  - inversion H2. subst x0. exists (exist _ x H). 1: constructor. now simpl.
Qed.

Lemma isolated_in_set_in_subspace:
  forall {A} {Ao: OpenSet A} (x: A) (S: Ensemble A) (H: isolated_in_set x S),
      isolated_in_subspace x S (proj1 H).
Proof.
  intros. pose proof H. red in H0 |- *. destruct H0 as [? [U [? ?]]]. red.
  unfold open, subspace_open. exists U. split; auto.
  rewrite Intersection_commutative, H2. apply Extensionality_Ensembles.
  split; repeat intro.
  - destruct H3. inversion H3. subst x0. simpl in H4. subst. constructor.
  - exists (exist _ x (proj1 H)). 1: constructor. inversion H3. subst. now simpl.
Qed.
