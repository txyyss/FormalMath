Generalizable All Variables.

Require Import FormalMath.Topology.TopologicalSpace.
Require Import Coq.Logic.ClassicalChoice.

Section SubspaceTopology.

  Context `{TopologicalSpace A}.

  Definition subspace_open (S: Ensemble A): OpenSet {x: A | In S x} :=
    fun u => exists (O: Ensemble A),
        open O /\ Im u (@proj1_sig A _) = Intersection S O.

  Lemma subspace_topology:
    forall (S: Ensemble A), @TopologicalSpace {x: A | In S x} (subspace_open S).
  Proof.
    intros. split; unfold open, subspace_open; intros.
    - exists Full_set. split.
      + apply full_open.
      + apply Extensionality_Ensembles. split; repeat intro; destruct H0.
        * destruct x as [x ?]. simpl in *. subst. split; easy.
        * exists (exist _ x H0); easy.
    - assert (forall m: {s : Ensemble {x : A | In S x} | In f s},
                 exists O: Ensemble A,
                   open O /\ Im (proj1_sig m) (@proj1_sig A _) = Intersection S O). {
        intros [? ?]. apply H0. now simpl. }
      destruct (choice _ H1) as [func ?]. clear H0 H1. exists (IndexedUnion func).
      split.
      + rewrite indexed_to_family_union. apply any_union_open. intros.
        unfold imageFamily in H0. destruct H0.
        specialize (H2 x). destruct H2. now rewrite H1.
      + rewrite intersection_indexed_union, indexed_to_family_union.
        rewrite image_family_union. f_equal. unfold imageFamily.
        apply Extensionality_Ensembles. split; repeat intro; destruct H0.
        * specialize (H2 (exist _ x H0)). destruct H2. simpl in H3.
          exists (exist _ x H0). 1: constructor. now subst y.
        * specialize (H2 x). destruct H2. destruct x as [s ?]. simpl in *.
          exists s. auto. now subst y.
    - destruct H0 as [O1 [? ?]]. destruct H1 as [O2 [? ?]].
      exists (Intersection O1 O2). split.
      + now apply intersection_open.
      + rewrite injective_image_intersection.
        * rewrite intersection_distr. f_equal; auto.
        * repeat intro. destruct x as [x ?]. destruct y as [y ?]. simpl in H4. subst.
          f_equal. apply proof_irrelevance.
  Qed.

  Definition connected_region (U: Ensemble A): Prop :=
    connected {x: A | In U x} (subspace_open U) (subspace_topology U).

  Definition compact_region (U: Ensemble A): Prop :=
    compact {x: A | In U x} (subspace_open U) (subspace_topology U).

End SubspaceTopology.
