(* The file takes https://github.com/coq-community/topology as reference *)

Generalizable All Variables.

Require Export FormalMath.lib.Ensembles_ext.
Require Import Coq.Logic.ClassicalChoice.

Class OpenSet (A: Type) := open: Ensemble A -> Prop.
Typeclasses Transparent OpenSet.

Class TopologicalSpace (A: Type) {Ao: OpenSet A} : Prop :=
  {
    full_open: open Full_set;
    any_union_open: forall (f: Family A),
        (forall s, In f s -> open s) -> open (FamilyUnion f);
    intersection_open: forall (s1 s2: Ensemble A),
        open s1 -> open s2 -> open (Intersection s1 s2);
  }.

Definition topology_basis {A: Type} (B: Family A): Prop :=
  (forall (x: A), exists b, In B b /\ In b x) /\
  (forall (x: A) (b1 b2: Ensemble A),
      In B b1 -> In B b2 -> In (Intersection b1 b2) x ->
      exists b3, In B b3 /\ In b3 x /\ Included b3 (Intersection b1 b2)).

Definition basis_to_open {A} (B: Family A): OpenSet A :=
  fun u => forall x, In u x -> exists b, In B b /\ In b x /\ Included b u.

Lemma topology_basis_TopologicalSpace: forall A (B: Family A),
    topology_basis B -> @TopologicalSpace A (basis_to_open B).
Proof.
  intros. destruct H as [?B ?B]. split; unfold open, basis_to_open; intros.
  - destruct (B0 x) as [b [? ?]]. exists b. repeat split; auto.
  - destruct H0. destruct (H _ H0 _ H1) as [b [? [? ?]]]. exists b.
    repeat split; auto. repeat intro. exists S; auto.
  - destruct H1. destruct (H _ H1) as [b1 [? [? ?]]].
    destruct (H0 _ H2) as [b2 [? [? ?]]].
    assert (In (Intersection b1 b2) x) by (split; easy).
    specialize (B1 _ _ _ H3 H6 H9). destruct B1 as [b3 [? [? ?]]].
    exists b3. unfold Included in H12. repeat split; auto; destruct (H12 _ H13); auto.
Qed.

Lemma topology_basis_open_is_all_union: forall A (B: Family A),
    topology_basis B ->
    forall S, basis_to_open B S <->
              exists (F: Family A), Included F B /\ S = FamilyUnion F.
Proof.
  intros. destruct H as [?B ?B]. unfold basis_to_open. split; intros.
  - assert (forall m: {x | In S x},
               exists b, In B b /\ In b (proj1_sig m) /\ Included b S). {
      intros. destruct m. simpl. now apply H. } destruct (choice _ H0) as [f ?].
    exists (imageFamily f). split.
    + repeat intro. destruct H2. subst. now destruct (H1 x).
    + rewrite <- indexed_to_family_union. apply Extensionality_Ensembles.
      split; red; intros.
      * destruct (H1 (exist _ x H2)) as [? [? ?]]. simpl in *.
        exists (exist _ x H2); auto.
      * destruct H2. destruct (H1 i) as [? [? ?]]. auto.
  - destruct H as [F [? ?]]. destruct (B0 x) as [b [? ?]]. rewrite H1 in H0.
    inversion H0. subst. exists S0. repeat split; auto. repeat intro. exists S0; auto.
Qed.

Section TopologicalSpaceProp.

  Context `{T: TopologicalSpace A}.

  Lemma empty_open: open Empty_set.
  Proof. rewrite <- empty_family_union. apply any_union_open. intros. easy. Qed.

  Lemma union_open: forall (u v: Ensemble A), open u -> open v -> open (Union u v).
  Proof.
    intros.
    assert (Union u v = FamilyUnion (Couple u v)). {
      apply Extensionality_Ensembles. split; red; intros.
      - destruct H1; [exists u | exists v]; auto with sets.
      - destruct H1. destruct H1; [left | right]; easy.
    } rewrite H1. apply any_union_open. intros. now destruct H2.
  Qed.

  Definition closed (u: Ensemble A): Prop := open (Complement u).

  Lemma closed_compl_open: forall (S: Ensemble A), closed (Complement S) -> open S.
  Proof. intros. red in H. now rewrite Complement_Complement in H. Qed.

  Lemma full_closed: closed Full_set.
  Proof. red. rewrite Full_compl_empty. apply empty_open. Qed.

  Lemma empty_closed: closed Empty_set.
  Proof. red. rewrite Empty_compl_full. apply full_open. Qed.

  Lemma any_intersection_closed: forall (f: Family A),
      (forall s, In f s -> closed s) -> closed (FamilyIntersection f).
  Proof.
    intros. red. rewrite family_intersection_compl_union. apply any_union_open.
    intros. red in H0. specialize (H _ H0). now apply closed_compl_open.
  Qed.

  Lemma union_closed: forall (s1 s2: Ensemble A),
      closed s1 -> closed s2 -> closed (Union s1 s2).
  Proof. intros. red. rewrite De_Morgan_law1. apply intersection_open; auto. Qed.

End TopologicalSpaceProp.
