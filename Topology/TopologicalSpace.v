(* The file takes https://github.com/coq-community/topology as reference *)

Generalizable All Variables.

Require Export FormalMath.lib.Sets_ext.
Require Import FormalMath.lib.FiniteType.
Require Import Stdlib.Logic.ClassicalChoice.

Class OpenSet (A: Type) := open: Ensemble A -> Prop.
#[global] Typeclasses Transparent OpenSet.

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

Class HausdorffSpace (A: Type) {Ao: OpenSet A}: Type :=
  Hausdorff_prop: forall (x1 x2: A),
    x1 <> x2 ->
    { U1: Ensemble A & { U2: Ensemble A |
      open U1 /\ open U2 /\ In U1 x1 /\ In U2 x2 /\ Intersection U1 U2 = Empty_set } }.

Section TOPOLOGICAL_SPACE_PROP.

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

  Definition interior (S: Ensemble A): Ensemble A :=
    FamilyUnion (fun U => open U /\ Included U S).

  Lemma interior_open: forall S, open (interior S).
  Proof. intro. apply any_union_open. intros. red in H. now destruct H. Qed.

  Lemma interior_Included: forall S, Included (interior S) S.
  Proof. repeat intro. destruct H. destruct H. auto with sets. Qed.

  Lemma open_interior_self: forall S, open S -> interior S = S.
  Proof.
    intros. apply Extensionality_Ensembles. split.
    - apply interior_Included.
    - repeat intro. exists S; auto with sets.
  Qed.

  Lemma interior_maximal: forall U S,
      open U -> Included U S -> Included U (interior S).
  Proof. repeat intro. exists U; auto with sets. Qed.

  Lemma Included_interior_open: forall S, Included S (interior S) -> open S.
  Proof.
    intros. replace S with (interior S). 1: apply interior_open.
    apply Extensionality_Ensembles. split; auto. apply interior_Included.
  Qed.

  Definition closure (S: Ensemble A): Ensemble A :=
    FamilyIntersection (fun U => closed U /\ Included S U).

  Lemma closure_closed: forall S, closed (closure S).
  Proof. intros. apply any_intersection_closed. intros. red in H. now destruct H. Qed.

  Lemma closure_Included: forall S, Included S (closure S).
  Proof. repeat intro. constructor. intros U ?. destruct H0. auto with sets. Qed.

  Lemma closed_closure_self: forall S, closed S -> closure S = S.
  Proof.
    intros. apply Extensionality_Ensembles. split.
    - repeat intro. destruct H0. apply H0. auto with sets.
    - apply closure_Included.
  Qed.

  Lemma closure_minimal: forall U S,
      closed U -> Included S U -> Included (closure S) U.
  Proof. repeat intro. destruct H1. apply H1. auto with sets. Qed.

  Definition isolated (x: A): Prop := open (Singleton x).

  Definition isolated_in_set (x: A) (S: Ensemble A): Prop :=
    In S x /\ exists U, open U /\ Intersection U S = Singleton x.

  Definition discrete (U: Ensemble A): Prop :=
    forall x, In U x -> isolated_in_set x U.

  Definition connected: Prop :=
    forall (S: Ensemble A), open S -> closed S -> S = Empty_set \/ S = Full_set.

  Definition compact: Prop :=
    forall (C: Family A),
      (forall U, In C U -> open U) -> FamilyUnion C = Full_set ->
      exists (fC: Family A), Finite fC /\ Included fC C /\ FamilyUnion fC = Full_set.

  Definition compact_set (S: Ensemble A): Prop :=
    forall (C: Family A),
      (forall U, In C U -> open U) -> Included S (FamilyUnion C) ->
      exists (fC: Family A), Finite fC /\ Included fC C /\
                             Included S (FamilyUnion fC).

  Lemma compact_set_on_indexed_covers:
    forall (S: Ensemble A) (Idx: Type) (C: IndexedFamily Idx A),
      compact_set S ->
      (forall idx: Idx, open (C idx)) -> Included S (IndexedUnion C) ->
      exists idxSet: Ensemble Idx,
        Finite idxSet /\
        Included S (IndexedUnion (fun i: {x: Idx | In idxSet x} => C (proj1_sig i))).
  Proof.
    intros. destruct (H (imageFamily C)) as [subcover].
    - intros. destruct H2. subst y. apply H0.
    - now rewrite indexed_to_family_union in H1.
    - destruct H2 as [? []]. apply Finite_FiniteT in H2.
      destruct (finite_choice _ _
                              (fun (U:{x:Ensemble A | In subcover x}) (a:Idx) =>
                                 proj1_sig U = C a)) as [choice_fun]; auto.
      + intros. destruct x as [x]. simpl. apply H3 in i. destruct i. exists x; auto.
      + exists (Im Full_set choice_fun). split.
        * apply FiniteT_img; auto. intros. apply classic.
        * repeat intro. apply H4 in H6. destruct H6.
          assert (In (Im Full_set choice_fun) (choice_fun (exist _ S0 H6))). {
            exists (exist _ S0 H6); constructor. }
          exists (exist _ (choice_fun (exist _ S0 H6)) H8). simpl. now rewrite <- H5.
  Qed.

  Lemma finite_intersection_open: forall {Idx: Type} (F:IndexedFamily Idx A),
      FiniteT Idx -> (forall i: Idx, open (F i)) -> open (IndexedIntersection F).
  Proof.
    intros. induction H.
    - rewrite empty_indexed_intersection. apply full_open.
    - assert (IndexedIntersection F =
              Intersection (IndexedIntersection (fun x => F (Some x))) (F None)). {
        apply Extensionality_Ensembles; split; red; intros.
        - destruct H1. constructor.
          + constructor. intros; apply H1.
          + apply H1.
        - destruct H1. destruct H1. constructor. intros.
          destruct i; [apply H1 | apply H2]. }
      rewrite H1. apply intersection_open.
      + apply IHFiniteT. intros; apply H0.
      + apply H0.
    - destruct H1.
      assert (IndexedIntersection F = IndexedIntersection (fun x => F (f x))). {
        apply Extensionality_Ensembles; split; red; intros.
        - constructor. destruct H3. intro; apply H3.
        - constructor. destruct H3. intro; rewrite <- H2 with i. apply H3. }
      rewrite H3. apply IHFiniteT. intro; apply H0.
  Qed.

  (* Theorem 26.3 of Topology *)
  Lemma compact_of_Hausdorff_closed:
    forall {Hau: HausdorffSpace A} (S: Ensemble A), compact_set S -> closed S.
  Proof.
    intros. red. apply Included_interior_open. repeat intro.
    assert (forall y, In S y -> y <> x). {
      intros. hnf in H0. intro. apply H0. now subst. }
    remember (fun yS: {z: A | In S z} =>
                let whole := Hausdorff_prop (proj1_sig yS) x (H1 _ (proj2_sig yS)) in
                (projT1 whole, proj1_sig (projT2 whole))).
    remember ((fun x: {z : A | In S z} => fst (p x)) :
                IndexedFamily {z : A | In S z} A) as V.
    assert (forall idx: {z: A | In S z}, open (V idx)). {
      intros. subst. simpl. destruct idx as [z]. simpl. unfold Hausdorff_prop.
      destruct Hau. destruct s. destruct a. simpl. easy. }
    assert (Included S (IndexedUnion V)). {
      repeat intro. exists (exist _ x0 H3). subst. simpl. unfold Hausdorff_prop.
      destruct Hau. destruct s. simpl. tauto. }
    destruct (compact_set_on_indexed_covers _ _ _ H H2 H3) as [idxSet []].
    remember ((fun x: {z : A | In S z} => snd (p x)) :
                IndexedFamily {z : A | In S z} A) as U.
    hnf. exists (IndexedIntersection
                   (fun i : {x : {z : A | In S z} | In idxSet x} => U (proj1_sig i))).
    - hnf. split.
      + apply finite_intersection_open.
        * now apply Finite_FiniteT.
        * intros. subst. simpl. unfold Hausdorff_prop. destruct Hau. simpl.
          destruct s as [? [? []]]. now simpl.
      + repeat intro. specialize (H5 _ H7). inversion H5. subst x1. clear H5.
        inversion H6. subst x1. clear H6. specialize (H5 i). subst. simpl in H5, H8.
        unfold Hausdorff_prop in H8, H5. destruct Hau. simpl in H8, H5.
        destruct s. simpl in H5. destruct a as [_ [_ [_ [_ ?]]]].
        assert (In (Intersection x1 x2) x0) by now constructor. rewrite H6 in H9.
        inversion H9.
    - hnf. constructor. intros. destruct i. simpl. subst. simpl. unfold Hausdorff_prop.
      destruct x0. simpl. destruct Hau. simpl. destruct s. simpl. tauto.
  Qed.

End TOPOLOGICAL_SPACE_PROP.
