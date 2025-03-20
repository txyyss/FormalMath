Require Export Stdlib.Sets.Ensembles.
Require Export Stdlib.Sets.Image.
Require Stdlib.Vectors.FinFun.

Arguments In {_}.
Arguments Union {_}.
Arguments Intersection {_}.
Arguments Empty_set {_}.
Arguments Full_set {_}.
Arguments Included {_}.
Arguments Couple {_}.
Arguments Complement {_}.
Arguments Singleton {_}.
Arguments Add {_}.
Arguments Setminus {_}.

Arguments Im {_ _}.
Arguments injective {_ _}.

Arguments Finite {_}.

Lemma Full_compl_empty: forall (A: Type), @Complement A Full_set = Empty_set.
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro; [|inversion H].
  hnf in H. exfalso. apply H. constructor.
Qed.

Lemma Empty_compl_full: forall (A: Type), @Complement A Empty_set = Full_set.
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro.
  - constructor.
  - inversion H0.
Qed.

Lemma De_Morgan_law1: forall (A: Type) (s1 s2: Ensemble A),
    Complement (Union s1 s2) = Intersection (Complement s1) (Complement s2).
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro.
  - hnf in H. constructor; intro; apply H; auto with sets.
  - destruct H. destruct H0; [apply H | apply H1]; easy.
Qed.

Lemma injective_image_intersection: forall (U V: Type) (X1 X2: Ensemble U) (f: U -> V),
    injective f -> Im (Intersection X1 X2) f = Intersection (Im X1 f) (Im X2 f).
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro.
  - destruct H0. destruct H0. split; exists x; auto.
  - destruct H0. destruct H0, H1. exists x; auto.
    assert (x0 = x) by (apply H; rewrite <- H2, <- H3; easy). subst. split; auto.
Qed.

Lemma intersection_distr: forall (U: Type) (A B C: Ensemble U),
    Intersection A (Intersection B C) =
    Intersection (Intersection A B) (Intersection A C).
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro; destruct H.
  - destruct H0. split; split; auto.
  - destruct H, H0. split; [|split]; auto.
Qed.

Definition Family (A: Type) := Ensemble (Ensemble A).

Inductive FamilyUnion {A: Type} (F: Family A): Ensemble A :=
  FamilyUnion_intro: forall (S: Ensemble A) (x: A),
    In F S -> In S x -> In (FamilyUnion F) x.

Inductive FamilyIntersection {A: Type} (F: Family A): Ensemble A :=
  FamilyIntersection_intro: forall (x: A),
    (forall S: Ensemble A, In F S -> In S x) -> In (FamilyIntersection F) x.

Lemma empty_family_union: forall A,
    FamilyUnion (@Empty_set (Ensemble A)) = Empty_set.
Proof.
  intros. apply Extensionality_Ensembles.
  split; red; intros; unfold In in *; [destruct H|]; easy.
Qed.

Lemma empty_family_intersection: forall A,
    FamilyIntersection (@Empty_set (Ensemble A)) = Full_set.
Proof.
  intros. apply Extensionality_Ensembles. split; red; intros; constructor.
  intros. inversion H0.
Qed.

Lemma family_intersection_compl_union: forall A (F: Family A),
    Complement (FamilyIntersection F) = FamilyUnion (fun S => In F (Complement S)).
Proof.
  intros. apply Extensionality_Ensembles. split; red; intros.
  - apply NNPP. intro. apply H. clear H. constructor. intros. apply NNPP. intro.
    contradict H0. exists (Complement S); auto. red. now rewrite Complement_Complement.
  - destruct H. red in H. intro. destruct H1. specialize (H1 _ H). now apply H1.
Qed.

Lemma image_family_union: forall (U V: Type) (F: Family U) (f: U -> V),
    Im (FamilyUnion F) f = FamilyUnion (Im F (fun u => Im u f)).
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro; destruct H.
  - destruct H. exists (Im S f).
    + exists S; auto.
    + exists x; auto.
  - destruct H. subst. destruct H0. exists x; auto. exists x0; auto.
Qed.

Definition interSum {A: Type} (U S: Ensemble A): Ensemble {x : A | In S x} :=
  fun m => In U (proj1_sig m).

Definition FamilyIntersectSet {A: Type} (F: Family A) (S: Ensemble A):
  Family {x : A | In S x} := Im F (fun f y => In f (proj1_sig y)).

Lemma union_FIS: forall {A} (F: Family A) (S: Ensemble A),
    FamilyUnion (FamilyIntersectSet F S) = interSum (FamilyUnion F) S.
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro.
  - unfold interSum. destruct x as [x ?]. inversion H. subst. clear H.
    red. simpl. inversion H0. subst. clear H0. red in H1. simpl in H1. exists x0; auto.
  - unfold interSum in H. red in H. destruct x as [x ?]. simpl in H.
    destruct H as [U ?]. exists (interSum U S).
    + exists U; auto.
    + unfold interSum. red. now simpl.
Qed.

Definition IndexedFamily (Idx A: Type) := Idx -> Ensemble A.

Inductive IndexedUnion {Idx A: Type} (F: IndexedFamily Idx A): Ensemble A :=
  IndexedUnion_intro: forall (i: Idx) (x: A), In (F i) x -> In (IndexedUnion F) x.

Inductive IndexedIntersection {Idx A: Type} (F: IndexedFamily Idx A): Ensemble A :=
  IndexedIntersection_intro: forall (x: A),
    (forall i: Idx, In (F i) x) -> In (IndexedIntersection F) x.

Lemma empty_indexed_union: forall {A:Type} (F:IndexedFamily False A),
    IndexedUnion F = Empty_set.
Proof. intros. apply Extensionality_Ensembles. split; red; intros; now destruct H. Qed.

Definition imageFamily {Idx A} (F: IndexedFamily Idx A): Family A := Im Full_set F.

Lemma indexed_to_family_union: forall {Idx A} (F: IndexedFamily Idx A),
    IndexedUnion F = FamilyUnion (imageFamily F).
Proof.
  intros. apply Extensionality_Ensembles. split; red; intros; destruct H.
  - exists (F i); auto. exists i; auto. constructor.
  - destruct H. subst. now exists x0.
Qed.

Lemma intersection_indexed_union:
  forall (Idx A: Type) (F: IndexedFamily Idx A) (S: Ensemble A),
    Intersection S (IndexedUnion F) =
    IndexedUnion (fun id => Intersection S (F id)).
Proof.
  intros. apply Extensionality_Ensembles. split; repeat intro; destruct H.
  - destruct H0. exists i. now split.
  - destruct H. split; auto. now exists i.
Qed.

Lemma Finite_iff: forall {A} (S: Ensemble A),
    Finite S <-> exists l, forall x, In S x -> List.In x l.
Proof.
  intros. split; intros.
  - induction H.
    + exists nil. intros. inversion H.
    + destruct IHFinite as [l ?]. exists (List.cons x l). intros y ?. destruct H2.
      * right. now apply H1.
      * inversion H2. subst x0. now left.
  - destruct H as [l ?]. revert S H. induction l; intros.
    + replace S with (@Empty_set A). 1: constructor. apply Extensionality_Ensembles.
      split; repeat intro.
      * inversion H0.
      * specialize (H _ H0). inversion H.
    + destruct (classic (In S a)).
      * specialize (IHl (Setminus S (Singleton a))).
        replace S with (Add (Setminus S (Singleton a)) a).
        -- constructor.
           ++ apply IHl. intros. destruct H1. specialize (H _ H1). destruct H; auto.
              subst. exfalso. apply H2. constructor.
           ++ intro. destruct H1. apply H2. constructor.
        -- apply Extensionality_Ensembles. split; repeat intro.
           ++ destruct H1.
              ** destruct H1. auto.
              ** inversion H1. now subst.
           ++ destruct (classic (x = a)).
              ** subst. right. constructor.
              ** left. split; auto. intro. inversion H3. subst. now apply H2.
      * apply IHl. intros. specialize (H _ H1). destruct H; auto.
        subst. contradiction.
Qed.

Definition sumAdd {A: Type} (S: Ensemble A) (a: A) (b: {x: A | In S x}):
  {x : A | In (Add S a) x} := let (y, i) := b in exist _ y (Add_intro1 A S a y i).

Lemma finite_sig_iff: forall {A} (S: Ensemble A),
    Finite S <-> FinFun.Finite {x: A | In S x}.
Proof.
  intros. split.
  - intros; induction H.
    + exists nil. intros [a]. inversion i.
    + rename A0 into S. destruct IHFinite as [l ?]. red in H1.
      exists (List.cons (exist _ x (Add_intro2 A S x)) (List.map (sumAdd S x) l)).
      red. intros [y]. destruct i.
      * right. specialize (H1 (exist _ x0 i)).
        apply (List.in_map (sumAdd S x)) in H1.
        replace (exist (fun x1 : A => In (Add S x) x1) x0
                       (Union_introl A S (Singleton x) x0 i)) with
            (sumAdd S x (exist (In S) x0 i)); auto.
        unfold sumAdd. f_equal. apply proof_irrelevance.
      * left. inversion i. subst x0. f_equal. apply proof_irrelevance.
  - intros. destruct H as [l ?]. red in H. rewrite Finite_iff.
    exists (List.map (@proj1_sig A (fun m => In S m)) l). intros.
    specialize (H (exist _ x H0)).
    apply (List.in_map (@proj1_sig A (fun m => In S m))) in H. now simpl in H.
Qed.

Lemma finite_type_full_iff: forall (A: Type),
    FinFun.Finite A <-> FinFun.Finite {x : A | In Full_set x}.
Proof.
  intros. split; intros; red in H |- *; destruct H as [l ?]; red in H.
  - exists (List.map (fun x => exist _ x (Full_intro A x)) l). red. intros.
    destruct a as [x ?]. specialize (H x).
    apply (List.in_map (fun y => exist _ y (Full_intro A y))) in H.
    replace (exist (fun x0 : A => In Full_set x0) x i) with
        (exist (In Full_set) x (Full_intro A x)); auto. f_equal.
    apply proof_irrelevance.
  - exists (List.map (@proj1_sig A (In Full_set)) l). red. intros.
    specialize (H (exist _ a (Full_intro A a))).
    apply (List.in_map (@proj1_sig A (In Full_set))) in H. now simpl in H.
Qed.


Lemma empty_indexed_intersection: forall {T:Type} (F:IndexedFamily False T),
    IndexedIntersection F = Full_set.
Proof.
  intros. apply Extensionality_Ensembles; red; split; red; intros; constructor.
  intros. easy.
Qed.
