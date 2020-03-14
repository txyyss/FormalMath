Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Image.

Arguments In {_}.
Arguments Union {_}.
Arguments Intersection {_}.
Arguments Empty_set {_}.
Arguments Full_set {_}.
Arguments Included {_}.
Arguments Couple {_}.
Arguments Complement {_}.

Arguments Im {_ _}.
Arguments injective {_ _}.

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

Definition IndexedFamily (Idx A: Type) := Idx -> Ensemble A.

Inductive IndexedUnion {Idx A: Type} (F: IndexedFamily Idx A): Ensemble A :=
  IndexedUnion_intro: forall (i: Idx) (x: A), In (F i) x -> In (IndexedUnion F) x.

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
