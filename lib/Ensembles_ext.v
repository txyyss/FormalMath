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
