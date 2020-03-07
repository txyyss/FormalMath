Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Image.

Arguments In {_}.
Arguments Union {_}.
Arguments Intersection {_}.
Arguments Empty_set {_}.
Arguments Full_set {_}.
Arguments Included {_}.
Arguments Couple {_}.

Arguments Im {_ _}.

Definition Family (A: Type) := Ensemble (Ensemble A).

Inductive FamilyUnion {A: Type} (F: Family A): Ensemble A :=
  FamilyUnion_intro: forall (S: Ensemble A) (x: A),
    In F S -> In S x -> In (FamilyUnion F) x.

Lemma empty_family_union: forall A,
    FamilyUnion (@Empty_set (Ensemble A)) = Empty_set.
Proof.
  intros. apply Extensionality_Ensembles.
  split; red; intros; unfold In in *; [destruct H|]; easy.
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
