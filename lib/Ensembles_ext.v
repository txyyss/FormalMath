Require Export Coq.Sets.Ensembles.

Arguments In {_}.
Arguments Union {_}.
Arguments Intersection {_}.
Arguments Empty_set {_}.
Arguments Full_set {_}.
Arguments Included {_}.
Arguments Couple {_}.

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
