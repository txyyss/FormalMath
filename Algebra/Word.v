Section WORD.

  Variable A : Type.

  Inductive Alphabet : Type :=
  | Pe: A -> Alphabet
  | Ne: A -> Alphabet.

  Definition Word := list Alphabet.

  Definition opposite (letter: Alphabet) : Alphabet :=
    match letter with
    | Pe x => Ne x
    | Ne x => Pe x
    end.

  Lemma double_opposite: forall a, opposite (opposite a) = a.
  Proof. intros. destruct a; simpl; auto. Qed.

End WORD.

Arguments Pe [_] _.
Arguments Ne [_] _.
