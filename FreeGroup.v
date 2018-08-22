Require Export FormalMath.Group.

Section FREE_GROUP.

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

  Lemma double_opposite: forall a, opposite (opposite a) == a.
  Proof. intros. destruct a; simpl; auto. Qed.

  Inductive word_equiv: relation Word :=
  | word_equiv_pair: forall (x y: Word) s,
      word_equiv (x ++ y) (x ++ s :: opposite s :: y)
  | word_equiv_refl: forall x, word_equiv x x
  | word_equiv_symm: forall x y, word_equiv x y -> word_equiv y x
  | word_equiv_trans: forall x y z, word_equiv x y -> word_equiv y z -> word_equiv x z.

  Global Instance free_equiv: Equiv Word := word_equiv.
  Global Instance free_binop: BinOp Word := fun x y => x ++ y.
  Global Instance free_gunit: GrUnit Word := nil.
  Global Instance free_neg: Negate Word := fun x => map opposite (rev x).

  Instance: Setoid Word.
  Proof.
    constructor; unfold equiv, free_equiv; repeat intro;
      [apply word_equiv_refl | now apply word_equiv_symm |
       now apply word_equiv_trans with y].
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) free_binop.
  Proof.
    constructor. unfold free_binop. transitivity (x ++ y0).
    - induction H; [| reflexivity | now symmetry | now transitivity (y ++ y0)].
      rewrite !app_ass. simpl. symmetry. apply word_equiv_pair.
    - induction H0; [| reflexivity | now symmetry | now transitivity (x ++ y0)].
      rewrite <- !app_ass. symmetry. apply word_equiv_pair.
  Qed.

  Instance: Proper ((=) ==> (=)) free_neg.
  Proof.
    constructor. unfold free_neg.
    induction H; [| reflexivity | now symmetry |
                  now transitivity (map opposite (rev y))]. rewrite !rev_app_distr.
    simpl. rewrite !app_ass, <- !app_comm_cons, !app_nil_l, !map_app. simpl.
    rewrite double_opposite. symmetry. apply word_equiv_pair.
  Qed.

  Global Instance freeGroup: Group Word.
  Proof.
    constructor; try apply _; intros;
      unfold bi_op, free_binop, one, free_gunit, neg, free_neg.
    - now rewrite app_ass.
    - now rewrite app_nil_l.
    - induction x; simpl; auto. rewrite map_app. simpl.
      rewrite app_ass, <- app_comm_cons, app_nil_l.
      transitivity (map opposite (rev x) ++ x); auto.
      rewrite <- (double_opposite a) at 2. symmetry. constructor.
  Qed.

  Definition fp_condition (l: list Word) := normal_gen (fun w => In w l).

  Goal forall l: list Word, Group (Quotient Word (fp_condition l)).
  Proof. apply _. Qed.

End FREE_GROUP.

Arguments Pe [_] _.
Arguments Ne [_] _.
