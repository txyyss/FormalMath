Require Export FormalMath.Word.
Require Export FormalMath.Group.

Section FREE_GROUP.

  Variable A : Type.

  Inductive word_equiv: relation (Word A):=
  | word_equiv_pair: forall (x y: Word A) s,
      word_equiv (x ++ y) (x ++ s :: opposite A s :: y)
  | word_equiv_refl: forall x, word_equiv x x
  | word_equiv_symm: forall x y, word_equiv x y -> word_equiv y x
  | word_equiv_trans: forall x y z, word_equiv x y -> word_equiv y z -> word_equiv x z.

  Global Instance free_equiv: Equiv (Word A) := word_equiv.
  Global Instance free_binop: BinOp (Word A):= fun x y => x ++ y.
  Global Instance free_gunit: GrUnit (Word A) := nil.
  Global Instance free_neg: Negate (Word A) := fun x => map (opposite A) (rev x).

  Instance: Setoid (Word A).
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
                  now transitivity (map (opposite A) (rev y))]. rewrite !rev_app_distr.
    simpl. rewrite !app_ass, <- !app_comm_cons, !app_nil_l, !map_app. simpl.
    rewrite double_opposite. symmetry. apply word_equiv_pair.
  Qed.

  Global Instance freeGroup: Group (Word A).
  Proof.
    constructor; try apply _; intros;
      unfold bi_op, free_binop, one, free_gunit, neg, free_neg.
    - now rewrite app_ass.
    - now rewrite app_nil_l.
    - induction x; simpl; auto. rewrite map_app. simpl.
      rewrite app_ass, <- app_comm_cons, app_nil_l.
      transitivity (map (opposite A) (rev x) ++ x); auto.
      rewrite <- (double_opposite A a) at 2. symmetry. constructor.
  Qed.

End FREE_GROUP.

Section FINITELY_PRESENTED_GROUP.

  Variable A : Type.
  
  Definition FP_Cond (relators : list (Word A)) :=
    normal_gen (fun w => In w relators).
  
End FINITELY_PRESENTED_GROUP.
