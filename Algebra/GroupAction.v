Require Import FormalMath.Algebra.Group.
Require Import FormalMath.lib.Sets_ext.

Class GrAct (A X: Type) := gr_act : A -> X -> X.
Infix "⊙" := gr_act (at level 50): math_scope.
Notation "(⊙)" := gr_act (only parsing) : math_scope.
Notation "( x ⊙)" := (gr_act x) (only parsing) : math_scope.
Notation "(⊙ x )" := (fun y => y ⊙ x) (only parsing) : math_scope.

Class GroupAction (A X: Type) `{G: Group A} {Ga: GrAct A X}: Prop := {
  gr_act_prop :: Proper ((=) ==> (==) ==> (==)) (⊙);
  gr_act_ident: forall x: X, one ⊙ x == x;
  gr_act_compat: forall (g h: A) (x: X), (g & h) ⊙ x == g ⊙ (h ⊙ x); }.

Section GROUPACTION_PROP.

  Variable (A X: Type).
  Context `{GA: GroupAction A X}.

  Definition orbit (x: X): Ensemble X := Im Full_set (⊙ x).

  Lemma orbit_the_same: forall (g: A) (x: X), orbit x == orbit (g ⊙ x).
  Proof.
    intros. apply Extensionality_Ensembles. split; repeat intro; unfold orbit in *.
    - destruct H as [g' ?]. exists (g' & (neg g)). 1: constructor.
      now rewrite <- gr_act_compat, op_assoc, neg_left, one_right.
    - destruct H as [g' ?]. exists (g' & g). 1: constructor.
      now rewrite gr_act_compat.
  Qed.

End GROUPACTION_PROP.

Section SUBGROUP_ACTION.

  Context `{SA: SubGroupCondition A P}.
  Context `{Ga: GrAct A X}.
  Context `{GRA: !GroupAction A X}.

  #[global] Instance subgroup_act: GrAct (Subpart A P) X := fun g x => 'g ⊙ x.

  Instance: Proper ((=) ==> (==) ==> (==)) subgroup_act.
  Proof.
    intros [x] [y] ? a b ?. unfold subgroup_act. subst. red in H0.
    unfold subgroup_equiv in H0. unfold cast, subgroup_rep in *. simpl in *.
    now rewrite H0.
  Qed.

  #[global] Instance subgroup_action: GroupAction (Subpart A P) X.
  Proof.
    constructor.
    - apply _.
    - intros. unfold one, subgroup_gunit, gr_act, subgroup_act, cast, subgroup_rep.
      simpl. apply gr_act_ident.
    - intros [g] [h] ?. unfold bi_op, gr_act, subgroup_act, subgroup_binop, cast,
                        subgroup_rep. simpl. apply gr_act_compat.
  Qed.

End SUBGROUP_ACTION.
