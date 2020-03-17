Require Import FormalMath.Algebra.Group.

Class GrAct (A X: Type) := gr_act : A -> X -> X.
Infix "⊙" := gr_act (at level 50): math_scope.
Notation "(⊙)" := gr_act (only parsing) : math_scope.
Notation "( x ⊙)" := (gr_act x) (only parsing) : math_scope.
Notation "(⊙ x )" := (fun y => y ⊙ x) (only parsing) : math_scope.

Class GroupAction (A X: Type) `{G: Group A} {Ga: GrAct A X}: Prop := {
  gr_act_prop :> Proper ((=) ==> (==) ==> (==)) (⊙);
  gr_act_ident: forall x: X, one ⊙ x == x;
  gr_act_compat: forall (g h: A) (x: X), (g & h) ⊙ x == g ⊙ (h ⊙ x); }.

Section SUBGROUP_ACTION.

  Context `{SA: SubGroupCondition A P}.
  Context `{Ga: GrAct A X}.
  Context `{GRA: !GroupAction A X}.

  Global Instance subgroup_act: GrAct (Subpart A P) X := fun g x => 'g ⊙ x.

  Instance: Proper ((=) ==> (==) ==> (==)) subgroup_act.
  Proof.
    intros [x] [y] ? a b ?. unfold subgroup_act. subst. red in H0.
    unfold subgroup_equiv in H0. unfold cast, subgroup_rep in *. simpl in *.
    now rewrite H0.
  Qed.

  Global Instance subgroup_action: GroupAction (Subpart A P) X.
  Proof.
    constructor.
    - apply _.
    - intros. unfold one, subgroup_gunit, gr_act, subgroup_act, cast, subgroup_rep.
      simpl. apply gr_act_ident.
    - intros [g] [h] ?. unfold bi_op, gr_act, subgroup_act, subgroup_binop, cast,
                        subgroup_rep. simpl. apply gr_act_compat.
  Qed.

End SUBGROUP_ACTION.
