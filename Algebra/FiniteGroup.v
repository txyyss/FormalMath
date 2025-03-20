Require Import FormalMath.Algebra.Group.
Require Import Stdlib.Sorting.SetoidList.
Require Import Stdlib.Sorting.SetoidPermutation.

Section FINITE_GROUP.

  Context `{G: Group A}.

  Lemma finite_group_left_perm: forall l,
      (forall a: A, InA Ae a l) -> NoDupA Ae l ->
      forall x, PermutationA Ae l (map (x &) l).
  Proof.
    intros. pose proof gr_as_setoid. apply NoDupA_equivlistA_PermutationA; auto.
    - clear H. induction H0; simpl. 1: easy. constructor; auto.
      intro. rewrite InA_alt in H2. destruct H2 as [y [? ?]]. rewrite in_map_iff in H3.
      destruct H3 as [x1 [? ?]]. rewrite <- H3 in H2.
      assert (x & x0 = x & x1) by easy. rewrite <- eq_left in H5.
      rewrite H5 in H. apply H. apply In_InA; auto.
    - intro y. split; intro. 2: apply H. specialize (H (neg x & y)).
      rewrite InA_alt in H |- *. destruct H as [z [? ?]]. exists (x & z). split.
      * rewrite <- H. rewrite <- op_assoc.
        autorewrite with group; [easy | apply G..].
      * now apply in_map.
  Qed.

End FINITE_GROUP.
