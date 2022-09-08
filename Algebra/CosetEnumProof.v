Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.Arith_base.
Require Import Coq.PArith.PArith.
Require Import Coq.micromega.Lia.
Require Import FormalMath.Algebra.FreeGroup.
Require Import FormalMath.Algebra.CosetEnum.
Require Import FormalMath.lib.List_ext.
Import ListNotations.

Local Open Scope positive_scope.

Section FIN_GEN_REP_PROOFS.

  Context `{FG: FiniteGenerators A}.

  Lemma a2p_helper_low: forall x l n, n <= a2p_helper x l n.
  Proof.
    intro x. induction l; intros; simpl. 1: intuition. if_tac.
    - intuition.
    - specialize (IHl (Pos.succ n)). transitivity (Pos.succ n). 2: assumption.
      rewrite <- Pos.add_1_r. apply Pos.lt_le_incl, Pos.lt_add_r.
  Qed.

  Lemma pos_add_succ: forall n m, n + Pos.succ m == Pos.succ n + m.
  Proof. intros. lia. Qed.

  Lemma pos_succ_add_sub: forall n m, Pos.succ n + m - 1 == n + m.
  Proof. intros. lia. Qed.

  Lemma a2p_helper_In:
    forall x l n, In x l <-> a2p_helper x l n < n + Pos.of_succ_nat (length l) - 1.
  Proof.
    intros x l. induction l; intros; simpl. 1: lia.
    rewrite pos_add_succ. split; intros; [if_tac | if_tac in H].
    - lia.
    - rewrite <- IHl. destruct H; auto. compute in c. exfalso; auto.
    - left; auto.
    - right. rewrite (IHl (Pos.succ n)); auto.
  Qed.

  Lemma nth_a2p_helper: forall x l n a,
      In x l -> nth (Pos.to_nat (a2p_helper x l n) - Pos.to_nat n) l a == x.
  Proof.
    intro x. induction l; intros. 1: simpl; inversion H.
    Opaque nth. simpl. if_tac. Transparent nth.
    - simpl. rewrite Nat.sub_diag. rewrite e. reflexivity.
    - compute in c. simpl in H. destruct H. 1: exfalso; auto.
      specialize (IHl (Pos.succ n) a0 H). rewrite <- IHl at 2.
      rewrite Pos2Nat.inj_succ. simpl.
      destruct ((Pos.to_nat (a2p_helper x l (Pos.succ n)) - Pos.to_nat n)%nat) eqn: ?.
      + rewrite Nat.sub_0_le in Heqn0. exfalso.
        pose proof (a2p_helper_low x l (Pos.succ n)). lia.
      + rewrite Nat.sub_succ_r, Heqn0, Nat.pred_succ. reflexivity.
  Qed.

  Lemma a2p_heler_nth: forall x l n a,
      (Pos.to_nat x <= length l)%nat -> NoDup l ->
      a2p_helper (nth (Init.Nat.pred (Pos.to_nat x)) l a) l n == x + n - 1.
  Proof.
    intros x l. revert x. induction l; intros.
    - simpl in *. lia.
    - Opaque nth. simpl. if_tac. Transparent nth.
      + simpl in e. destruct (pred (Pos.to_nat x)) eqn: ?.
        * clear -Heqn0. lia.
        * exfalso. rewrite NoDup_cons_iff in H0. destruct H0 as [? _]. apply H0.
          rewrite <- e. apply nth_In. simpl in H. lia.
      + simpl in *. destruct (pred (Pos.to_nat x)) eqn: ?.
        * exfalso. compute in c. apply c. auto.
        * rewrite NoDup_cons_iff in H0. destruct H0 as [_ ?].
          assert (1 < x) by lia.
          assert ((Pos.to_nat (x - 1) <= length l)%nat) by lia.
          specialize (IHl (x - 1) (n + 1) a0 H2 H0).
          assert (Nat.pred (Pos.to_nat (x - 1)) == n0) by lia. rewrite H3 in IHl.
          replace (Pos.succ n) with (n + 1) by lia. rewrite IHl. lia.
  Qed.

  Lemma a2p_helper_not_In:
    forall x l n, ~ In x l <-> a2p_helper x l n == n + Pos.of_succ_nat (length l) - 1.
  Proof.
    intros x l. induction l; intros; simpl. 1: rewrite Pos.add_sub; intuition.
    rewrite pos_add_succ. if_tac.
    - rewrite pos_succ_add_sub.
      pose proof (Pos.add_no_neutral n (Pos.of_succ_nat (length l))).
      rewrite Pos.add_comm in H. intuition.
    - rewrite <- IHl. intuition.
  Qed.

  Lemma a2p2a_the_same: forall x, positive_to_alphabet (alphabet_to_positive x) == x.
  Proof.
    intros. unfold positive_to_alphabet, alphabet_to_positive.
    assert (forall x, x <= fg_size <->
                        x < 1 + Pos.of_succ_nat (length fg_gens) - 1). {
      intro. rewrite fg_gens_size. lia. }
    assert (forall a, a2p_helper a fg_gens 1 <= fg_size). {
      intros. rewrite H, <- a2p_helper_In. apply fg_gens_all. } destruct x.
    - if_tac.
      + rewrite Pos.leb_le, H, <- a2p_helper_In in Heqb.
        rewrite <- Nat.sub_1_r, nth_a2p_helper; auto.
      + rewrite Pos.leb_nle in Heqb. exfalso. apply Heqb. apply H0.
    - pose proof (Pos.mul_xI_r 1 fg_size).
      rewrite !Pos.mul_1_l, <- Pos.add_diag, Pos.add_assoc in H1.
      assert (a2p_helper a fg_gens 1 < 1 + fg_size). {
          apply Pos.le_lt_trans with fg_size; auto. rewrite Pos.add_comm.
          apply Pos.lt_add_r. }
      assert (1 + fg_size + fg_size - a2p_helper a fg_gens 1 ==
              1 + fg_size - a2p_helper a fg_gens 1 + fg_size) by lia.
      if_tac.
      + rewrite Pos.leb_le in Heqb. specialize (H0 a). exfalso.
        rewrite H1 in Heqb. clear H1. rewrite H3 in Heqb. clear H3.
        apply (Pos.lt_irrefl fg_size). lia.
      + rewrite H1 in *. clear H1. rewrite Pos.leb_gt in Heqb. specialize (H0 a).
        assert ((Pos.to_nat (1 + fg_size - a2p_helper a fg_gens 1) <=
                 Pos.to_nat fg_size)%nat) by lia.
        rewrite H3, Pos.add_sub, rev_nth; rewrite fg_gens_size.
        * rewrite (Nat.lt_succ_pred O). 2: apply Pos2Nat.is_pos.
          rewrite Pos2Nat.inj_sub; auto.
          assert (forall (n m p : nat),
                     (p < m)%nat ->
                     ((m - p)%nat <= n)%nat -> (n - (m - p) == n + p - m)%nat). {
            clear. intros. lia. } rewrite H4. clear H4.
          -- rewrite Pos2Nat.inj_add.
             replace (Pos.to_nat fg_size + Pos.to_nat (a2p_helper a fg_gens 1) -
                                          (Pos.to_nat 1 + Pos.to_nat fg_size))%nat
               with (Pos.to_nat (a2p_helper a fg_gens 1) - Pos.to_nat 1)%nat by lia.
             f_equal. rewrite nth_a2p_helper; auto. apply fg_gens_all.
          -- rewrite <- Pos2Nat.inj_lt. assumption.
          -- rewrite <- Pos2Nat.inj_sub; auto.
        * assert (forall n m, (O < n)%nat -> (Nat.pred n < m <-> n <= m)%nat) by
              (intros; lia). rewrite H4; clear H4; auto. apply Pos2Nat.is_pos.
  Qed.

  Lemma p2a2p_the_same:
    forall x, x <= fg_size~0 -> alphabet_to_positive (positive_to_alphabet x) == x.
  Proof.
    intros. unfold positive_to_alphabet, alphabet_to_positive. if_tac.
    - rewrite Pos.leb_le in Heqb. rewrite a2p_heler_nth.
      + rewrite Pos.add_sub. reflexivity.
      + rewrite fg_gens_size, <- Pos2Nat.inj_le. assumption.
      + apply fg_gens_nodup.
    - rewrite Pos.leb_gt in Heqb. rewrite <- Pos.add_diag in H.
      pose proof (Pos.mul_xI_r 1 fg_size).
      rewrite !Pos.mul_1_l, <- Pos.add_diag, Pos.add_assoc in H0. rewrite H0. clear H0.
      assert (Pos.to_nat (x - fg_size) - 1 < length fg_gens)%nat. {
        rewrite fg_gens_size, Pos2Nat.inj_sub; auto.
        rewrite Pos2Nat.inj_le, Pos2Nat.inj_add in H.
        pose proof (Pos2Nat.is_pos x). pose proof (Pos2Nat.is_pos fg_size). lia.
      } rewrite <- Nat.sub_1_r, rev_nth; auto.
      remember (length fg_gens - S (Pos.to_nat (x - fg_size) - 1))%nat.
      replace n with (pred (n + 1)) by lia.
      rewrite <- (Nat2Pos.id (n + 1)) by lia.
      pose proof (Pos2Nat.is_pos fg_size). pose proof (Pos2Nat.is_pos x).
      assert (1 < x) by lia.
      assert (x - 1 < fg_size + fg_size) by lia.
      assert (length fg_gens - S (Pos.to_nat (x - fg_size) - 1) + 1 ==
              Pos.to_nat (fg_size + fg_size - (x - 1)))%nat. {
        replace (S (Pos.to_nat (x - fg_size) - 1)) with (Pos.to_nat (x - fg_size)) by
            (pose proof (Pos2Nat.is_pos (x - fg_size)); lia).
        rewrite fg_gens_size, Pos2Nat.inj_sub; auto.
        rewrite Pos2Nat.inj_lt in Heqb. rewrite Pos2Nat.inj_le, Pos2Nat.inj_add in H.
        replace (Pos.to_nat fg_size - (Pos.to_nat x - Pos.to_nat fg_size) + 1)%nat
          with (Pos.to_nat fg_size + Pos.to_nat fg_size - (Pos.to_nat x - 1))%nat
          by lia. rewrite <- Pos2Nat.inj_add, <- Pos2Nat.inj_1.
        rewrite <- !Pos2Nat.inj_sub; auto.
      } rewrite a2p_heler_nth; [ subst; rewrite H5.. | apply fg_gens_nodup].
      + rewrite Pos2Nat.id, Pos.add_sub. rewrite Pos.sub_sub_distr; auto; lia.
      + rewrite Pos2Nat.id, fg_gens_size. lia.
  Qed.

End FIN_GEN_REP_PROOFS.

Section TODD_COXETER_PROOFS.

  Context `{FG: FiniteGenerators A}.

  Definition coset_map_prop (ct: CosetEnum): Prop := forall i,
      (i <= num_coset ct -> exists j, PM.find i (coset_map ct) == Some j /\ j <= i)
      /\ (num_coset ct < i -> PM.find i (coset_map ct) == None).

  Definition valid_gen_rep (x: positive): Prop := x < fg_size~1.

  Definition valid_coset_rep (ct: CosetEnum) (a: positive): Prop := a <= num_coset ct.

  Definition coset_table_prop (ct: CosetEnum): Prop := forall a x b,
      valid_gen_rep x -> table_find a x (coset_table ct) == Some b ->
      table_find b (neg_rep x) (coset_table ct) == Some a /\
      valid_coset_rep ct a /\ valid_coset_rep ct b.

  Lemma double_neg_rep: forall x, valid_gen_rep x -> neg_rep (neg_rep x) == x.
  Proof. intros. unfold valid_gen_rep in H. unfold neg_rep. lia. Qed.

  Lemma gen_rep_neq_neg_rep: forall x, valid_gen_rep x -> x =/= neg_rep x.
  Proof. unfold valid_gen_rep, neg_rep. repeat intro. lia. Qed.

  Lemma valid_neg_rep: forall x, valid_gen_rep x -> valid_gen_rep (neg_rep x).
  Proof. unfold valid_gen_rep, neg_rep. intros. lia. Qed.

  Lemma init_coset_map_good: forall ub, coset_map_prop (init_coset_enum ub).
  Proof.
    Opaque PM.add PM.empty.
    intros. unfold init_coset_enum, coset_map_prop. simpl. intros.
    assert (i <= 1 \/ 1 < i) by lia.
    destruct H; split; intros; try lia.
    - assert (i == 1) by lia. subst i. exists 1. now rewrite PM.gss.
    - assert (i =/= 1) by lia. rewrite PM.gso by assumption. apply PM.gempty.
    Transparent PM.add PM.empty.
  Qed.

  Lemma init_coset_table_good: forall ub, coset_table_prop (init_coset_enum ub).
  Proof.
    intros. unfold init_coset_enum, coset_table_prop. simpl. intros.
    unfold table_find in H0. rewrite PM.gempty in H0. discriminate.
  Qed.

  Lemma define_new_coset_map_good: forall ct a x,
      coset_map_prop ct -> coset_map_prop (define_new_coset ct a x).
  Proof.
    unfold coset_map_prop. intros. unfold define_new_coset.
    destruct (should_stop ct); [apply H | simpl].
    split; intros; specialize (H i); destruct H.
    - assert (i <= num_coset ct \/ i == num_coset ct + 1) by lia. destruct H2.
      + rewrite PM.gso by (intro; subst; lia). apply H. assumption.
      + subst i. rewrite PM.gss. exists (num_coset ct + 1). intuition.
    - rewrite PM.gso by (intro; subst; lia). apply H1. lia.
  Qed.

  Lemma table_find_add_same: forall a x v t,
      table_find a x (table_add a x v t) == Some v.
  Proof. intros. unfold table_find, table_add. rewrite PM.gss. reflexivity. Qed.

  Lemma table_key_eq_iff: forall a b x y,
      valid_gen_rep x -> valid_gen_rep y ->
      table_key a x == table_key b y <-> a == b /\ x == y.
  Proof.
    intros. split; intros. 2: destruct H1; subst; reflexivity. unfold table_key in H1.
    unfold valid_gen_rep in H, H0.
    destruct (Pos.lt_total a b) as [? | [? | ?]]; nia.
  Qed.

  Lemma table_find_add_diff: forall a b x y v t,
      valid_gen_rep x -> valid_gen_rep y -> (a =/= b \/ x =/= y) ->
      table_find a x (table_add b y v t) == table_find a x t.
  Proof.
    intros. unfold table_find, table_add. rewrite PM.gso. 1: reflexivity.
    intro. rewrite table_key_eq_iff in H2 by assumption. intuition.
  Qed.

  Lemma pos_double_eq: forall (a b x y: positive),
      (a == b /\ x == y) \/ (a =/= b \/ x =/= y). Proof. intros. lia. Qed.

  Lemma define_new_coset_table_good: forall ct a x,
      coset_table_prop ct -> valid_coset_rep ct a -> valid_gen_rep x ->
      table_find a x (coset_table ct) == None ->
      coset_table_prop (define_new_coset ct a x).
  Proof.
    unfold define_new_coset. intros. destruct (should_stop ct). 1: assumption.
    unfold coset_table_prop, valid_coset_rep. simpl. intros c y b ? ?.
    assert (valid_gen_rep (neg_rep x)) by (apply valid_neg_rep; assumption).
    assert (valid_gen_rep (neg_rep y)) by (apply valid_neg_rep; assumption).
    destruct (pos_double_eq c (num_coset ct + 1) y (neg_rep x)).
    - destruct H7. subst. rewrite table_find_add_same in H4. inversion H4. subst b.
      rewrite double_neg_rep by assumption.
      rewrite table_find_add_diff;
        [rewrite table_find_add_same | | | right; apply gen_rep_neq_neg_rep];
        intuition. red in H0. lia.
    - rewrite table_find_add_diff in H4 by assumption.
      destruct (pos_double_eq c a y x).
      + destruct H8. subst. rewrite table_find_add_same in H4. inversion H4. subst.
        rewrite table_find_add_same. split; [|split]; [reflexivity | | intuition].
        clear -H0. red in H0. lia.
      + rewrite table_find_add_diff in H4 by assumption. apply H in H4.
        2: assumption. destruct H4 as [? [? ?]].
        rewrite table_find_add_diff;
          [|assumption..|left; red in H10; intro; lia].
        destruct (pos_double_eq b a (neg_rep y) x).
        * destruct H11. subst. exfalso. rewrite H2 in H4. inversion H4.
        * rewrite table_find_add_diff by assumption. split. 1: assumption.
          red in H9, H10. lia.
  Qed.

  Theorem todd_coxeter_is_right: forall
      (relators generators: list (Word A))
      relator_rep generator_rep bound coset_table,
      relator_rep == map (map alphabet_to_positive) relators ->
      generator_rep == map (map alphabet_to_positive) generators ->
      coset_table == coset_enumration_r relator_rep generator_rep bound ->
      num_coset coset_table < bound ->
      Cardinals (RightCoset (Quotient (Word A) (FP_Cond relators))
                            (FP_Sub_Cond relators generators))
                (Pos.to_nat (num_coset (compress coset_table))).
  Proof.
  Abort.

End TODD_COXETER_PROOFS.
