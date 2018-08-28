Require Import Coq.Classes.EquivDec.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import FormalMath.FreeGroup.
Require Import FormalMath.CosetEnum.
Import ListNotations.

Tactic Notation "if_tac" :=
  match goal with |- context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ => destruct a
    | bool => destruct a eqn: ?
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
    end end.

Tactic Notation "if_tac" "in" hyp(H0)
  := match type of H0 with context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ => destruct a
    | bool => destruct a eqn: ?
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
    end end.

Lemma nat_seq_length: forall s n, length (nat_seq s n) == n.
Proof.
  intros. revert s. induction n; intros; simpl; [|rewrite IHn]; reflexivity.
Qed.

Lemma nat_seq_S: forall i num, nat_seq i (S num) == nat_seq i num ++ [num + i].
Proof.
  intros. revert i. induction num; intros. 1: simpl; reflexivity. remember (S num).
  simpl. rewrite (IHnum (S i)). subst. simpl. repeat f_equal. omega.
Qed.

Lemma nat_seq_In_iff: forall s n i, In i (nat_seq s n) <-> s <= i < s + n.
Proof. intros. revert s. induction n; intros; simpl; [|rewrite IHn]; omega. Qed.

Lemma nat_seq_NoDup: forall s n, NoDup (nat_seq s n).
Proof.
  intros. revert s. induction n; intros; simpl; constructor. 2: apply IHn.
  intro. rewrite nat_seq_In_iff in H. omega.
Qed.

Lemma nat_seq_nth: forall s num n a, n < num ->
                                     nth n (nat_seq s num) a == s + n.
Proof.
  intros. revert s n H. induction num; intros. 1: exfalso; omega. simpl. destruct n.
  1: omega. specialize (IHnum (S s) n).
  replace (s + S n) with (S s + n) by omega.
  rewrite IHnum; [reflexivity | omega].
Qed.

Lemma nat_seq_app: forall s n m,
    nat_seq s (n + m) == nat_seq s n ++ nat_seq (s + n) m.
Proof.
  intros. revert s; induction n; simpl; intros.
  - rewrite Nat.add_0_r. reflexivity.
  - f_equal. rewrite IHn. replace (S s + n) with (s + S n) by omega.
    reflexivity.
Qed.

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
  Proof. intros. zify. omega. Qed.

  Lemma pos_succ_add_sub: forall n m, Pos.succ n + m - 1 == n + m.
  Proof. intros. zify. omega. Qed.

  Lemma a2p_helper_In:
    forall x l n, In x l <-> a2p_helper x l n < n + Pos.of_succ_nat (length l) - 1.
  Proof.
    intros x l. induction l; intros; simpl. 1: zify; omega.
    rewrite pos_add_succ. split; intros; [if_tac | if_tac in H].
    - zify. omega.
    - rewrite <- IHl. destruct H; auto. compute in c. exfalso; auto.
    - left; auto.
    - right. rewrite (IHl (Pos.succ n)); auto.
  Qed.

  Lemma nth_a2p_helper: forall x l n a,
      In x l -> nth (Pos.to_nat (a2p_helper x l n) - Pos.to_nat n) l a == x.
  Proof.
    intro x. induction l; intros. 1: simpl; inversion H.
    Opaque nth. simpl. if_tac. Transparent nth.
    - simpl. rewrite PeanoNat.Nat.sub_diag. rewrite e. reflexivity.
    - compute in c. simpl in H. destruct H. 1: exfalso; auto.
      specialize (IHl (Pos.succ n) a0 H). rewrite <- IHl at 2.
      rewrite Pos2Nat.inj_succ. simpl.
      destruct ((Pos.to_nat (a2p_helper x l (Pos.succ n)) - Pos.to_nat n)%nat) eqn: ?.
      + rewrite PeanoNat.Nat.sub_0_le in Heqn0. exfalso.
        pose proof (a2p_helper_low x l (Pos.succ n)). zify. omega.
      + rewrite PeanoNat.Nat.sub_succ_r, Heqn0, PeanoNat.Nat.pred_succ. reflexivity.
  Qed.

  Lemma a2p_heler_nth: forall x l n a,
      (Pos.to_nat x <= length l)%nat -> NoDup l ->
      a2p_helper (nth (Init.Nat.pred (Pos.to_nat x)) l a) l n == x + n - 1.
  Proof.
    intros x l. revert x. induction l; intros.
    - simpl in *. exfalso. zify. omega.
    - Opaque nth. simpl. if_tac. Transparent nth.
      + simpl in e. destruct (pred (Pos.to_nat x)) eqn: ?.
        * clear -Heqn0. rewrite Nat.eq_pred_0 in Heqn0. zify. omega.
        * exfalso. rewrite NoDup_cons_iff in H0. destruct H0 as [? _]. apply H0.
          rewrite <- e. apply nth_In. simpl in H.
          pose proof (Pos2Nat.is_pos x). omega.
      + simpl in *. destruct (pred (Pos.to_nat x)) eqn: ?.
        * exfalso. compute in c. apply c. auto.
        * rewrite NoDup_cons_iff in H0. destruct H0 as [_ ?].
          assert (1 < x) by (zify; omega).
          assert ((Pos.to_nat (x - 1) <= length l)%nat) by (zify; omega).
          specialize (IHl (x - 1) (n + 1) a0 H2 H0).
          rewrite <- Nat.sub_1_r in *. rewrite Pos2Nat.inj_sub in *; auto.
          rewrite Pos2Nat.inj_1 in *. rewrite <- Pos.add_1_r.
          assert (n0 == (Pos.to_nat x - 1 - 1)%nat) by omega. rewrite H3.
          rewrite IHl. zify; omega.
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
      intro. rewrite fg_gens_size. zify; omega. }
    assert (forall a, a2p_helper a fg_gens 1 <= fg_size). {
      intros. rewrite H, <- a2p_helper_In. apply fg_gens_all. } destruct x.
    - if_tac.
      + rewrite Pos.leb_le, H, <- a2p_helper_In in Heqb.
        rewrite Minus.pred_of_minus, nth_a2p_helper; auto.
      + rewrite Pos.leb_nle in Heqb. exfalso. apply Heqb. apply H0.
    - pose proof (Pos.mul_xI_r 1 fg_size).
      rewrite !Pos.mul_1_l, <- Pos.add_diag, Pos.add_assoc in H1.
      assert (a2p_helper a fg_gens 1 < 1 + fg_size). {
          apply Pos.le_lt_trans with fg_size; auto. rewrite Pos.add_comm.
          apply Pos.lt_add_r. }
      assert (1 + fg_size + fg_size - a2p_helper a fg_gens 1 ==
              1 + fg_size - a2p_helper a fg_gens 1 + fg_size) by (zify; omega).
      if_tac.
      + rewrite Pos.leb_le in Heqb. specialize (H0 a). exfalso.
        rewrite H1 in Heqb. clear H1. rewrite H3 in Heqb. clear H3.
        apply (Pos.lt_irrefl fg_size). zify; omega.
      + rewrite H1 in *. clear H1. rewrite Pos.leb_gt in Heqb. specialize (H0 a).
        assert ((Pos.to_nat (1 + fg_size - a2p_helper a fg_gens 1) <=
                 Pos.to_nat fg_size)%nat) by (zify; omega).
        rewrite H3, Pos.add_sub, rev_nth; rewrite fg_gens_size.
        * rewrite <- (Lt.S_pred _ O). 2: apply Pos2Nat.is_pos.
          rewrite Pos2Nat.inj_sub; auto.
          assert (forall (n m p : nat),
                     (p < m)%nat ->
                     ((m - p)%nat <= n)%nat -> (n - (m - p) == n + p - m)%nat). {
            clear. intros. omega. } rewrite H4. clear H4.
          -- rewrite Pos2Nat.inj_add.
             replace (Pos.to_nat fg_size + Pos.to_nat (a2p_helper a fg_gens 1) -
                                          (Pos.to_nat 1 + Pos.to_nat fg_size))%nat
               with (Pos.to_nat (a2p_helper a fg_gens 1) - Pos.to_nat 1)%nat by omega.
             f_equal. rewrite nth_a2p_helper; auto. apply fg_gens_all.
          -- rewrite <- Pos2Nat.inj_lt. assumption.
          -- rewrite <- Pos2Nat.inj_sub; auto.
        * assert (forall n m, (O < n)%nat -> (Nat.pred n < m <-> n <= m)%nat) by
              (intros; omega). rewrite H4; clear H4; auto. apply Pos2Nat.is_pos.
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
        pose proof (Pos2Nat.is_pos x). pose proof (Pos2Nat.is_pos fg_size). omega.
      } rewrite <- Nat.sub_1_r, rev_nth; auto.
      remember (length fg_gens - S (Pos.to_nat (x - fg_size) - 1))%nat.
      replace n with (pred (n + 1)) by omega.
      rewrite <- (Nat2Pos.id (n + 1)) by omega.
      pose proof (Pos2Nat.is_pos fg_size). pose proof (Pos2Nat.is_pos x).
      assert (1 < x) by (zify; omega).
      assert (x - 1 < fg_size + fg_size) by (zify; omega).
      assert (length fg_gens - S (Pos.to_nat (x - fg_size) - 1) + 1 ==
              Pos.to_nat (fg_size + fg_size - (x - 1)))%nat. {
        replace (S (Pos.to_nat (x - fg_size) - 1)) with (Pos.to_nat (x - fg_size)) by
            (pose proof (Pos2Nat.is_pos (x - fg_size)); omega).
        rewrite fg_gens_size, Pos2Nat.inj_sub; auto.
        rewrite Pos2Nat.inj_lt in Heqb. rewrite Pos2Nat.inj_le, Pos2Nat.inj_add in H.
        replace (Pos.to_nat fg_size - (Pos.to_nat x - Pos.to_nat fg_size) + 1)%nat
          with (Pos.to_nat fg_size + Pos.to_nat fg_size - (Pos.to_nat x - 1))%nat
          by omega. rewrite <- Pos2Nat.inj_add, <- Pos2Nat.inj_1.
        rewrite <- !Pos2Nat.inj_sub; auto.
      } rewrite a2p_heler_nth; [ subst; rewrite H5.. | apply fg_gens_nodup].
      + rewrite Pos2Nat.id, Pos.add_sub. rewrite Pos.sub_sub_distr; auto; zify; omega.
      + rewrite Pos2Nat.id, fg_gens_size. zify; omega.
  Qed.

End FIN_GEN_REP_PROOFS.

Section TODD_COXETER_PROOFS.

  Context `{FG: FiniteGenerators A}.

  Definition coset_map_prop (cm: CosetMap): Prop :=
    forall i j, PM.find i cm == Some j -> j <= i.

  Definition coset_table_prop (tbl: TableMap): Prop :=
    forall a x b, table_find a x tbl == Some b <->
                  table_find b (negRep x) tbl == Some a.

  Definition valid_gen_rep (x: positive): Prop := x < fg_size~1.

  Lemma double_neg_rep: forall x, valid_gen_rep x -> negRep (negRep x) == x.
  Proof. intros. unfold valid_gen_rep in H. unfold negRep. zify. omega. Qed.

End TODD_COXETER_PROOFS.
