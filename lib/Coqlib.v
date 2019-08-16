Require Import Coq.Arith.Arith.

Lemma lt_plus_S_l: forall (n m: nat), n < n + S m.
Proof. intros. rewrite <- Nat.le_succ_l, <- Nat.add_succ_comm. apply le_plus_l. Qed.

Lemma lt_exists_S_diff: forall (n m: nat), n < m -> exists k, m = n + S k.
Proof.
  intros. apply lt_le_S, le_plus_minus in H; rewrite plus_Snm_nSm in H.
  now exists (m - S n).
Qed.

Ltac decomp_lt_subst' H :=
  match type of H with
  | ?i < ?n =>
    apply lt_exists_S_diff in H; let k := fresh "k" in let ph := fresh "H" in
                                                       destruct H as [k ph]; subst n
  end.

Ltac decomp_lt_subst := match goal with | [H: ?i < ?n |- _ ] => decomp_lt_subst' H end.

Lemma S_plus_neq: forall i m, m + S i <> m.
Proof.
  intros. apply Nat.neq_sym. rewrite <- plus_n_Sm, Nat.add_comm.
  apply Nat.succ_add_discr.
Qed.

Lemma neq_nSl_nSm: forall l n m, l <> m -> n + S l <> n + S m.
Proof.
  intros.  intro.
  rewrite Nat.add_cancel_l in H0. inversion H0. subst. now apply H.
Qed.

Lemma subsub_eq: forall m n, n <= m -> m - (m - n) = n.
Proof.
  induction m, n; intros.
  - now simpl.
  - now apply Nat.nle_succ_0 in H.
  - simpl. apply Nat.sub_diag.
  - rewrite <- Nat.succ_le_mono in H. rewrite Nat.sub_succ, Nat.sub_succ_l.
    + now rewrite IHm.
    + apply Nat.le_sub_l.
Qed.

Lemma lt_sub_1_sub_lt: forall m n, m < n -> n - 1 - m < n.
Proof.
  intros. rewrite <- Nat.sub_add_distr. apply Nat.sub_lt.
  - now rewrite Nat.add_1_l.
  - apply lt_plus_trans, Nat.lt_0_1.
Qed.

Lemma lt_sub1_sub1_sub_eq:  forall i n, i < n -> n - 1 - (n - 1 - i) = i.
Proof.
  intros. rewrite subsub_eq; auto. apply Nat.le_add_le_sub_l. now rewrite Nat.add_1_l.
Qed.

Lemma sub_lt_mono_l: forall n m p : nat, n < m <= p -> p - m < p - n.
Proof.
  induction n, m, p; intros; destruct H.
  - inversion H.
  - inversion H.
  - inversion H0.
  - simpl. rewrite <- Nat.sub_succ. apply Nat.sub_lt; auto.
  - inversion H.
  - inversion H.
  - inversion H0.
  - rewrite !Nat.sub_succ in *. apply lt_S_n in H. apply le_S_n in H0.
    now apply IHn.
Qed.

Lemma ltlt_sub1_lt: forall i j m, i < j < m -> m - 1 - j < m - 1 - i < m.
Proof.
  intros. destruct H. assert (i < m) by (eapply lt_trans; eauto).
  split. 2: now apply lt_sub_1_sub_lt. apply sub_lt_mono_l. split; auto.
  apply Nat.le_add_le_sub_r. now rewrite Nat.add_1_r.
Qed.
