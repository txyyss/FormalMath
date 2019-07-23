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

