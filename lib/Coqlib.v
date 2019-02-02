Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint flatten {A: Type} (l: list (list A)): list A :=
  match l with
  | nil => nil
  | lh :: lt => lh ++ flatten lt
  end.

Fixpoint filter_option {A: Type} (l: list (option A)): list A :=
  match l with
  | nil => nil
  | Some h :: lt => h :: filter_option lt
  | None :: lt => filter_option lt
  end.

Fixpoint nat_seq (s: nat) (total: nat): list nat :=
  match total with
  | O => nil
  | S n => s :: nat_seq (S s) n
  end.

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

Lemma nat_seq_length: forall s n, length (nat_seq s n) = n.
Proof.
  intros. revert s. induction n; intros; simpl; [|rewrite IHn]; reflexivity.
Qed.

Lemma nat_seq_S: forall i num, nat_seq i (S num) = nat_seq i num ++ [num + i].
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
                                     nth n (nat_seq s num) a = s + n.
Proof.
  intros. revert s n H. induction num; intros. 1: exfalso; omega. simpl. destruct n.
  1: omega. specialize (IHnum (S s) n).
  replace (s + S n) with (S s + n) by omega.
  rewrite IHnum; [reflexivity | omega].
Qed.

Lemma nat_seq_app: forall s n m,
    nat_seq s (n + m) = nat_seq s n ++ nat_seq (s + n) m.
Proof.
  intros. revert s; induction n; simpl; intros.
  - rewrite Nat.add_0_r. reflexivity.
  - f_equal. rewrite IHn. replace (S s + n) with (s + S n) by omega.
    reflexivity.
Qed.
