Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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

Lemma seq_S: forall i num, seq i (S num) = seq i num ++ [num + i].
Proof.
  intros. revert i. induction num; intros. 1: simpl; reflexivity. remember (S num).
  simpl. rewrite (IHnum (S i)). subst. simpl. repeat f_equal. now rewrite plus_n_Sm.
Qed.

Lemma seq_app: forall s n m, seq s (n + m) = seq s n ++ seq (s + n) m.
Proof.
  intros. revert s; induction n; simpl; intros.
  - now rewrite <- plus_n_O.
  - now rewrite IHn, plus_Snm_nSm.
Qed.
