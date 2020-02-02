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

Lemma fold_right_ext: forall {A B: Type} (g f: B -> A -> A) a l,
    (forall x y, f x y = g x y) -> fold_right f a l = fold_right g a l.
Proof. intros. induction l; simpl; [| rewrite H, IHl]; easy. Qed.

Lemma fold_right_split: forall {A B: Type} (f: A -> A -> A) (g h: B -> A) a l,
    f a a = a -> (forall x y, f x y = f y x) ->
    (forall x y z, f (f x y) z = f x (f y z)) ->
    fold_right (fun x => f (f (g x) (h x))) a l =
    f (fold_right (fun x => f (g x)) a l) (fold_right (fun x => f (h x)) a l).
Proof.
  intros. induction l; simpl; auto. rewrite IHl, !H1. f_equal.
  now rewrite <- (H1 (h a0)), (H0 (h a0)), H1.
Qed.

Lemma fold_right_map: forall {A B C: Type} (f: B -> A -> A) (g: C -> B) a l,
    fold_right (fun x => f (g x)) a l = fold_right f a (map g l).
Proof. intros. induction l; simpl; [|rewrite IHl]; easy. Qed.
