Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
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

Lemma fold_right_perm: forall {A} (f: A -> A -> A) a l1 l2,
    (forall x y, f x y = f y x) -> (forall x y z, f (f x y) z = f x (f y z)) ->
    Permutation l1 l2 -> fold_right f a l1 = fold_right f a l2.
Proof.
  intros. induction H1; simpl; auto.
  - now rewrite IHPermutation.
  - now rewrite <- !H0, (H x y).
  - now rewrite IHPermutation1.
Qed.

Lemma fold_right_distr: forall {A B: Type} (f: B -> A -> A) (g: A -> A -> A) b a l,
    (forall z x y, f z (g x y) = g (f z x) (f z y)) ->
    f b (fold_right g a l) = fold_right g (f b a) (map (f b) l).
Proof. intros. induction l; simpl; [| rewrite H, IHl]; easy. Qed.

Lemma map_binary_func: forall {A B C: Type} (f: A -> B -> C) a l,
    map (f a) l = map (fun x => f (fst x) (snd x)) (combine (repeat a (length l)) l).
Proof. intros. induction l; simpl; [| rewrite IHl]; easy. Qed.

Lemma map_fst_combine: forall {A B: Type} (l1: list A) (l2: list B),
    length l1 <= length l2 -> map fst (combine l1 l2) = l1.
Proof.
  intros A B. induction l1, l2; simpl; intros; auto.
  - inversion H.
  - apply le_S_n in H. now rewrite IHl1.
Qed.

Lemma map_binary_snd_combine:
  forall {A B C D: Type} (l1: list A) (l2: list D) (f: A -> B -> C) (g: D -> B),
    map (fun x => f (fst x) (g (snd x))) (combine l1 l2) =
    map (fun x => f (fst x) (snd x)) (combine l1 (map g l2)).
Proof.
  intros. revert l2. induction l1; intros; simpl; auto.
  destruct l2; simpl; auto. now rewrite IHl1.
Qed.
