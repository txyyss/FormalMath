Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Arith.PeanoNat.

Inductive dep_list (A: Type): nat -> Type :=
| dep_nil: dep_list A O
| dep_cons: forall n: nat, A -> dep_list A n -> dep_list A (S n).

Arguments dep_nil [_].
Arguments dep_cons [_ _] _ _.

Module DepListNotations.
  Notation "{| |}" := dep_nil (format "{| |}"): dep_list_scope.
  Notation "{| x |}" := (dep_cons x dep_nil): dep_list_scope.
  Notation "{| x ; y ; .. ; z |}" :=
    (dep_cons x (dep_cons y .. (dep_cons z dep_nil) ..)): dep_list_scope.
End DepListNotations.

Fixpoint dep_fold_left {A B: Type} {n: nat}
         (f: A -> B -> A) (dl: dep_list B n) (a: A): A :=
  match dl with
  | dep_nil => a
  | dep_cons b dl' => dep_fold_left f dl' (f a b)
  end.

Eval compute in (dep_fold_left Nat.add (dep_cons 2 (dep_cons 1 dep_nil)) O).

Fixpoint dep_fold_right {A B: Type} {n: nat}
         (f: B -> A -> A) (dl: dep_list B n) (a: A): A :=
  match dl with
  | dep_nil => a
  | dep_cons b dl' => f b (dep_fold_right f dl' a)
  end.

Eval compute in (dep_fold_right Nat.sub (dep_cons 2 (dep_cons 1 dep_nil)) O).

Definition dep_list_to_list {A: Type} {n: nat} (dl: dep_list A n): list A :=
  dep_fold_right cons dl nil.

Eval compute in (dep_list_to_list (dep_cons 2 (dep_cons 1 dep_nil))).

Fixpoint dep_app {A: Type} {n m: nat} (dl1: dep_list A n) (dl2: dep_list A m):
  dep_list A (n + m) :=
  match dl1 with
  | dep_nil => dl2
  | dep_cons b dl' => dep_cons b (dep_app dl' dl2)
  end.

Fixpoint dep_zip {A B: Type} {n: nat} (dl: dep_list A n):
  dep_list B n -> dep_list (A * B) n :=
  match dl in (dep_list _ n) return (dep_list B n -> dep_list (A * B) n) with
  | dep_nil => fun _ => dep_nil
  | @dep_cons _ m a dl' =>
    fun dl2 => match dl2 in (dep_list _ k) return
                     (k = S m -> dep_list (A * B) (S m)) with
               | dep_nil => fun h => False_rect _ (O_S _ h)
               | dep_cons b dl2' =>
                 fun h =>
                   dep_cons (a, b) (dep_zip dl' (eq_rect _ _ dl2' _ (eq_add_S _ _ h)))
               end (eq_refl (S m))
  end.

Eval compute in dep_zip (dep_cons 1 (dep_cons 2 (dep_cons 3 dep_nil)))
                        (dep_cons 4 (dep_cons 5 (dep_cons 6 dep_nil))).

Fixpoint dep_map {A B: Type} (f: A -> B) {n: nat} (dl: dep_list A n): dep_list B n :=
  match dl with
  | dep_nil => dep_nil
  | dep_cons a dl' => dep_cons (f a) (dep_map f dl')
  end.

Lemma dep_map_cons: forall {A B: Type} (f: A -> B) {n: nat} (a: A) (dl: dep_list A n),
    dep_map f (dep_cons a dl) = dep_cons (f a) (dep_map f dl).
Proof. intros. now simpl. Qed.

Hint Rewrite @dep_map_cons: dep_list.

Definition dep_list_binop {A B C: Type} (f: A -> B -> C) {n: nat}
           (dl1: dep_list A n) (dl2: dep_list B n): dep_list C n :=
  dep_map (fun p: (A * B) => f (fst p) (snd p)) (dep_zip dl1 dl2).

Lemma dep_list_O_unique: forall {A} (v: dep_list A O), v = dep_nil.
Proof.
  intros. change (v = eq_rect _ _ (@dep_nil A) _ eq_refl). generalize (eq_refl O).
  case v; intros; try easy. apply K_dec_set with (p := e); [exact Nat.eq_dec | easy].
Qed.

Lemma dep_list_S_decompose: forall {A} {n: nat} (v: dep_list A (S n)),
    {a: A & {v': dep_list A n | v = dep_cons a v'}}.
Proof.
  intros. cut {a: A &  {t: dep_list A n |
                         eq_dep nat (dep_list A) (S n) v (S n) (dep_cons a t)}}.
  - intros. destruct X as [a [t ?]]. exists a, t.
    apply eq_dep_eq_dec; [exact Nat.eq_dec | easy].
  - dependent inversion_clear v with
      (fun (m: nat) (vl: dep_list A m) =>
         {a: A &  {v': dep_list A n |
                    eq_dep nat (dep_list A) m vl (S n) (dep_cons a v')}}).
    exists a, d. constructor.
Qed.

Ltac dep_list_decomp :=
  repeat match goal with
         | v: dep_list ?A O |- _ => pose proof (dep_list_O_unique v); subst v
         | v: dep_list ?A (S ?n) |- _ =>
           destruct (dep_list_S_decompose v) as [?v [?v ?]]; subst v
  end.

Lemma dep_list_ind_1: forall {A} (P: forall n, dep_list A n -> Prop),
    P O dep_nil ->
    (forall (n: nat) (v: dep_list A n),
        P n v -> forall a: A, P (S n) (dep_cons a v)) ->
    forall (n: nat) (v: dep_list A n), P n v.
Proof.
  intros until n. induction n; intros; dep_list_decomp; [easy | apply H0, IHn].
Qed.

Lemma dep_list_ind_2: forall
    {A B} (P: forall n, dep_list A n -> dep_list B n -> Prop),
    P O dep_nil dep_nil ->
    (forall (n: nat) (v1: dep_list A n) (v2: dep_list B n),
        P n v1 v2 -> forall (a: A) (b: B), P (S n) (dep_cons a v1) (dep_cons b v2)) ->
    forall (n: nat) (v1: dep_list A n) (v2: dep_list B n), P n v1 v2.
Proof.
  intros until n. induction n; intros; dep_list_decomp; [easy | apply H0, IHn].
Qed.

Lemma dep_list_ind_3: forall
    {A B C} (P: forall n, dep_list A n -> dep_list B n -> dep_list C n -> Prop),
    P O dep_nil dep_nil dep_nil ->
    (forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n),
        P n v1 v2 v3 -> forall (a: A) (b: B) (c: C),
          P (S n) (dep_cons a v1) (dep_cons b v2) (dep_cons c v3)) ->
    forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n),
      P n v1 v2 v3.
Proof.
  intros until n. induction n; intros; dep_list_decomp; [easy | apply H0, IHn].
Qed.

Lemma dep_cons_eq_inv: forall {A n} (a1 a2: A) (l1 l2: dep_list A n),
    dep_cons a1 l1 = dep_cons a2 l2 -> a1 = a2 /\ l1 = l2.
Proof.
  intros. inversion H. split; auto. apply eq_sigT_eq_dep in H2.
  apply eq_dep_eq_dec; auto. apply Nat.eq_dec.
Qed.

Lemma dep_map_nest:
  forall {A B C: Type} (f: A -> B) (g: B -> C) {n} (dl: dep_list A n),
    dep_map g (dep_map f dl) = dep_map (fun x => g (f x)) dl.
Proof.
  intros. revert n dl. apply dep_list_ind_1; intros; simpl; [| rewrite H]; easy.
Qed.

Lemma dep_list_binop_nil: forall {A B C} (f: A -> B -> C),
    dep_list_binop f dep_nil dep_nil = dep_nil.
Proof. intros. unfold dep_list_binop. simpl. easy. Qed.

Hint Rewrite @dep_list_binop_nil: dep_list.

Lemma dep_list_binop_cons: forall
    {A B C} {n: nat} (a: A) (b: B)
    (v1: dep_list A n) (v2: dep_list B n) (f: A -> B -> C),
    dep_list_binop f (dep_cons a v1) (dep_cons b v2) =
    dep_cons (f a b) (dep_list_binop f v1 v2).
Proof. intros. unfold dep_list_binop. simpl. easy. Qed.

Hint Rewrite @dep_list_binop_cons: dep_list.

Lemma dep_list_binop_comm: forall
    {A B} {n: nat} (v1 v2: dep_list A n) (f: A -> A -> B),
    (forall x y, f x y = f y x) -> dep_list_binop f v1 v2 = dep_list_binop f v2 v1.
Proof.
  intros. revert n v1 v2. apply dep_list_ind_2. 1: easy. intros.
  autorewrite with dep_list. f_equal; easy.
Qed.

Lemma dep_list_binop_assoc: forall
    {A} {n: nat} (v1 v2 v3: dep_list A n) (f: A -> A -> A),
    (forall x y z, f (f x y) z = f x (f y z)) ->
    dep_list_binop f (dep_list_binop f v1 v2) v3 =
    dep_list_binop f v1 (dep_list_binop f v2 v3).
Proof.
  intros. revert n v1 v2 v3.
  apply dep_list_ind_3; intros; autorewrite with dep_list; [easy | now f_equal].
Qed.

Fixpoint dep_repeat {A} (e: A) (n: nat): dep_list A n :=
  match n with
  | O => dep_nil
  | S n' => dep_cons e (dep_repeat e n')
  end.

Lemma dep_map_repeat: forall {A B} (f: A -> B) (a: A) n,
    dep_map f (dep_repeat a n) = dep_repeat (f a) n.
Proof. intros. induction n; simpl; [easy | now rewrite IHn]. Qed.

Hint Rewrite @dep_map_repeat: dep_list.

Fixpoint dep_list_transpose {A: Type} {m n: nat}
         (mat: dep_list (dep_list A n) m): dep_list (dep_list A m) n :=
  match mat with
  | dep_nil => dep_repeat dep_nil n
  | @dep_cons _ m' row rest_rows =>
    dep_list_binop (@dep_cons _ m') row (dep_list_transpose rest_rows)
  end.

Compute (dep_list_transpose
           (dep_cons (dep_cons 1 (dep_cons 2 dep_nil))
                     (dep_cons (dep_cons 3 (dep_cons 4 dep_nil))
                               (dep_cons (dep_cons 5 (dep_cons 6 dep_nil)) dep_nil)))).

Lemma dep_list_transpose_involutive: forall {A m n} (mat: dep_list (dep_list A n) m),
    dep_list_transpose (dep_list_transpose mat) = mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1. 1: apply dep_list_O_unique. intros.
  rename n0 into m. simpl. rewrite <- H at 2. remember (dep_list_transpose v).
  clear v Heqd H. revert a.
  apply dep_list_ind_1 with (v := d); intros; dep_list_decomp. 1: now simpl.
  autorewrite with dep_list. simpl. rewrite H. now autorewrite with dep_list.
Qed.

Definition dep_hd {A: Type} {n: nat} (l: dep_list A (S n)): A :=
  match l in (dep_list _ m) return (O < m -> A) with
  | dep_nil => fun p => False_rect _ (Nat.nle_succ_0 _ p)
  | dep_cons h _ => fun _ => h
  end (Nat.lt_0_succ n).

Lemma dep_hd_transpose: forall {A} {m n} (mat: dep_list (dep_list A (S n)) m),
    dep_hd (dep_list_transpose mat) = dep_map dep_hd mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros. 1: easy. simpl. rewrite <- H.
  generalize (dep_list_transpose v). clear. intros. dep_list_decomp. now simpl.
Qed.

Fixpoint dep_colist {A: Type} {n: nat} (l: dep_list A (S n)):
  dep_list (dep_list A n) (S n) :=
  match l in (dep_list _ m) return (m = S n -> dep_list (dep_list A n) (S n)) with
  | dep_nil => fun p => False_rect _ (O_S _ p)
  | @dep_cons _ n0 h l' =>
    fun p => match l' in (dep_list _ k) return
                   (k = n0 -> dep_list (dep_list A n) (S n)) with
             | dep_nil =>
               fun p2 =>
                 eq_rect_r _ (fun H4 => eq_rect 0 (fun n1 => dep_list _ (S n1))
                                                (dep_cons dep_nil dep_nil) n H4)
                           (eq_add_S _ _ p) p2
             | @dep_cons _ i _ _ =>
               fun p2 =>
                 eq_rect
                   n0 (fun n1 => dep_list _ (S n1))
                   (eq_rect (S i) (fun n1 => dep_list A n1 -> _)
                            (fun l0 => dep_cons l0 (dep_map (dep_cons h)
                                                            (dep_colist l0))) n0 p2 l')
                   n (eq_add_S _ _ p)
             end (eq_refl n0)
  end (eq_refl (S n)).

Compute (dep_colist (dep_cons 1 (dep_cons 2 (dep_cons 3 (dep_cons 4 dep_nil))))).

Lemma dep_colist_cons: forall {A} {n} (a: A) (l: dep_list A (S n)),
    dep_colist (dep_cons a l) = dep_cons l (dep_map (dep_cons a) (dep_colist l)).
Proof. intros. dep_list_decomp. easy. Qed.

Lemma dep_colist_nil: forall {A} (a: A),
    dep_colist (dep_cons a dep_nil) = dep_cons dep_nil dep_nil.
Proof. intros. easy. Qed.
