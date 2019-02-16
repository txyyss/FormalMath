Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Arith.PeanoNat.

Inductive dep_list (A: Type): nat -> Type :=
| dep_nil: dep_list A O
| dep_cons: forall n: nat, A -> dep_list A n -> dep_list A (S n).

Arguments dep_nil [_].
Arguments dep_cons [_ _] _ _.

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

Eval compute in dep_map (fun x => x * 2)
                        (dep_cons 4 (dep_cons 5 (dep_cons 6 dep_nil))).

Definition dep_list_binop {A B C: Type} (f: A -> B -> C) {n: nat}
           (dl1: dep_list A n) (dl2: dep_list B n): dep_list C n :=
  dep_map (fun p: (A * B) => f (fst p) (snd p)) (dep_zip dl1 dl2).

Lemma dep_list_O_unique: forall {A} (v: dep_list A O), v = dep_nil.
Proof.
  intros. change (v = eq_rect _ _ (@dep_nil A) _ eq_refl). generalize (eq_refl O).
  case v; intros; try easy. apply K_dec_set with (p := e); [exact Nat.eq_dec | easy].
Qed.

Lemma dep_list_S_decompose: forall {A} n (v: dep_list A (S n)),
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

Lemma dep_list_ind_1: forall {A} (P: forall n, dep_list A n -> Prop),
    P O dep_nil ->
    (forall (n: nat) (v: dep_list A n),
        P n v -> forall a: A, P (S n) (dep_cons a v)) ->
    forall (n: nat) (v: dep_list A n), P n v.
Proof.
  intros until n. induction n; intros.
  - rewrite dep_list_O_unique. easy.
  - destruct (dep_list_S_decompose n v) as [a [v' ?]]. subst v. apply H0, IHn.
Qed.

Lemma dep_list_ind_2: forall
    {A B} (P: forall n, dep_list A n -> dep_list B n -> Prop),
    P O dep_nil dep_nil ->
    (forall (n: nat) (v1: dep_list A n) (v2: dep_list B n),
        P n v1 v2 -> forall (a: A) (b: B), P (S n) (dep_cons a v1) (dep_cons b v2)) ->
    forall {n: nat} (v1: dep_list A n) (v2: dep_list B n), P n v1 v2.
Proof.
  intros until n. induction n; intros.
  - rewrite (dep_list_O_unique v1), (dep_list_O_unique v2). easy.
  - destruct (dep_list_S_decompose n v1) as [a [va ?]].
    destruct (dep_list_S_decompose n v2) as [b [vb ?]]. subst v1 v2. apply H0, IHn.
Qed.

Lemma dep_list_ind_3: forall
    {A B C} (P: forall n, dep_list A n -> dep_list B n -> dep_list C n -> Prop),
    P O dep_nil dep_nil dep_nil ->
    (forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n),
        P n v1 v2 v3 -> forall (a: A) (b: B) (c: C),
          P (S n) (dep_cons a v1) (dep_cons b v2) (dep_cons c v3)) ->
    forall {n: nat} (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n),
      P n v1 v2 v3.
Proof.
  intros until n. induction n; intros.
  - rewrite (dep_list_O_unique v1), (dep_list_O_unique v2), (dep_list_O_unique v3).
    easy.
  - destruct (dep_list_S_decompose n v1) as [a [va ?]].
    destruct (dep_list_S_decompose n v2) as [b [vb ?]].
    destruct (dep_list_S_decompose n v3) as [c [vc ?]]. subst v1 v2 v3. apply H0, IHn.
Qed.

Lemma dep_list_binop_cons: forall
    {A B C} {n: nat} (a: A) (b: B)
    (v1: dep_list A n) (v2: dep_list B n) (f: A -> B -> C),
    dep_list_binop f (dep_cons a v1) (dep_cons b v2) =
    dep_cons (f a b) (dep_list_binop f v1 v2).
Proof. intros. unfold dep_list_binop. simpl. easy. Qed.

Lemma dep_list_binop_comm: forall
    {A B} {n: nat} (v1 v2: dep_list A n) (f: A -> A -> B),
    (forall x y, f x y = f y x) -> dep_list_binop f v1 v2 = dep_list_binop f v2 v1.
Proof.
  intros. revert n v1 v2. apply dep_list_ind_2. 1: easy. intros.
  rewrite !dep_list_binop_cons. f_equal; easy.
Qed.

Lemma dep_list_binop_assoc: forall
    {A} {n: nat} (v1 v2 v3: dep_list A n) (f: A -> A -> A),
    (forall x y z, f (f x y) z = f x (f y z)) ->
    dep_list_binop f (dep_list_binop f v1 v2) v3 =
    dep_list_binop f v1 (dep_list_binop f v2 v3).
Proof.
  intros. revert n v1 v2 v3. apply dep_list_ind_3.
  - unfold dep_list_binop. simpl. easy.
  - intros. rewrite !dep_list_binop_cons. f_equal; easy.
Qed.
