Require Import Coq.Lists.List.

Inductive dep_list (A: Type): nat -> Type :=
| dep_nil: dep_list A O
| dep_cons: forall n: nat, A -> dep_list A n -> dep_list A (S n).

Arguments dep_nil [_].
Arguments dep_cons [_ _] _ _.

Fixpoint dep_fold_left {A B: Type} {n: nat}
         (f: A -> B -> A) (dl: dep_list B n) (a: A) : A :=
  match dl with
  | dep_nil => a
  | dep_cons b dl' => dep_fold_left f dl' (f a b)
  end.

Eval compute in (dep_fold_left Nat.add (dep_cons 2 (dep_cons 1 dep_nil)) O).

Fixpoint dep_fold_right {A B: Type} {n: nat}
         (f: B -> A -> A) (dl: dep_list B n) (a: A) : A :=
  match dl with
  | dep_nil => a
  | dep_cons b dl' => f b (dep_fold_right f dl' a)
  end.

Eval compute in (dep_fold_right Nat.sub (dep_cons 2 (dep_cons 1 dep_nil)) O).

Definition dep_to_list {A: Type} {n: nat} (dl: dep_list A n) : list A :=
  dep_fold_right cons dl nil.

Eval compute in (dep_to_list (dep_cons 2 (dep_cons 1 dep_nil))).

Fixpoint dep_app {A: Type} {n m: nat} (dl1: dep_list A n) (dl2: dep_list A m)
  : dep_list A (n + m) :=
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

Definition dep_binop {A B C: Type} (f: A -> B -> C) {n: nat}
           (dl1: dep_list A n) (dl2: dep_list B n) : dep_list C n :=
  dep_map (fun p: (A * B) => f (fst p) (snd p)) (dep_zip dl1 dl2).
