(** Lɪʙʀᴀʀʏ ᴏғ Lᴇɴɢᴛʜ-Iɴᴅᴇxᴇᴅ Lɪsᴛ *)
(** Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

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

Fixpoint dep_fold_right {A B: Type} {n: nat}
         (f: B -> A -> A) (dl: dep_list B n) (a: A): A :=
  match dl with
  | dep_nil => a
  | dep_cons b dl' => f b (dep_fold_right f dl' a)
  end.

Definition dep_list_to_list {A: Type} {n: nat} (dl: dep_list A n): list A :=
  dep_fold_right cons dl nil.

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
  dep_map (fun p: A * B => f (fst p) (snd p)) (dep_zip dl1 dl2).

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

Ltac dep_step_decomp v :=
  match type of v with
  | dep_list ?A O  => pose proof (dep_list_O_unique v); subst v
  | dep_list ?A (S ?n) => destruct (dep_list_S_decompose v) as [?v [?v ?]]; subst v
  end.

Ltac dep_list_decomp :=
  repeat   match goal with
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

Lemma dep_list_ind_4: forall
    {A B C D} (P: forall n, dep_list A n -> dep_list B n ->
                            dep_list C n -> dep_list D n -> Prop),
    P O dep_nil dep_nil dep_nil dep_nil ->
    (forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n)
            (v4: dep_list D n), P n v1 v2 v3 v4 -> forall (a: A) (b: B) (c: C) (d: D),
          P (S n) (dep_cons a v1) (dep_cons b v2) (dep_cons c v3) (dep_cons d v4)) ->
    forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n)
           (v4: dep_list D n), P n v1 v2 v3 v4.
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
  forall {A B C: Type} (f: B -> C) (g: A -> B) {n} (dl: dep_list A n),
    dep_map f (dep_map g dl) = dep_map (fun x => f (g x)) dl.
Proof.
  intros. revert n dl. apply dep_list_ind_1; intros; simpl; [| rewrite H]; easy.
Qed.

Lemma dep_map_ext: forall {A B: Type} (g f: A -> B) {n: nat} (l: dep_list A n),
    (forall a, f a = g a) -> dep_map f l = dep_map g l.
Proof.
  intros. revert n l. apply dep_list_ind_1; intros; simpl; [| rewrite H, H0]; easy.
Qed.

Lemma dep_list_binop_nil: forall {A B C} (f: A -> B -> C),
    dep_list_binop f dep_nil dep_nil = dep_nil.
Proof. intros. unfold dep_list_binop. simpl. easy. Qed.

Hint Rewrite @dep_list_binop_nil: dep_list.

Lemma dep_map_nil: forall {A B: Type} (f: A -> B), dep_map f dep_nil = dep_nil.
Proof. intros. now simpl. Qed.

Hint Rewrite @dep_map_nil: dep_list.

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

Lemma dep_transpose_cons_row:
  forall {A m n} (v: dep_list A n) (mat: dep_list (dep_list A n) m),
    dep_list_transpose (dep_cons v mat) =
    dep_list_binop (dep_cons (n:=m)) v (dep_list_transpose mat).
Proof. intros. now simpl. Qed.

Hint Rewrite @dep_transpose_cons_row: dep_list.

Lemma dep_transpose_cons_col:
  forall {A m n} (v: dep_list A m) (mat: dep_list (dep_list A n) m),
    dep_list_transpose (dep_list_binop (dep_cons (n := n)) v mat) =
    dep_cons v (dep_list_transpose mat).
Proof.
  intros. revert m v mat. apply dep_list_ind_2; intros. 1: easy.
  autorewrite with dep_list. rewrite H. now autorewrite with dep_list.
Qed.

Hint Rewrite @dep_transpose_cons_col: dep_list.

Lemma dep_list_transpose_involutive: forall {A m n} (mat: dep_list (dep_list A n) m),
    dep_list_transpose (dep_list_transpose mat) = mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1. 1: apply dep_list_O_unique. intros.
  autorewrite with dep_list. now rewrite H.
Qed.

Hint Rewrite @dep_list_transpose_involutive: dep_list.

Lemma dep_list_transpose_double_map:
  forall {A B} (f: A -> B) {m n} (mat: dep_list (dep_list A n) m),
    dep_list_transpose (dep_map (dep_map f) mat) =
    dep_map (dep_map f) (dep_list_transpose mat).
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros. 2: autorewrite with dep_list.
  - simpl. rewrite dep_map_repeat. now simpl.
  - rewrite H. clear. remember (dep_list_transpose v). clear v Heqd. revert n a d.
    apply dep_list_ind_2; intros; autorewrite with dep_list; simpl. 1: easy.
    f_equal. apply H.
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

Lemma dep_colist_cons: forall {A} {n} (a: A) (l: dep_list A (S n)),
    dep_colist (dep_cons a l) = dep_cons l (dep_map (dep_cons a) (dep_colist l)).
Proof. intros. dep_list_decomp. easy. Qed.

Lemma dep_colist_nil: forall {A} (a: A),
    dep_colist (dep_cons a dep_nil) = dep_cons dep_nil dep_nil.
Proof. intros. easy. Qed.

Hint Rewrite @dep_colist_cons: dep_list.
Hint Rewrite @dep_colist_nil: dep_list.

Lemma dep_list_binop_nest_cons:
  forall {A m n l} (a : A) (v : dep_list A m)
         (mat1 : dep_list (dep_list A n) l)
         (mat2 : dep_list (dep_list (dep_list A m) n) l),
    dep_list_binop (dep_list_binop (dep_cons (n:=m))) (dep_map (dep_cons a) mat1)
                   (dep_map (dep_cons v) mat2) =
    dep_map (dep_cons (dep_cons a v))
            (dep_list_binop (dep_list_binop (dep_cons (n:=m))) mat1 mat2).
Proof.
  intros. revert l mat1 mat2. apply dep_list_ind_2; intros; autorewrite with dep_list.
  1: now simpl. f_equal. apply H.
Qed.

Lemma dep_colist_cons_col:
  forall {A} {m n} (v: dep_list A (S n)) (mat: dep_list (dep_list A m) (S n)),
    dep_colist (dep_list_binop (dep_cons (n := m)) v mat) =
    dep_list_binop (dep_list_binop (dep_cons (n := m)))
                   (dep_colist v) (dep_colist mat).
Proof.
  intros. revert v mat. induction n; intros.
  - dep_list_decomp. autorewrite with dep_list. easy.
  - dep_step_decomp v. dep_step_decomp mat. autorewrite with dep_list. f_equal.
    rewrite IHn. now rewrite dep_list_binop_nest_cons.
Qed.

Lemma dep_map_list_binop: forall {A B C D: Type} (g: C -> D) (f: A -> B -> C) {n: nat}
                                 (l1: dep_list A n) (l2: dep_list B n),
    dep_map g (dep_list_binop f l1 l2) =
    dep_list_binop (fun x y => g (f x y)) l1 l2.
Proof.
  intros. revert n l1 l2. apply dep_list_ind_2; intros; autorewrite with dep_list.
  1: easy. now rewrite H.
Qed.

Lemma dep_list_binop_ext: forall {A B C} (g f: A -> B -> C) {n: nat}
                                 (l1: dep_list A n) (l2: dep_list B n),
    (forall x y, f x y = g x y) -> dep_list_binop f l1 l2 = dep_list_binop g l1 l2.
Proof.
  intros. revert n l1 l2. apply dep_list_ind_2; intros; autorewrite with dep_list.
  1: easy. now rewrite H, H0.
Qed.

Lemma dep_colist_cons_one: forall {A} (a: A) (l: dep_list A O),
    dep_colist (dep_cons a l) = dep_cons dep_nil dep_nil.
Proof. intros. dep_list_decomp. easy. Qed.

Hint Rewrite @dep_colist_cons_one: dep_list.

Lemma dep_map_const: forall {A B} (b: B) {n} (l: dep_list A n),
    dep_map (fun _ => b) l = dep_repeat b n.
Proof.
  intros. revert n l. apply dep_list_ind_1; intros; autorewrite with dep_list. 1: easy.
  simpl. now rewrite H.
Qed.

Hint Rewrite @dep_map_const: dep_list.

Lemma dep_list_binop_const: forall {A B C} (c: C) {n: nat}
                                   (l1: dep_list A n) (l2: dep_list B n),
    dep_list_binop (fun _ _ => c) l1 l2 = dep_repeat c n.
Proof. intros. unfold dep_list_binop. now autorewrite with dep_list. Qed.

Hint Rewrite @dep_list_binop_const: dep_list.

Lemma dep_colist_repeat: forall {A n} (a: A),
    dep_colist (dep_repeat a (S n)) = dep_repeat (dep_repeat a n) (S n).
Proof.
  intros. induction n; simpl dep_repeat.
  - now autorewrite with dep_list.
  - change (dep_cons a (dep_repeat a n)) with (dep_repeat a (S n)).
    autorewrite with dep_list. rewrite IHn. autorewrite with dep_list. now simpl.
Qed.

Hint Rewrite @dep_colist_repeat: dep_list.

Lemma dep_list_binop_map_1: forall {A B C D} (g: D -> A) (f: A -> B -> C) {n}
                                   (l1: dep_list D n) (l2: dep_list B n),
    dep_list_binop (fun x y => f (g x) y) l1 l2 =
    dep_list_binop f (dep_map g l1) l2.
Proof.
  intros. revert n l1 l2. apply dep_list_ind_2; intros; autorewrite with dep_list.
  1: easy. now rewrite H.
Qed.

Lemma dep_list_binop_map_2: forall {A B C D} (g: D -> B) (f: A -> B -> C) {n}
                                   (l1: dep_list A n) (l2: dep_list D n),
    dep_list_binop (fun x y => f x (g y)) l1 l2 =
    dep_list_binop f l1 (dep_map g l2).
Proof.
  intros. revert n l1 l2. apply dep_list_ind_2; intros; autorewrite with dep_list.
  1: easy. now rewrite H.
Qed.

Lemma dep_colist_nest: forall {A m n} (mat: dep_list (dep_list A (S n)) (S m)),
   dep_list_transpose (dep_map (fun x => dep_colist (dep_list_transpose x))
                               (dep_colist (dep_list_transpose mat))) =
   dep_map (dep_map dep_list_transpose)
           (dep_map (fun x => dep_colist (dep_list_transpose x)) (dep_colist mat)).
Proof.
  intros. revert m mat. induction m; intros; dep_step_decomp mat.
  - dep_step_decomp mat1. autorewrite with dep_list. simpl dep_list_transpose.
    change (dep_cons (@dep_nil A) (dep_repeat dep_nil n)) with
        (dep_repeat (@dep_nil A) (S n)).
    rewrite <- (dep_map_nest dep_colist), dep_colist_cons_col, !dep_map_list_binop.
    rewrite (dep_list_binop_ext
               (fun (x : dep_list A n) (y : dep_list (dep_list A 0) n) =>
                  dep_cons (@dep_nil (dep_list A n)) dep_nil)) by
        (intros; now autorewrite with dep_list). autorewrite with dep_list.
    rewrite (dep_list_O_unique (dep_list_transpose (dep_repeat dep_nil n))).
    clear. generalize (S n). intro m. clear.
    induction m; simpl; autorewrite with dep_list. 1: easy. rewrite IHm.
    unfold dep_list_binop. now simpl.
  - autorewrite with dep_list.
    rewrite <- (dep_map_nest dep_colist), dep_colist_cons_col, !dep_map_list_binop.
    rewrite (dep_list_binop_ext
               (fun (x : dep_list A n) (y : dep_list (dep_list A (S m)) n) =>
                  dep_cons
                    (dep_list_transpose y)
                    (dep_map (dep_cons x) (dep_colist (dep_list_transpose y))))) by
        (intros; now autorewrite with dep_list).
    rewrite !dep_map_nest. specialize (IHm mat1). rewrite dep_map_nest in IHm.
    rewrite (dep_map_ext
               (fun a : dep_list (dep_list A (S n)) m =>
                  dep_list_binop (dep_cons (n:=m)) (dep_colist mat0)
                                 (dep_map dep_list_transpose
                                          (dep_colist (dep_list_transpose a))))).
    2: { intros; autorewrite with dep_list. rewrite dep_colist_cons_col.
         rewrite dep_map_list_binop.
         rewrite (dep_list_binop_ext
                    (fun (x : dep_list A n) (y : dep_list (dep_list A m) n) =>
                       dep_cons x (dep_list_transpose y))) by
             (intros; now autorewrite with dep_list).
         rewrite (dep_list_binop_map_2 (@dep_list_transpose A n m)
                                       (dep_cons (n := m))). easy. }
    rewrite (dep_list_binop_map_2
               (@dep_list_transpose A n (S m))
               (fun (x : dep_list A n) (y : dep_list (dep_list A n) (S m)) =>
                  dep_cons y (dep_map (dep_cons x) (dep_colist y)))).
    rewrite <- (dep_map_nest (dep_list_binop (dep_cons (n:=m)) (dep_colist mat0))).
    rewrite <- IHm. clear.
    remember (dep_colist (dep_list_transpose mat1)).
    remember (dep_colist mat0). clear. revert d d0. generalize (S n). intro l.
    revert l. apply dep_list_ind_2; intros; autorewrite with dep_list.
    + simpl. now autorewrite with dep_list.
    + rewrite H. clear. autorewrite with dep_list. f_equal.
      generalize (dep_colist (dep_list_transpose a)).
      generalize (dep_list_transpose
                    (dep_map (fun x : dep_list (dep_list A (S m)) n =>
                                dep_colist (dep_list_transpose x)) v1)). clear.
      intros v1 a. rewrite dep_map_list_binop.
      rewrite (dep_list_binop_ext
                 (fun x y =>
                    dep_cons (dep_cons b x) (dep_list_binop (dep_cons (n:=m)) v2 y)))
        by (intros; now autorewrite with dep_list).
      rewrite (dep_list_binop_map_2 (dep_list_binop (dep_cons (n:=m)) v2)
                                    (fun x y => dep_cons (dep_cons b x) y)).
      now rewrite (dep_list_binop_map_1 (dep_cons b) (dep_cons (n := n0))).
Qed.

Lemma dep_map_double_nest:
  forall {A B C} (f: B -> C) (g: A -> B) {m n} (mat: dep_list (dep_list A n) m),
    dep_map (dep_map f) (dep_map (dep_map g) mat) =
    dep_map (dep_map (fun x => f (g x))) mat.
Proof.
  intros. rewrite dep_map_nest. apply dep_map_ext. intros. now rewrite dep_map_nest.
Qed.

Lemma dep_transpose_app: forall {A m n l} (m1: dep_list (dep_list A l) m)
                                       (m2: dep_list (dep_list A l) n),
    dep_list_transpose (dep_app m1 m2) =
    dep_list_binop dep_app (dep_list_transpose m1) (dep_list_transpose m2).
Proof.
  intros. revert m m1. apply dep_list_ind_1; intros; simpl.
  - generalize (dep_list_transpose m2). clear. revert l.
    apply dep_list_ind_1. 1: easy. intros. simpl. autorewrite with dep_list.
    rewrite <- H. now simpl.
  - rewrite H. generalize (dep_list_transpose v). generalize (dep_list_transpose m2).
    clear. revert l a. apply dep_list_ind_3. 1: easy. intros.
    autorewrite with dep_list. simpl. f_equal. apply H.
Qed.

Lemma dep_list_binop_nest_app:
  forall {A m n l k} (m0 : dep_list A m) (m1 : dep_list A n)
         (m3 : dep_list (dep_list (dep_list A m) l) k)
         (m4 : dep_list (dep_list (dep_list A n) l) k),
    dep_map (dep_cons (dep_app m0 m1))
            (dep_list_binop (dep_list_binop dep_app) m3 m4) =
    dep_list_binop (dep_list_binop dep_app) (dep_map (dep_cons m0) m3)
                   (dep_map (dep_cons m1) m4).
Proof.
  intros. revert k m3 m4. apply dep_list_ind_2; intros; autorewrite with dep_list.
  1: easy. f_equal. apply H.
Qed.

Lemma dep_colist_app: forall {A m n l} (m1 : dep_list (dep_list A m) (S l))
                             (m2 : dep_list (dep_list A n) (S l)),
    dep_colist (dep_list_binop dep_app m1 m2) =
    dep_list_binop (dep_list_binop dep_app) (dep_colist m1) (dep_colist m2).
Proof.
  intros. induction l; intros.
  - dep_list_decomp. autorewrite with dep_list. easy.
  - dep_step_decomp m1. dep_step_decomp m2. autorewrite with dep_list. f_equal.
    rewrite IHl. apply dep_list_binop_nest_app.
Qed.

Definition dep_list_triop {A B C D: Type} (f: A -> B -> C -> D) {n: nat}
           (dl1: dep_list A n) (dl2: dep_list B n) (dl3: dep_list C n): dep_list D n :=
  dep_map (fun p: A * (B * C) => f (fst p) (fst (snd p)) (snd (snd p)))
          (dep_zip dl1 (dep_zip dl2 dl3)).

Lemma dep_list_triop_nil: forall {A B C D} (f: A -> B -> C -> D),
    dep_list_triop f dep_nil dep_nil dep_nil = dep_nil.
Proof. intros. unfold dep_list_triop. simpl. easy. Qed.

Hint Rewrite @dep_list_triop_nil: dep_list.

Lemma dep_list_triop_cons: forall
    {A B C D} {n: nat} (a: A) (b: B) (c: C)
    (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n) (f: A -> B -> C -> D),
    dep_list_triop f (dep_cons a v1) (dep_cons b v2) (dep_cons c v3) =
    dep_cons (f a b c) (dep_list_triop f v1 v2 v3).
Proof. intros. unfold dep_list_triop. simpl. easy. Qed.

Hint Rewrite @dep_list_triop_cons: dep_list.

Lemma dep_list_binop_triop: forall
    {A B C D E n} (f: A -> D -> E) (g: B -> C -> D) (l1: dep_list A n)
    (l2: dep_list B n) (l3: dep_list C n),
    dep_list_binop f l1 (dep_list_binop g l2 l3) =
    dep_list_triop (fun x y z => f x (g y z)) l1 l2 l3.
Proof.
  intros. revert n l1 l2 l3. apply dep_list_ind_3; intros; autorewrite with dep_list.
  1: easy. now rewrite H.
Qed.

Lemma dep_list_triop_ext: forall
    {A B C D} (g f: A -> B -> C -> D) {n: nat}
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n),
    (forall x y z, f x y z = g x y z) ->
    dep_list_triop f l1 l2 l3 = dep_list_triop g l1 l2 l3.
Proof.
  intros. revert n l1 l2 l3. apply dep_list_ind_3; intros; autorewrite with dep_list.
  1: easy. now rewrite H, H0.
Qed.

Definition dep_list_quadruple {A B C D E: Type} (f: A -> B -> C -> D -> E) {n: nat}
           (dl1: dep_list A n) (dl2: dep_list B n) (dl3: dep_list C n)
           (dl4: dep_list D n): dep_list E n :=
  dep_map (fun p: A * (B * (C * D)) =>
             f (fst p) (fst (snd p)) (fst (snd (snd p))) (snd (snd (snd p))))
          (dep_zip dl1 (dep_zip dl2 (dep_zip dl3 dl4))).

Lemma dep_list_quadruple_nil: forall {A B C D E} (f: A -> B -> C -> D -> E),
    dep_list_quadruple f dep_nil dep_nil dep_nil dep_nil = dep_nil.
Proof. intros. unfold dep_list_quadruple. simpl. easy. Qed.

Hint Rewrite @dep_list_quadruple_nil: dep_list.

Lemma dep_list_quadruple_cons: forall
    {A B C D E} {n: nat} (a: A) (b: B) (c: C) (d: D) (f: A -> B -> C -> D -> E)
    (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n) (v4: dep_list D n),
    dep_list_quadruple
      f (dep_cons a v1) (dep_cons b v2) (dep_cons c v3) (dep_cons d v4) =
    dep_cons (f a b c d) (dep_list_quadruple f v1 v2 v3 v4).
Proof. intros. unfold dep_list_quadruple. simpl. easy. Qed.

Hint Rewrite @dep_list_quadruple_cons: dep_list.

Lemma dep_list_triop_quadruple: forall
    {A B C D E F n} (f: A -> D -> E -> F) (g: B -> C -> D)
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list E n),
    dep_list_triop f l1 (dep_list_binop g l2 l3) l4 =
    dep_list_quadruple (fun x y z w => f x (g y z) w) l1 l2 l3 l4.
Proof.
  intros. revert n l1 l2 l3 l4.
  apply dep_list_ind_4; intros; autorewrite with dep_list; [|rewrite H]; easy.
Qed.

Lemma dep_list_quadruple_ext: forall
    {A B C D E} (g f: A -> B -> C -> D -> E) {n: nat}
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n),
    (forall x y z w, f x y z w = g x y z w) ->
    dep_list_quadruple f l1 l2 l3 l4 = dep_list_quadruple g l1 l2 l3 l4.
Proof.
  intros. revert n l1 l2 l3 l4.
  apply dep_list_ind_4; intros; autorewrite with dep_list; [| rewrite H, H0]; easy.
Qed.

Lemma dep_list_quadruple_split: forall
    {A B C D E F G n} (f: A -> B -> D -> E) (g: A -> C -> D -> F) (h: E -> F -> G)
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n),
    dep_list_quadruple (fun x y z w => h (f x y w) (g x z w)) l1 l2 l3 l4 =
    dep_list_binop h (dep_list_triop f l1 l2 l4) (dep_list_triop g l1 l3 l4).
Proof.
  intros. revert n l1 l2 l3 l4.
  apply dep_list_ind_4; intros; autorewrite with dep_list; [|rewrite H]; easy.
Qed.
