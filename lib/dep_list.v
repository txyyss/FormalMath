(** Lɪʙʀᴀʀʏ ᴏғ Lᴇɴɢᴛʜ-Iɴᴅᴇxᴇᴅ Lɪsᴛ *)
(** Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import FormalMath.lib.Coqlib.

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

Ltac dep_list_decomp :=
  repeat match goal with
  | v: dep_list ?A O |- _ => pose proof (dep_list_O_unique v); subst v
  | v: dep_list ?A (S ?n) |- _ =>
    destruct (dep_list_S_decompose v) as [?v [?v ?]]; subst v
         end.

Lemma dep_list_add_decompose: forall {A} {m n: nat} (l: dep_list A (m + n)),
    {l1: dep_list A m & {l2: dep_list A n | l = dep_app l1 l2}}.
Proof.
  intros A. induction m; intros.
  - simpl in *. now exists dep_nil, l.
  - revert l.
    cut (forall l : dep_list A (S (m + n)),
            {l1 : dep_list A (S m) & {l2 : dep_list A n | l = dep_app l1 l2}}); intros.
    1: apply X. dep_list_decomp. destruct (IHm _ l1) as [?l [?l ?H]].
    exists (dep_cons l0 l), l2. now subst l1.
Qed.

Ltac dep_add_decomp :=
  repeat match goal with
  | v: dep_list ?A (?m + ?n) |- _ =>
    destruct (dep_list_add_decompose v) as [?v [?v ?]]; subst v
  end.

Ltac dep_step_decomp v :=
  match type of v with
  | dep_list ?A O  => pose proof (dep_list_O_unique v); subst v
  | dep_list ?A (S ?n) => destruct (dep_list_S_decompose v) as [?v [?v ?]]; subst v
  | dep_list ?A (?m + ?n) =>
    destruct (dep_list_add_decompose v) as [?v [?v ?]]; subst v
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

Lemma dep_list_ind_5: forall
    {A B C D E} (P: forall n, dep_list A n -> dep_list B n ->
                              dep_list C n -> dep_list D n -> dep_list E n -> Prop),
    P O dep_nil dep_nil dep_nil dep_nil dep_nil ->
    (forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n)
            (v4: dep_list D n) (v5: dep_list E n),
        P n v1 v2 v3 v4 v5 ->
        forall (a: A) (b: B) (c: C) (d: D) (e: E),
          P (S n) (dep_cons a v1) (dep_cons b v2) (dep_cons c v3)
            (dep_cons d v4) (dep_cons e v5)) ->
    forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n)
           (v4: dep_list D n) (v5: dep_list E n), P n v1 v2 v3 v4 v5.
Proof.
  intros until n. induction n; intros; dep_list_decomp; [easy | apply H0, IHn].
Qed.

Lemma dep_list_ind_6: forall
    {A B C D E F}
    (P: forall n, dep_list A n -> dep_list B n -> dep_list C n -> dep_list D n ->
                  dep_list E n -> dep_list F n -> Prop),
    P O dep_nil dep_nil dep_nil dep_nil dep_nil dep_nil ->
    (forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n)
            (v4: dep_list D n) (v5: dep_list E n) (v6: dep_list F n),
        P n v1 v2 v3 v4 v5 v6->
        forall (a: A) (b: B) (c: C) (d: D) (e: E) (f: F),
          P (S n) (dep_cons a v1) (dep_cons b v2) (dep_cons c v3)
            (dep_cons d v4) (dep_cons e v5) (dep_cons f v6)) ->
    forall (n: nat) (v1: dep_list A n) (v2: dep_list B n) (v3: dep_list C n)
           (v4: dep_list D n) (v5: dep_list E n) (v6: dep_list F n),
      P n v1 v2 v3 v4 v5 v6.
Proof.
  intros until n. induction n; intros; dep_list_decomp; [easy | apply H0, IHn].
Qed.

Lemma dep_cons_app: forall {A n m} (a: A) (l1: dep_list A n) (l2: dep_list A m),
    dep_cons a (dep_app l1 l2) = dep_app (dep_cons a l1) l2.
Proof. intros. now simpl dep_app. Qed.

Lemma dep_cons_eq_inv: forall {A n} (a1 a2: A) (l1 l2: dep_list A n),
    dep_cons a1 l1 = dep_cons a2 l2 -> a1 = a2 /\ l1 = l2.
Proof.
  intros. inversion H. split; auto.
  apply inj_pair2_eq_dec in H2; [easy | exact Nat.eq_dec].
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

Lemma dep_list_binop_app: forall
    {A B C} {m n: nat} (v1: dep_list A m) (v3: dep_list A n)
    (v2: dep_list B m) (v4: dep_list B n) (f: A -> B -> C),
    dep_list_binop f (dep_app v1 v3) (dep_app v2 v4) =
    dep_app (dep_list_binop f v1 v2) (dep_list_binop f v3 v4).
Proof.
  intros. revert m v1 v2. apply dep_list_ind_2; intros. 1: now simpl.
  autorewrite with dep_list. simpl. autorewrite with dep_list. now rewrite H.
Qed.

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

Lemma dep_repeat_app: forall {A} (e: A) (m n: nat),
    dep_repeat e (m + n) = dep_app (dep_repeat e m) (dep_repeat e n).
Proof. intros. induction m; simpl; [|rewrite IHm]; easy. Qed.

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
             end eq_refl
  end eq_refl.

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

Lemma dep_list_triop_quadruple': forall
    {A B C D E F n} (f: A -> B -> E -> F) (g: C -> B -> D -> E) (l1: dep_list A n)
    (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n),
    dep_list_triop f l1 l2 (dep_list_triop g l3 l2 l4) =
    dep_list_quadruple (fun x y z w => f x y (g z y w)) l1 l2 l3 l4.
Proof.
  intros. revert n l1 l2 l3 l4.
  apply dep_list_ind_4; intros; autorewrite with dep_list; [|rewrite H]; easy.
Qed.

Lemma dep_list_quadruple_const: forall
    {A B C D E} (c: E) {n: nat} (l1: dep_list A n)
    (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n),
    dep_list_quadruple (fun _ _ _ _ => c) l1 l2 l3 l4 = dep_repeat c n.
Proof. intros. unfold dep_list_quadruple. now autorewrite with dep_list. Qed.

Hint Rewrite @dep_list_quadruple_const: dep_list.

Definition dep_list_quintuple {A B C D E F: Type} (f: A -> B -> C -> D -> E -> F)
           {n: nat} (dl1: dep_list A n) (dl2: dep_list B n) (dl3: dep_list C n)
           (dl4: dep_list D n) (dl5: dep_list E n): dep_list F n :=
  dep_map (fun p: A * (B * (C * (D * E))) =>
             f (fst p) (fst (snd p)) (fst (snd (snd p))) (fst (snd (snd (snd p))))
               (snd (snd (snd (snd p)))))
          (dep_zip dl1 (dep_zip dl2 (dep_zip dl3 (dep_zip dl4 dl5)))).

Lemma dep_list_quintuple_nil: forall {A B C D E F} (f: A -> B -> C -> D -> E -> F),
    dep_list_quintuple f dep_nil dep_nil dep_nil dep_nil dep_nil = dep_nil.
Proof. intros. unfold dep_list_quintuple. simpl. easy. Qed.

Hint Rewrite @dep_list_quintuple_nil: dep_list.

Lemma dep_list_quintuple_cons: forall
    {A B C D E F} {n: nat} (a: A) (b: B) (c: C) (d: D) (e: E)
    (f: A -> B -> C -> D -> E -> F) (v1: dep_list A n) (v2: dep_list B n)
    (v3: dep_list C n) (v4: dep_list D n) (v5: dep_list E n),
    dep_list_quintuple
      f (dep_cons a v1) (dep_cons b v2) (dep_cons c v3) (dep_cons d v4) (dep_cons e v5)
    = dep_cons (f a b c d e) (dep_list_quintuple f v1 v2 v3 v4 v5).
Proof. intros. unfold dep_list_quintuple. simpl. easy. Qed.

Hint Rewrite @dep_list_quintuple_cons: dep_list.

Lemma dep_list_triop_quintuple: forall
    {A B C D E F G n} (f: A -> B -> F -> G) (g: C -> D -> E -> F) (l1: dep_list A n)
    (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n) (l5: dep_list E n),
    dep_list_triop f l1 l2 (dep_list_triop g l3 l4 l5) =
    dep_list_quintuple (fun x y z w v => f x y (g z w v)) l1 l2 l3 l4 l5.
Proof.
  intros. revert n l1 l2 l3 l4 l5.
  apply dep_list_ind_5; intros; autorewrite with dep_list; [|rewrite H]; easy.
Qed.

Lemma dep_list_quintuple_ext: forall
    {A B C D E F n} (g f: A -> B -> C -> D -> E -> F) (l1: dep_list A n)
    (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n) (l5: dep_list E n),
    (forall x y z w v, f x y z w v = g x y z w v) ->
    dep_list_quintuple f l1 l2 l3 l4 l5 = dep_list_quintuple g l1 l2 l3 l4 l5.
Proof.
  intros. revert n l1 l2 l3 l4 l5.
  apply dep_list_ind_5; intros; autorewrite with dep_list; [|rewrite H, H0]; easy.
Qed.

Lemma dep_list_quintuple_constant_split: forall
    {A B C D E F G H n} (f: A -> B -> C -> D -> E -> F) (a: G) (h: G -> F -> H)
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n)
    (l5: dep_list E n),
    dep_list_quintuple (fun x y z w v => h a (f x y z w v)) l1 l2 l3 l4 l5 =
    dep_map (h a) (dep_list_quintuple f l1 l2 l3 l4 l5).
Proof.
  intros. revert n l1 l2 l3 l4 l5.
  apply dep_list_ind_5; intros; autorewrite with dep_list; [|rewrite H0]; easy.
Qed.

Definition dep_list_sextuple {A B C D E F G: Type} (f: A -> B -> C -> D -> E -> F -> G)
           {n: nat} (dl1: dep_list A n) (dl2: dep_list B n) (dl3: dep_list C n)
           (dl4: dep_list D n) (dl5: dep_list E n) (dl6: dep_list F n): dep_list G n :=
  dep_map (fun p: A * (B * (C * (D * (E * F)))) =>
             f (fst p) (fst (snd p)) (fst (snd (snd p))) (fst (snd (snd (snd p))))
               (fst (snd (snd (snd (snd p))))) (snd (snd (snd (snd (snd p))))))
          (dep_zip dl1 (dep_zip dl2 (dep_zip dl3 (dep_zip dl4 (dep_zip dl5 dl6))))).

Lemma dep_list_sextuple_nil: forall {A B C D E F G}
                                    (f: A -> B -> C -> D -> E -> F -> G),
    dep_list_sextuple f dep_nil dep_nil dep_nil dep_nil dep_nil dep_nil = dep_nil.
Proof. intros. unfold dep_list_sextuple. simpl. easy. Qed.

Hint Rewrite @dep_list_sextuple_nil: dep_list.

Lemma dep_list_sextuple_cons: forall
    {A B C D E F G} {n: nat} (a: A) (b: B) (c: C) (d: D) (e: E) (f: F)
    (fn: A -> B -> C -> D -> E -> F -> G) (v1: dep_list A n) (v2: dep_list B n)
    (v3: dep_list C n) (v4: dep_list D n) (v5: dep_list E n) (v6: dep_list F n),
    dep_list_sextuple
      fn (dep_cons a v1) (dep_cons b v2) (dep_cons c v3) (dep_cons d v4)
      (dep_cons e v5) (dep_cons f v6) =
    dep_cons (fn a b c d e f) (dep_list_sextuple fn v1 v2 v3 v4 v5 v6).
Proof. intros. unfold dep_list_sextuple. simpl. easy. Qed.

Hint Rewrite @dep_list_sextuple_cons: dep_list.

Lemma dep_list_tri_quad_sextuple: forall
    {A B C D E F G H n} (f: A -> B -> G -> H) (g: C -> D -> E -> F -> G)
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n)
    (l5: dep_list E n) (l6: dep_list F n),
    dep_list_triop f l1 l2 (dep_list_quadruple g l3 l4 l5 l6) =
    dep_list_sextuple (fun x y z w v u => f x y (g z w v u)) l1 l2 l3 l4 l5 l6.
Proof.
  intros. revert n l1 l2 l3 l4 l5 l6.
  apply dep_list_ind_6; intros; autorewrite with dep_list; [|rewrite H0]; easy.
Qed.

Lemma dep_list_sextuple_ext: forall
    {A B C D E F G n} (g f: A -> B -> C -> D -> E -> F -> G)
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n)
    (l5: dep_list E n) (l6: dep_list F n),
    (forall x y z w v u, f x y z w v u = g x y z w v u) ->
    dep_list_sextuple f l1 l2 l3 l4 l5 l6 = dep_list_sextuple g l1 l2 l3 l4 l5 l6.
Proof.
  intros. revert n l1 l2 l3 l4 l5 l6.
  apply dep_list_ind_6; intros; autorewrite with dep_list; [|rewrite H, H0]; easy.
Qed.

Lemma dep_list_sextuple_split: forall
    {A B C D E F G H I n} (f: A -> B -> C -> D -> F -> G)
    (g: A -> B -> C -> E -> F -> H) (h: G -> H -> I)
    (l1: dep_list A n) (l2: dep_list B n) (l3: dep_list C n) (l4: dep_list D n)
    (l5: dep_list E n) (l6: dep_list F n),
    dep_list_sextuple (fun x y z w v u => h (f x y z w u) (g x y z v u))
                      l1 l2 l3 l4 l5 l6 =
    dep_list_binop h (dep_list_quintuple f l1 l2 l3 l4 l6)
                   (dep_list_quintuple g l1 l2 l3 l5 l6).
Proof.
  intros. revert n l1 l2 l3 l4 l5 l6.
  apply dep_list_ind_6; intros; autorewrite with dep_list; [|rewrite H0]; easy.
Qed.

Definition dep_tl {A: Type} {n: nat} (l: dep_list A (S n)): dep_list A n :=
  match l in (dep_list _ m) return (m = S n -> dep_list A n) with
  | dep_nil => fun p => False_rect _ (O_S _ p)
  | dep_cons _ l' => fun p => eq_rect_r _ (fun l1 => l1) (eq_add_S _ _ p) l'
  end eq_refl.

Lemma dep_tl_cons: forall {A n} (a: A) (l: dep_list A n), dep_tl (dep_cons a l) = l.
Proof. intros. easy. Qed.

Hint Rewrite @dep_tl_cons: dep_list.

Lemma dep_tl_cons_col: forall {A m n} (v: dep_list A m)
                              (mat: dep_list (dep_list A n) m),
    dep_map dep_tl (dep_list_binop (@dep_cons _ n) v mat) = mat.
Proof.
  intros. revert m v mat.
  apply dep_list_ind_2; intros; autorewrite with dep_list; [| rewrite H]; easy.
Qed.

Hint Rewrite @dep_tl_cons_col: dep_list.

Fixpoint dep_nth {A: Type} (i: nat) {n: nat} (l: dep_list A n) (default: A) : A :=
  match i with
  | O => match l with
         | dep_nil => default
         | dep_cons x _ => x
         end
  | S m => match l with
           | dep_nil => default
           | dep_cons _ t => dep_nth m t default
           end
  end.

Lemma dep_nth_overflow: forall {A n} (i: nat) (l: dep_list A n) (d: A),
    n <= i -> dep_nth i l d = d.
Proof.
  intros A n i. revert n. induction i; intros.
  - apply le_n_0_eq in H. subst n. dep_list_decomp. now simpl.
  - simpl. destruct l. 1: easy. apply le_S_n in H. now apply IHi.
Qed.

Lemma dep_nth_indep: forall {A n} (i: nat) (l: dep_list A n) (d d': A),
    i < n -> dep_nth i l d = dep_nth i l d'.
Proof.
  intros A n i. revert n. induction i; intros.
  - apply Nat.succ_pred_pos in H. remember (pred n) as m. clear Heqm. subst n.
    dep_list_decomp. now simpl.
  - destruct n.
    + exfalso. now apply Nat.nlt_0_r in H.
    + dep_list_decomp. simpl. apply IHi. now apply lt_S_n.
Qed.

Lemma dep_nth_app_cons:
  forall {A} (i: nat) {n: nat} (l1: dep_list A i) (l2: dep_list A n) (a d: A),
    dep_nth i (dep_app l1 (dep_cons a l2)) d = a.
Proof.
  intros A. induction i; intros; dep_list_decomp; simpl; [|apply IHi]; easy.
Qed.

Lemma dep_nth_eq_iff:
  forall {A} {n: nat} (l1 l2: dep_list A n),
    (forall d1 d2 i, i < n -> dep_nth i l1 d1 = dep_nth i l2 d2) <-> l1 = l2.
Proof.
  intro. apply dep_list_ind_2.
  - split; intros; simpl. 1: easy. exfalso. now apply Nat.nlt_0_r in H0.
  - intros. split; intros.
    + f_equal.
      * specialize (H0 a b O (Nat.lt_0_succ n)). now simpl in H0.
      * rewrite <- H. intros. apply lt_n_S in H1.
        specialize (H0 d1 d2 _ H1). now simpl in H0.
    + apply dep_cons_eq_inv in H0. destruct H0. subst. destruct i.
      * now simpl.
      * simpl. now apply dep_nth_indep, lt_S_n.
Qed.

Lemma dep_nth_app_1:
  forall {A} (i: nat) {m n: nat} (l1: dep_list A m) (l2: dep_list A n) (d: A),
    i < m -> dep_nth i l1 d = dep_nth i (dep_app l1 l2) d.
Proof.
  intros A. induction i; intros.
  - apply Nat.succ_pred_pos in H. remember (pred m) as m1. clear Heqm1. subst m.
    dep_list_decomp. now simpl.
  - destruct m. 1: exfalso; now apply Nat.nlt_0_r in H. dep_list_decomp. simpl.
    now apply IHi, lt_S_n.
Qed.

Lemma dep_nth_app_2:
  forall {A} (i: nat) {m n: nat} (l1: dep_list A m) (l2: dep_list A n) (d: A),
    dep_nth i l2 d = dep_nth (m + i) (dep_app l1 l2) d.
Proof.
  intros. revert m l1 i n l2 d. induction m; intros; dep_list_decomp.
  - now simpl.
  - rewrite plus_Sn_m, <- dep_cons_app. simpl. apply IHm.
Qed.

Lemma dep_nth_cons: forall {A} (i: nat) {n: nat} (l: dep_list A n) (a d: A),
    dep_nth i l d = dep_nth (S i) (dep_cons a l) d.
Proof. intros. now simpl. Qed.

Lemma dep_nth_nil: forall {A} (i: nat) d, dep_nth i (@dep_nil A) d = d.
Proof. intros. rewrite dep_nth_overflow; [easy | apply Nat.le_0_l]. Qed.

Hint Rewrite @dep_nth_nil: dep_list.

Lemma dep_nth_list_binop: forall {A B C: Type} (f: A -> B -> C) {n: nat}
                                 (dl1: dep_list A n) (dl2: dep_list B n) i d1 d2 d,
    f d1 d2 = d -> dep_nth i (dep_list_binop f dl1 dl2) d =
                   f (dep_nth i dl1 d1) (dep_nth i dl2 d2).
Proof.
  intros. revert n dl1 dl2 i. induction n; intros; dep_list_decomp.
  - now autorewrite with dep_list.
  - rewrite dep_list_binop_cons. destruct i; simpl; auto.
Qed.

Lemma dep_nth_repeat: forall {A n} (i: nat) (e d: A),
    i < n -> dep_nth i (dep_repeat e n) d = e.
Proof.
  intros. decomp_lt_subst. rewrite dep_repeat_app. simpl. now rewrite dep_nth_app_cons.
Qed.

Definition rev_rel {A} {n: nat} (l1 l2: dep_list A n): Prop :=
  forall d i, i < n -> dep_nth i l1 d = dep_nth (n - 1 - i) l2 d.

Lemma rev_rel_nil: forall {A}, @rev_rel A _ dep_nil dep_nil.
Proof. intros. red. intros. now apply Nat.nlt_0_r in H. Qed.

Lemma rev_rel_sym: forall {A n} (l1 l2: dep_list A n), rev_rel l1 l2 -> rev_rel l2 l1.
Proof.
  intros. unfold rev_rel in *. intros. specialize (H d _ (lt_sub_1_sub_lt _ _ H0)).
  now rewrite lt_sub1_sub1_sub_eq in H.
Qed.

Lemma rev_rel_exists: forall {A n} (l: dep_list A n), exists l', rev_rel l l'.
Proof.
  intro. apply dep_list_ind_1; intros.
  - exists dep_nil. apply rev_rel_nil.
  - destruct H as [l2 ?]. rename v into l1.
    remember (dep_app l2 (dep_cons a dep_nil)) as l3.
    assert (forall d i, i < n -> dep_nth i l3 d = dep_nth i l2 d). {
      intros. subst l3. now rewrite <- dep_nth_app_1. }
    assert (forall d, dep_nth n l3 d = a). {
      intros. subst l3. now rewrite dep_nth_app_cons. } clear Heql3.
    remember (n + 1) as m. rewrite Nat.add_1_r in Heqm. subst m. exists l3.
    unfold rev_rel in *. intros. destruct i; simpl; rewrite !Nat.sub_0_r.
    1: now rewrite H1. rewrite <- Nat.succ_lt_mono in H2.
    rewrite <- Nat.add_1_l, Nat.sub_add_distr, H, H0; auto. now apply lt_sub_1_sub_lt.
Qed.

Lemma rev_rel_unique: forall {A n} (l l1 l2: dep_list A n),
    rev_rel l l1 -> rev_rel l l2 -> l1 = l2.
Proof.
  intros. red in H, H0. rewrite <- dep_nth_eq_iff. intros.
  pose proof (lt_sub_1_sub_lt _ _ H1). specialize (H d1 _ H2). specialize (H0 d2 _ H2).
  rewrite lt_sub1_sub1_sub_eq in *; auto. rewrite <- H, <- H0. now apply dep_nth_indep.
Qed.

Lemma double_rev_rel_eq: forall {A n} (l1 l2 l3: dep_list A n),
    rev_rel l1 l2 -> rev_rel l2 l3 -> l1 = l3.
Proof. intros. apply rev_rel_sym in H. now apply rev_rel_unique with l2. Qed.

Definition row_rev_rel {A: Type} {m n: nat} (m1 m2: dep_list (dep_list A n) m): Prop :=
  forall row d, row < m -> rev_rel (dep_nth row m1 d) (dep_nth row m2 d).

Lemma row_rev_rel_sym: forall {A m n} (m1 m2: dep_list (dep_list A n) m),
    row_rev_rel m1 m2 -> row_rev_rel m2 m1.
Proof. intros. unfold row_rev_rel in *. intros. now apply rev_rel_sym, H. Qed.

Lemma row_rev_rel_cons: forall
    {A m n} (v1 v2: dep_list A n) (mat1 mat2: dep_list (dep_list A n) m),
    rev_rel v1 v2 -> row_rev_rel mat1 mat2 ->
    row_rev_rel (dep_cons v1 mat1) (dep_cons v2 mat2).
Proof.
  intros. unfold row_rev_rel in *. intros.
  destruct row; simpl; [|apply H0, lt_S_n]; easy.
Qed.

Lemma row_rev_rel_exists: forall {A m n} (mat: dep_list (dep_list A n) m),
    exists mat', row_rev_rel mat mat'.
Proof.
  intro. induction m; intros; dep_list_decomp.
  - exists dep_nil. red. intros. now apply Nat.nlt_0_r in H.
  - rename mat0 into v. destruct (rev_rel_exists v) as [v' ?].
    destruct (IHm _ mat1) as [mat2 ?]. exists (dep_cons v' mat2).
    now apply row_rev_rel_cons.
Qed.

Lemma row_rev_rel_unique: forall {A m n} (mat mat1 mat2: dep_list (dep_list A n) m),
    row_rev_rel mat mat1 -> row_rev_rel mat mat2 -> mat1 = mat2.
Proof.
  intros. rewrite <- dep_nth_eq_iff. intros. rewrite (dep_nth_indep _ _ d1 d2); auto.
  unfold row_rev_rel in *. specialize (H _ d2 H1). specialize (H0 _ d2 H1).
  now apply rev_rel_unique with (dep_nth i mat d2).
Qed.

Lemma double_row_rev_rel_eq: forall {A m n} (m1 m2 m3: dep_list (dep_list A n) m),
    row_rev_rel m1 m2 -> row_rev_rel m2 m3 -> m1 = m3.
Proof. intros. apply row_rev_rel_sym in H. now apply row_rev_rel_unique with m2. Qed.

Lemma row_rev_comm_rev: forall {A m n} (m1 m2 m3 m4 m5: dep_list (dep_list A n) m),
    row_rev_rel m1 m2 -> rev_rel m2 m3 ->
    rev_rel m1 m4 -> row_rev_rel m4 m5 -> m3 = m5.
Proof.
  intros. unfold rev_rel, row_rev_rel in *. rewrite <- dep_nth_eq_iff.
  intros ? ? row ?. rewrite (dep_nth_indep _ _ d1 d2 H3). clear d1. rename d2 into d.
  pose proof (lt_sub_1_sub_lt _ _ H3). specialize (H _ d H4). specialize (H0 d _ H4).
  specialize (H1 d _ H4). specialize (H2 _ d H3).
  assert (m - 1 - (m - 1 - row) = row). {
    rewrite subsub_eq; auto. rewrite <- (Nat.add_sub row 1), Nat.add_1_r.
    now apply Nat.sub_le_mono_r. } rewrite H5 in *. rewrite H0 in H.
  rewrite <- H1 in H2. eapply rev_rel_unique; eauto.
Qed.

Definition dual_rev_rel {A: Type} {m n: nat}(m1 m2: dep_list (dep_list A n) m): Prop :=
  exists m3, row_rev_rel m1 m3 /\ rev_rel m3 m2.

Lemma dual_rev_rel_sym: forall {A m n} (m1 m2: dep_list (dep_list A n) m),
    dual_rev_rel m1 m2 -> dual_rev_rel m2 m1.
Proof.
  intros. unfold dual_rev_rel in *. destruct H as [m3 [? ?]].
  destruct (row_rev_rel_exists m2) as [m4 ?]. exists m4. split; auto.
  apply rev_rel_sym in H0. apply row_rev_rel_sym in H.
  destruct (rev_rel_exists m4) as [m5 ?].
  pose proof (row_rev_comm_rev _ _ _ _ _ H1 H2 H0 H). now subst.
Qed.

Lemma dual_rev_rel_exists: forall {A m n} (mat: dep_list (dep_list A n) m),
    exists mat', dual_rev_rel mat mat'.
Proof.
  intros. destruct (row_rev_rel_exists mat) as [mat1 ?].
  destruct (rev_rel_exists mat1) as [mat2 ?]. exists mat2. red. exists mat1. now split.
Qed.

Lemma dual_rev_rel_unique: forall {A m n} (mat mat1 mat2: dep_list (dep_list A n) m),
    dual_rev_rel mat mat1 -> dual_rev_rel mat mat2 -> mat1 = mat2.
Proof.
  intros. red in H, H0. destruct H as [m3 [? ?]]. destruct H0 as [m4 [? ?]].
  assert (m3 = m4) by (eapply row_rev_rel_unique; eauto). subst.
  eapply rev_rel_unique; eauto.
Qed.

Lemma double_dual_rev_rel_eq: forall A m n (m1 m2 m3: dep_list (dep_list A n) m),
    dual_rev_rel m1 m2 -> dual_rev_rel m2 m3 -> m1 = m3.
Proof. intros. apply dual_rev_rel_sym in H. now apply dual_rev_rel_unique with m2. Qed.

Fixpoint dep_to_list {A} {n} (l: dep_list A n): list A :=
  match l with
  | dep_nil => nil
  | dep_cons a l' => a :: dep_to_list l'
  end.

Lemma dep_to_list_len: forall {A n} (l: dep_list A n), length (dep_to_list l) = n.
Proof. intro. induction n; intros; dep_list_decomp; simpl; [|rewrite IHn]; easy. Qed.

Lemma dep_to_list_nth: forall {A n} (l: dep_list A n) (d: A) (i: nat),
    dep_nth i l d = nth i (dep_to_list l) d.
Proof.
  intros. destruct (le_lt_dec n i).
  - rewrite dep_nth_overflow, nth_overflow; auto. now rewrite dep_to_list_len.
  - revert l i l0. induction n; intros.
    + now apply Nat.nlt_0_r in l0.
    + dep_list_decomp. destruct i; simpl; [| apply IHn, lt_S_n]; easy.
Qed.

Lemma dep_vertical_split: forall {A n m} (mat: dep_list (dep_list A (S n)) m),
    exists v mat', mat = (dep_list_binop (dep_cons (n := n)) v mat').
Proof.
  intros. pose proof (dep_list_transpose_involutive mat).
  remember (dep_list_transpose mat) as mat0. dep_step_decomp mat0. rewrite e in H.
  clear e. rewrite dep_transpose_cons_row in H.
  remember (dep_list_transpose mat2) as mat3. now exists mat1, mat3.
Qed.

Lemma dep_list_binop_cons_eq: forall
    {A m n} (v1 v2: dep_list A m) (mat1 mat2: dep_list (dep_list A n) m),
    dep_list_binop (dep_cons (n:=n)) v1 mat1 =
    dep_list_binop (dep_cons (n:=n)) v2 mat2 -> v1 = v2 /\ mat1 = mat2.
Proof.
  intros. revert m v1 v2 mat1 mat2 H. induction m; intros; dep_list_decomp; auto.
  autorewrite with dep_list in H. do 2 (apply dep_cons_eq_inv in H; destruct H).
  apply IHm in H0. destruct H0. subst. easy.
Qed.

Lemma dep_nth_transpose: forall {A m n} d3 (mat: dep_list (dep_list A n) m) i j d1 d2,
    i < m -> j < n -> dep_nth i (dep_nth j (dep_list_transpose mat) d1) d2 =
                      dep_nth j (dep_nth i mat d3) d2.
Proof.
  intro. induction m, n; intros; [inversion H | inversion H | inversion H0 |].
  dep_list_decomp. destruct (dep_vertical_split mat1) as [v [mat4 ?]]. subst.
  rename mat4 into mat1. destruct i, j; simpl dep_nth at 4; autorewrite with dep_list.
  - simpl dep_nth at 3. now simpl.
  - simpl dep_nth at 3. simpl dep_nth at 2.
    rewrite (dep_nth_list_binop _ _ _ _ d0 d4); auto. simpl.
    now apply dep_nth_indep, lt_S_n.
  - simpl dep_nth at 2. rewrite (dep_nth_list_binop _ _ _ _ d1 d5); auto. simpl.
    now apply dep_nth_indep, lt_S_n.
  - simpl dep_nth at 2. rewrite (dep_nth_list_binop _ _ _ _ d1 d5),
                        (dep_nth_list_binop _ _ _ _ d0 d4); auto. simpl.
    apply IHm; now apply lt_S_n.
Qed.

Lemma dep_cons_app_col: forall
    {A m n l} (v: dep_list A l) (m1: dep_list (dep_list A m) l)
    (m2: dep_list (dep_list A n) l),
    dep_list_binop (dep_cons (n := m + n)) v (dep_list_binop dep_app m1 m2) =
    dep_list_binop dep_app (dep_list_binop (dep_cons (n:=m)) v m1) m2.
Proof.
  intros A m n. apply dep_list_ind_3; intros; autorewrite with dep_list. 1: easy.
  simpl dep_app. now rewrite H.
Qed.
