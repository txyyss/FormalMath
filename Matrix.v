(** * Lɪʙʀᴀʀʏ ᴏғ Mᴀᴛʀɪx Tʜᴇᴏʀʏ Bᴀsᴇᴅ ᴏɴ Dᴇᴘᴇɴᴅᴇɴᴛ Tʏᴘᴇs *)
(** * Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

Require Export Coq.Reals.Reals.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Lists.List.
Require Export FormalMath.lib.Coqlib.
Require Export FormalMath.lib.dep_list.
Require Export FormalMath.lib.Reals_ext.
Require Export FormalMath.lib.List_ext.

Import DepListNotations.

(** * Vector *)

Definition Vector (n: nat) := dep_list R n.

Definition vec_zero {n: nat}: Vector n := dep_repeat 0%R n.

Definition vec_add {n} (v1 v2: Vector n): Vector n := dep_list_binop Rplus v1 v2.

Lemma vec_add_assoc: forall {n} (v1 v2 v3: Vector n),
    vec_add (vec_add v1 v2) v3 = vec_add v1 (vec_add v2 v3).
Proof. intros. unfold vec_add. apply dep_list_binop_assoc, Rplus_assoc. Qed.

Lemma vec_add_comm: forall {n} (v1 v2: Vector n), vec_add v1 v2 = vec_add v2 v1.
Proof. intros. unfold vec_add. apply dep_list_binop_comm, Rplus_comm. Qed.

Lemma vec_add_nil: vec_add dep_nil dep_nil = dep_nil.
Proof. unfold vec_add. autorewrite with dep_list. easy. Qed.

Hint Rewrite vec_add_nil: vector.

Lemma vec_add_cons: forall a1 a2 {n} (v1 v2: Vector n),
    vec_add (dep_cons a1 v1) (dep_cons a2 v2) = dep_cons (a1 + a2)%R (vec_add v1 v2).
Proof.
  intros a1 a2. unfold vec_add.
  apply dep_list_ind_2; intros; autorewrite with dep_list; easy.
Qed.

Hint Rewrite @vec_add_cons: vector.

Lemma vec_zero_cons: forall {n}, @vec_zero (S n) = dep_cons 0%R vec_zero.
Proof. intros. unfold vec_zero. now simpl. Qed.

Hint Rewrite @vec_zero_cons: vector.

Lemma vec_zero_app: forall {m n: nat},
    @vec_zero (m + n) = dep_app (@vec_zero m) (@vec_zero n).
Proof. intros. unfold vec_zero. now rewrite dep_repeat_app. Qed.

Lemma vec_neq_zero: forall {n: nat} (v: Vector n),
    v <> vec_zero -> exists i, i < n /\ dep_nth i v 0%R <> 0%R.
Proof.
  intro. induction n; intros; unfold Vector in *; dep_list_decomp.
  - unfold vec_zero in *. simpl in H. exfalso. now apply H.
  - autorewrite with vector in H. destruct (Req_dec v0 0%R).
    + subst. assert (v1 <> vec_zero) by (intro; apply H; now subst).
      destruct (IHn _ H0) as [j [? ?]]. exists (S j). simpl. split; auto.
      now apply lt_n_S.
    + exists O. simpl. split; auto. apply Nat.lt_0_succ.
Qed.

Lemma vec_add_id_r: forall {n} (v: Vector n), vec_add v vec_zero = v.
Proof.
  apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rplus_0_r.
Qed.

Hint Rewrite @vec_add_id_r: vector.

Lemma vec_add_id_l: forall {n} (v: Vector n), vec_add vec_zero v = v.
Proof. intros. rewrite vec_add_comm. apply vec_add_id_r. Qed.

Hint Rewrite @vec_add_id_l: vector.

Definition vec_neg {n} (v: Vector n): Vector n := dep_map Ropp v.

Lemma vec_neg_cons: forall a {n} (v: Vector n),
    vec_neg (dep_cons a v) = dep_cons (- a)%R (vec_neg v).
Proof. intros. unfold vec_neg. now simpl. Qed.

Hint Rewrite @vec_neg_cons: vector.

Lemma vec_neg_zero: forall {n}, vec_neg (@vec_zero n) = vec_zero.
Proof. induction n; intros; autorewrite with vector; [|rewrite IHn, Ropp_0]; easy. Qed.

Hint Rewrite @vec_neg_zero: vector.

Lemma vec_add_inv: forall {n} (v: Vector n), vec_add v (vec_neg v) = vec_zero.
Proof.
  apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rplus_opp_r.
Qed.

Hint Rewrite @vec_add_inv: vector.

Lemma vec_add_neg_zero_iff: forall {n} (u v: Vector n),
    vec_add u (vec_neg v) = vec_zero <-> u = v.
Proof.
  apply dep_list_ind_2; intros; autorewrite with vector. 1: easy.
  split; intros; apply dep_cons_eq_inv in H0; destruct H0.
  - f_equal. 2: now rewrite <- H. apply Rplus_opp_r_uniq, Ropp_eq_compat in H0.
    rewrite !Ropp_involutive in H0. now subst.
  - rewrite <- H in H1. rewrite H1. f_equal. subst. apply Rplus_opp_r.
Qed.

Lemma dep_nth_vec_add: forall i {n} d (v1 v2: Vector n),
    i < n -> dep_nth i (vec_add v1 v2) d = (dep_nth i v1 d + dep_nth i v2 d)%R.
Proof.
  induction i, n; intros; unfold Vector in *; dep_list_decomp;
    autorewrite with vector in *; simpl;
      [inversion H | |inversion H | apply IHi, lt_S_n]; easy.
Qed.

Lemma rev_rel_vec_add: forall {n} {v1 v2 v3 v4: Vector n},
    rev_rel v1 v2 -> rev_rel v3 v4 -> rev_rel (vec_add v1 v3) (vec_add v2 v4).
Proof.
  intros. unfold rev_rel in *. intros.
  rewrite !dep_nth_vec_add; auto; [rewrite H, H0 | apply lt_sub_1_sub_lt]; easy.
Qed.

Definition vec_scal_mul (a: R) {n} (v: Vector n): Vector n := dep_map (Rmult a) v.

Lemma vec_scal_mul_nil: forall a, vec_scal_mul a dep_nil = dep_nil.
Proof. intros. unfold vec_scal_mul. now simpl. Qed.

Hint Rewrite vec_scal_mul_nil: vector.

Lemma vec_scal_mul_cons: forall f a {n} (v: Vector n),
    vec_scal_mul f (dep_cons a v) = dep_cons (f * a)%R (vec_scal_mul f v).
Proof. intros. unfold vec_scal_mul. now simpl. Qed.

Hint Rewrite @vec_scal_mul_cons: vector.

Lemma vec_scal_mul_one: forall {n} (v: Vector n), vec_scal_mul 1 v = v.
Proof.
  apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rmult_1_l.
Qed.

Hint Rewrite @vec_scal_mul_one: vector.

Lemma vec_scal_mul_zero_r: forall {n} a, @vec_scal_mul a n vec_zero = vec_zero.
Proof.
  intros. induction n; autorewrite with vector; [| rewrite IHn, Rmult_0_r]; easy.
Qed.

Hint Rewrite @vec_scal_mul_zero_r: vector.

Lemma vec_scal_mul_zero_l: forall {n} (v: Vector n), vec_scal_mul 0%R v = vec_zero.
Proof.
  apply dep_list_ind_1; intros; autorewrite with vector; [|rewrite H, Rmult_0_l]; easy.
Qed.

Hint Rewrite @vec_scal_mul_zero_l: vector.

Lemma vec_scal_mul_assoc: forall a b {n} (v: Vector n),
    vec_scal_mul a (vec_scal_mul b v) = vec_scal_mul (a * b) v.
Proof.
  intros a b. apply dep_list_ind_1; intros; simpl. 1: easy.
  autorewrite with vector. now rewrite H, Rmult_assoc.
Qed.

Lemma vec_scal_mul_add_distr_l: forall a {n} (u v: Vector n),
    vec_scal_mul a (vec_add u v) = vec_add (vec_scal_mul a u) (vec_scal_mul a v).
Proof.
  intros a. apply dep_list_ind_2. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rmult_plus_distr_l.
Qed.

Lemma vec_scal_mul_add_distr_r: forall a b {n} (v: Vector n),
    vec_scal_mul (a + b) v = vec_add (vec_scal_mul a v) (vec_scal_mul b v).
Proof.
  intros a b. apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rmult_plus_distr_r.
Qed.

Lemma dep_nth_vec_scal_mul: forall i a {n} (v: Vector n) d,
    i < n -> dep_nth i (vec_scal_mul a v) d = (a * dep_nth i v d)%R.
Proof.
  induction i; intros.
  - destruct v; [apply Nat.nlt_0_r in H | autorewrite with vector; simpl]; easy.
  - destruct v. 1: now apply Nat.nlt_0_r in H. apply lt_S_n in H.
    autorewrite with vector. simpl. now apply IHi.
Qed.

Lemma rev_rel_vec_scal_mul: forall a {n} (v1 v2: Vector n),
    rev_rel v1 v2 -> rev_rel (vec_scal_mul a v1) (vec_scal_mul a v2).
Proof.
  intros. unfold rev_rel in *. intros.
  rewrite !dep_nth_vec_scal_mul; auto; [rewrite H | apply lt_sub_1_sub_lt]; easy.
Qed.

Lemma rev_rel_vec_scal_mul': forall a {n} (v1 v2: Vector n),
    a <> 0%R -> rev_rel (vec_scal_mul a v1) (vec_scal_mul a v2) -> rev_rel v1 v2.
Proof.
  intros. apply (rev_rel_vec_scal_mul (/ a)) in H0. rewrite !vec_scal_mul_assoc in H0.
  now rewrite Rinv_l, !vec_scal_mul_one in H0.
Qed.

Lemma rev_rel_vec_scal_mul_iff: forall a {n} (v1 v2: Vector n),
    a <> 0%R -> rev_rel (vec_scal_mul a v1) (vec_scal_mul a v2) <-> rev_rel v1 v2.
Proof.
  intros. split; intros; [apply rev_rel_vec_scal_mul' in H0 |
                          apply rev_rel_vec_scal_mul]; easy.
Qed.

Definition vec_sum {n} (v: Vector n) := dep_fold_left Rplus v 0%R.

Lemma vec_sum_nil: vec_sum dep_nil = 0%R. Proof. vm_compute. easy. Qed.

Hint Rewrite vec_sum_nil: vector.

Lemma vec_sum_cons: forall {n} a (v: Vector n),
    vec_sum (dep_cons a v) = (a + vec_sum v)%R.
Proof.
  intros. unfold vec_sum. simpl. rewrite Rplus_0_l. revert a.
  apply dep_list_ind_1 with (v := v); simpl; intros. 1: now rewrite Rplus_0_r.
  rewrite H, (H (0 + a)%R). ring.
Qed.

Hint Rewrite @vec_sum_cons: vector.

Definition vec_prod {n} (v: Vector n) := dep_fold_left Rmult v 1%R.

Lemma vec_prod_nil: vec_prod dep_nil = 1%R. Proof. vm_compute. easy. Qed.

Hint Rewrite vec_prod_nil: vector.

Lemma vec_prod_cons: forall {n} a (v: Vector n),
    vec_prod (dep_cons a v) = (a * vec_prod v)%R.
Proof.
  intros. unfold vec_prod. simpl. rewrite Rmult_1_l. revert a.
  apply dep_list_ind_1 with (v := v); simpl; intros. 1: now rewrite Rmult_1_r.
  rewrite H, (H (1 * a)%R). ring.
Qed.

Hint Rewrite @vec_prod_cons: vector.

Definition vec_dot_prod {n} (v1 v2: Vector n) := vec_sum (dep_list_binop Rmult v1 v2).

Lemma vec_dot_prod_nil: vec_dot_prod dep_nil dep_nil = 0%R.
Proof. unfold vec_dot_prod. now autorewrite with vector dep_list. Qed.

Hint Rewrite vec_dot_prod_nil: vector.

Lemma vec_dot_prod_cons: forall a b {n} (v1 v2: Vector n),
    vec_dot_prod (dep_cons a v1) (dep_cons b v2) = (a * b + vec_dot_prod v1 v2)%R.
Proof. intros. unfold vec_dot_prod. now autorewrite with vector dep_list. Qed.

Hint Rewrite @vec_dot_prod_cons: vector.

Lemma vec_dot_prod_comm: forall {n} (v1 v2: Vector n),
    vec_dot_prod v1 v2 = vec_dot_prod v2 v1.
Proof.
  apply dep_list_ind_2. 1: easy. intros. autorewrite with vector.
  now rewrite Rmult_comm, H.
Qed.

Lemma vec_dot_prod_add_l: forall {n} (a b c: Vector n),
    vec_dot_prod a (vec_add b c) = (vec_dot_prod a b + vec_dot_prod a c)%R.
Proof.
  apply dep_list_ind_3; intros; autorewrite with vector.
  - now rewrite Rplus_0_r.
  - rewrite H. rewrite Rmult_plus_distr_l, !Rplus_assoc. f_equal.
    rewrite <- !Rplus_assoc. f_equal. apply Rplus_comm.
Qed.

Lemma vec_dot_prod_add_r: forall {n} (a b c: Vector n),
    vec_dot_prod (vec_add a b) c = (vec_dot_prod a c + vec_dot_prod b c)%R.
Proof.
  intros. rewrite vec_dot_prod_comm, vec_dot_prod_add_l, vec_dot_prod_comm. f_equal.
  apply vec_dot_prod_comm.
Qed.

Lemma vec_dot_prod_scal_l: forall a {n} (b c: Vector n),
    vec_dot_prod (vec_scal_mul a b) c = (a * (vec_dot_prod b c))%R.
Proof.
  intros a. apply dep_list_ind_2; intros; autorewrite with vector.
  - now rewrite Rmult_0_r.
  - now rewrite H, Rmult_assoc, Rmult_plus_distr_l.
Qed.

Lemma vec_dot_prod_scal_r: forall a {n} (b c: Vector n),
    vec_dot_prod b (vec_scal_mul a c) = (a * (vec_dot_prod b c))%R.
Proof.
  intros. now rewrite vec_dot_prod_comm, vec_dot_prod_scal_l, vec_dot_prod_comm.
Qed.

Lemma vec_dot_prod_zero_r: forall {n} (v: Vector n), vec_dot_prod v vec_zero = 0%R.
Proof.
  apply dep_list_ind_1; intros; autorewrite with vector. 1: easy.
  now rewrite H, Rmult_0_r, Rplus_0_r.
Qed.

Hint Rewrite @vec_dot_prod_zero_r: vector.

Lemma vec_dot_prod_zero_l: forall {n} (v: Vector n), vec_dot_prod vec_zero v = 0%R.
Proof. intros. rewrite vec_dot_prod_comm. apply vec_dot_prod_zero_r. Qed.

Hint Rewrite @vec_dot_prod_zero_l: vector.

Lemma vec_dot_prod_neg_l: forall {n} (v1 v2: Vector n),
    vec_dot_prod (vec_neg v1) v2 = (- vec_dot_prod v1 v2)%R.
Proof.
  apply dep_list_ind_2; intros; autorewrite with vector. 1: now rewrite Ropp_0.
  now rewrite H, Ropp_plus_distr, Ropp_mult_distr_l.
Qed.

Hint Rewrite @vec_dot_prod_neg_l: vector.

Lemma vec_dot_prod_neg_r: forall {n} (v1 v2: Vector n),
    vec_dot_prod v1 (vec_neg v2) = (- vec_dot_prod v1 v2)%R.
Proof.
  intros. now rewrite vec_dot_prod_comm, vec_dot_prod_neg_l, vec_dot_prod_comm.
Qed.

Hint Rewrite @vec_dot_prod_neg_r: vector.

Lemma vec_dot_prod_nonneg: forall {n} (v: Vector n), (0 <= vec_dot_prod v v)%R.
Proof.
  apply dep_list_ind_1; intros; autorewrite with vector.
  - now apply Req_le.
  - rewrite <- (Rplus_0_l 0%R). apply Rplus_le_compat; auto. apply Rle_0_sqr.
Qed.

Lemma vec_dot_prod_zero: forall {n} (v: Vector n),
    vec_dot_prod v v = 0%R -> v = vec_zero.
Proof.
  intros. revert H.
  apply dep_list_ind_1 with (v := v); intros; autorewrite with vector in *. 1: easy.
  assert (0 <= a * a)%R by (apply Rle_0_sqr). pose proof (vec_dot_prod_nonneg v0).
  pose proof H0. apply Rplus_eq_0_l in H0; auto. rewrite Rplus_comm in H3.
  apply Rplus_eq_0_l, H in H3; auto. rewrite H3. f_equal. now apply Rsqr_eq_0 in H0.
Qed.

Definition vec_eq_dec: forall {n} (v1 v2: Vector n), {v1 = v2} + {v1 <> v2}.
Proof.
  unfold Vector. induction n; intros; dep_list_decomp.
  - now left.
  - destruct (Req_EM_T v0 v2).
    + subst. destruct (IHn v4 v3).
      * subst. now left.
      * right. intro. apply dep_cons_eq_inv in H. apply n0. now destruct H.
    + right. intro. apply dep_cons_eq_inv in H. apply n0. now destruct H.
Defined.

Definition preserve_vec_add {m n} (f: Vector m -> Vector n): Prop :=
  forall u v, f (vec_add u v) = vec_add (f u) (f v).

Definition preserve_vec_scal_mul {m n} (f: Vector m -> Vector n): Prop :=
  forall a v, f (vec_scal_mul a v) = vec_scal_mul a (f v).

Definition linear_map {m n} (f: Vector m -> Vector n): Prop :=
  preserve_vec_add f /\ preserve_vec_scal_mul f.

Definition affine_map {m n} (f: Vector m -> Vector n): Prop :=
  forall l: list (R * Vector m),
    fold_right (fun x => Rplus (fst x)) 0%R l = 1%R ->
    f (fold_right (fun x => vec_add (vec_scal_mul (fst x) (snd x))) vec_zero l) =
    fold_right (fun x => vec_add (vec_scal_mul (fst x) (f (snd x)))) vec_zero l.

Lemma linear_map_is_affine:
  forall {m n} (f: Vector m -> Vector n), linear_map f -> affine_map f.
Proof.
  intros. destruct H. red in H, H0 |- *. intros. clear H1. induction l; simpl.
  - rewrite <- (vec_scal_mul_zero_l vec_zero), H0. now autorewrite with vector.
  - now rewrite H, H0, IHl.
Qed.

Lemma vec_add_is_affine: forall {n} (v: Vector n), affine_map (vec_add v).
Proof.
  intros. red. intros.
  rewrite (fold_right_ext
             (fun x => vec_add (vec_add (vec_scal_mul (fst x) v)
                                        (vec_scal_mul (fst x) (snd x))))
             (fun x => vec_add (vec_scal_mul (fst x) (vec_add v (snd x))))).
  - rewrite fold_right_split.
    + f_equal.
      assert (fold_right (fun x : R * Vector n => vec_add (vec_scal_mul (fst x) v))
                         vec_zero l
              = vec_scal_mul
                  (fold_right (fun x : R * Vector n => Rplus (fst x)) 0%R l) v). {
        clear. induction l; simpl.
        - now autorewrite with vector.
        - now rewrite IHl, vec_scal_mul_add_distr_r. }
      rewrite H0, H. now autorewrite with vector.
    + apply vec_add_id_r.
    + apply vec_add_comm.
    + apply vec_add_assoc.
  - intros. now rewrite vec_scal_mul_add_distr_l.
Qed.

Lemma affine_map_compose:
  forall {m n l} (f: Vector m -> Vector n) (g: Vector n -> Vector l),
    affine_map f -> affine_map g -> affine_map (fun x => g (f x)).
Proof.
  intros. unfold affine_map in *. intros. rewrite H; auto.
  assert (fold_right (fun x => vec_add (vec_scal_mul (fst x) (f (snd x))))
                     vec_zero l0 =
          fold_right (fun x => vec_add (vec_scal_mul (fst x) (snd x)))
                     vec_zero (map (fun x => (fst x, f (snd x))) l0)) by
      (rewrite <- fold_right_map; now simpl).
  rewrite H2, H0; rewrite <- fold_right_map; now simpl.
Qed.

Lemma affine_map_ext: forall {m n} (f g: Vector m -> Vector n),
    (forall x, f x = g x) -> affine_map f -> affine_map g.
Proof.
  intros. unfold affine_map in *. intros. rewrite <- H, H0; auto.
  apply fold_right_ext. intros; now rewrite H.
Qed.

(** * General Matrix Theory *)

Definition Matrix (m n: nat) := dep_list (dep_list R n) m.

Definition mat_add {m n} (m1 m2: Matrix m n): Matrix m n :=
  dep_list_binop vec_add m1 m2.

Lemma mat_add_assoc: forall {m n} (m1 m2 m3: Matrix m n),
    mat_add (mat_add m1 m2) m3 = mat_add m1 (mat_add m2 m3).
Proof. intros. unfold mat_add. apply dep_list_binop_assoc, vec_add_assoc. Qed.

Lemma mat_add_comm: forall {m n} (m1 m2: Matrix m n), mat_add m1 m2 = mat_add m2 m1.
Proof. intros. unfold mat_add. apply dep_list_binop_comm, vec_add_comm. Qed.

Lemma mat_add_nil: forall {n}, mat_add (@dep_nil (Vector n)) dep_nil = dep_nil.
Proof. intros. unfold mat_add. autorewrite with dep_list. easy. Qed.

Hint Rewrite @mat_add_nil: matrix.

Lemma mat_add_cons: forall {m n} (m1 m2: Matrix m n) (v1 v2: Vector n),
    mat_add (dep_cons v1 m1) (dep_cons v2 m2) =
    dep_cons (vec_add v1 v2) (mat_add m1 m2).
Proof. intros. unfold mat_add. now autorewrite with dep_list. Qed.

Hint Rewrite @mat_add_cons: matrix.

Lemma mat_add_col_cons: forall {m n} (m1 m2: Matrix m n) (v1 v2: Vector m),
    mat_add (dep_list_binop (dep_cons (n:= n)) v1 m1)
            (dep_list_binop (dep_cons (n:= n)) v2 m2) =
    dep_list_binop (dep_cons (n:= n)) (vec_add v1 v2) (mat_add m1 m2).
Proof.
  intros m n. revert m. apply dep_list_ind_4; intros;
                          autorewrite with matrix vector dep_list; [|rewrite H]; easy.
Qed.

Hint Rewrite @mat_add_col_cons: matrix.

Lemma mat_add_app: forall {m n l} (m1 m2: Matrix m l) (m3 m4: Matrix n l),
    mat_add (dep_app m1 m3) (dep_app m2 m4) = dep_app (mat_add m1 m2) (mat_add m3 m4).
Proof. intros. unfold mat_add. now rewrite dep_list_binop_app. Qed.

Hint Rewrite @mat_add_app: matrix.

Definition mat_scal_mul {m n} (a: R): Matrix m n -> Matrix m n :=
  dep_map (vec_scal_mul a).

Lemma mat_scal_mul_nil_row:
  forall a {n}, mat_scal_mul a (@dep_nil (Vector n)) = dep_nil.
Proof. intros. unfold mat_scal_mul. now simpl. Qed.

Hint Rewrite @mat_scal_mul_nil_row: matrix.

Lemma mat_scal_mul_nil_col:
  forall a {n} (mat: Matrix n O), mat_scal_mul a mat = dep_repeat dep_nil n.
Proof.
  intros. unfold mat_scal_mul. revert n mat. apply dep_list_ind_1; intros; simpl.
  1: easy. rewrite H. dep_list_decomp. now autorewrite with vector.
Qed.

Hint Rewrite @mat_scal_mul_nil_col: matrix.

Lemma mat_scal_mul_cons: forall a {m n} (mat: Matrix m n) (v: Vector n),
    mat_scal_mul a (dep_cons v mat) = dep_cons (vec_scal_mul a v) (mat_scal_mul a mat).
Proof. intros. unfold mat_scal_mul. now simpl. Qed.

Hint Rewrite @mat_scal_mul_cons: matrix.

Lemma mat_scal_mul_one: forall {m n} (mat: Matrix m n), mat_scal_mul 1 mat = mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  now rewrite H, vec_scal_mul_one.
Qed.

Lemma mat_scal_mul_assoc: forall a b {m n} (mat: Matrix m n),
    mat_scal_mul a (mat_scal_mul b mat) = mat_scal_mul (a * b) mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  now rewrite H, vec_scal_mul_assoc.
Qed.

Lemma mat_scal_mul_add_distr_l: forall a {m n} (u v: Matrix m n),
    mat_scal_mul a (mat_add u v) = mat_add (mat_scal_mul a u) (mat_scal_mul a v).
Proof.
  intros. revert m u v. apply dep_list_ind_2; intros; autorewrite with matrix. 1: easy.
  now rewrite H, vec_scal_mul_add_distr_l.
Qed.

Lemma mat_scal_mul_add_distr_r: forall a b {m n} (mat: Matrix m n),
    mat_scal_mul (a + b) mat = mat_add (mat_scal_mul a mat) (mat_scal_mul b mat).
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  now rewrite H, vec_scal_mul_add_distr_r.
Qed.

Definition mat_transpose {m n}: Matrix m n -> Matrix n m := dep_list_transpose.

Lemma mat_transpose_involutive: forall {m n} (mat: Matrix m n),
    mat_transpose (mat_transpose mat) = mat.
Proof. intros. apply dep_list_transpose_involutive. Qed.

Hint Rewrite @mat_transpose_involutive: matrix.

Lemma mat_transpose_cons_row: forall {m n} (v: Vector n) (mat: Matrix m n),
    mat_transpose (dep_cons v mat) =
    dep_list_binop (dep_cons (n:=m)) v (mat_transpose mat).
Proof. intros. unfold mat_transpose. now simpl. Qed.

Hint Rewrite @mat_transpose_cons_row: matrix.

Lemma mat_transpose_cons_col: forall {m n} (v: Vector m) (mat: Matrix m n),
    mat_transpose (dep_list_binop (dep_cons (n := n)) v mat) =
    dep_cons v (mat_transpose mat).
Proof. intros. unfold mat_transpose. now rewrite dep_transpose_cons_col. Qed.

Hint Rewrite @mat_transpose_cons_col: matrix.

Lemma mat_transpose_nil_1: forall {n},
    mat_transpose (@dep_nil (Vector n)) = dep_repeat dep_nil n.
Proof. intros. unfold mat_transpose. now simpl. Qed.

Hint Rewrite @mat_transpose_nil_1: matrix.

Lemma mat_transpose_nil_2: forall {n} (mat: Matrix n O), mat_transpose mat = dep_nil.
Proof.
  apply dep_list_ind_1. 1: easy. intros. unfold mat_transpose in *.
  dep_list_decomp. simpl. rewrite H. easy.
Qed.

Hint Rewrite @mat_transpose_nil_2: matrix.

Lemma mat_transpose_add: forall {m n} (m1 m2: Matrix m n),
    mat_transpose (mat_add m1 m2) = mat_add (mat_transpose m1) (mat_transpose m2).
Proof.
  intros. revert m m1 m2. apply dep_list_ind_2; intros; autorewrite with matrix.
  - induction n; simpl; autorewrite with matrix vector; [easy | now rewrite <- IHn].
  - rewrite H. clear H. generalize (mat_transpose v1) as m1.
    generalize (mat_transpose v2) as m2. intros. clear v1 v2. revert a b.
    apply dep_list_ind_2 with (v1 := m1) (v2 := m2); intros; autorewrite with matrix;
      dep_list_decomp. 1: now autorewrite with dep_list.
    autorewrite with vector dep_list matrix. now rewrite H.
Qed.

Lemma mat_transpose_scal_mul: forall a {m n} (mat: Matrix m n),
    mat_transpose (mat_scal_mul a mat) = mat_scal_mul a (mat_transpose mat).
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  rewrite H. generalize (mat_transpose v). intros. clear. revert a0.
  apply dep_list_ind_1 with (v := m); intros; dep_list_decomp;
    autorewrite with matrix vector dep_list; [|rewrite H]; easy.
Qed.

Definition mat_neg {m n}: Matrix m n -> Matrix m n := dep_map vec_neg.

Definition mat_mul {m l n} (m1: Matrix m l) (m2: Matrix l n): Matrix m n :=
  dep_map (fun row => dep_map (vec_dot_prod row) (mat_transpose m2)) m1.

Lemma mat_mul_nil: forall {m n} (mat: Matrix m n), mat_mul dep_nil mat = dep_nil.
Proof. intros. unfold mat_mul. now simpl. Qed.

Hint Rewrite @mat_mul_nil: matrix.

Lemma mat_mul_cons: forall {m l n} (v: Vector l) (m1: Matrix m l) (m2: Matrix l n),
    mat_mul (dep_cons v m1) m2 =
    dep_cons (dep_map (vec_dot_prod v) (mat_transpose m2)) (mat_mul m1 m2).
Proof. intros. unfold mat_mul. now simpl. Qed.

Hint Rewrite @mat_mul_cons: matrix.

Definition zero_mat {m n}: Matrix m n := dep_repeat vec_zero m.

Lemma zero_mat_cons: forall {m n}, @zero_mat (S m) n = dep_cons vec_zero zero_mat.
Proof. intros; unfold zero_mat. now simpl. Qed.

Hint Rewrite @zero_mat_cons: matrix.

Lemma mat_mul_nil': forall {m n} (mat: Matrix m 0),
    mat_mul mat (@dep_nil (Vector n)) = zero_mat.
Proof.
  induction m; intros; unfold Matrix in *; dep_list_decomp;
    autorewrite with matrix vector dep_list;
    [unfold zero_mat; simpl | rewrite IHm]; easy.
Qed.

Hint Rewrite @mat_mul_nil': matrix.

Lemma zero_mat_col_cons: forall {m n},
    dep_list_binop (dep_cons (n:=n)) vec_zero (@zero_mat m n) = zero_mat.
Proof.
  induction m; intros.
  - unfold zero_mat, vec_zero. now simpl.
  - rewrite !zero_mat_cons, vec_zero_cons. autorewrite with dep_list. now rewrite IHm.
Qed.

Hint Rewrite @zero_mat_col_cons: matrix.

Lemma mat_mul_app: forall {k l m n} (m1: Matrix k l) (m2: Matrix m l) (m3: Matrix l n),
    mat_mul (dep_app m1 m2) m3 = dep_app (mat_mul m1 m3) (mat_mul m2 m3).
Proof.
  intro. induction k; intros; unfold Matrix in *; dep_list_decomp.
  - now simpl.
  - simpl dep_app at 1. autorewrite with matrix. simpl. autorewrite with matrix.
    f_equal. apply IHk.
Qed.

Hint Rewrite @mat_mul_app: matrix.

Lemma mat_mul_add_distr_l: forall {m l n} (m1: Matrix m l) (m2 m3: Matrix l n),
    mat_mul m1 (mat_add m2 m3) = mat_add (mat_mul m1 m2) (mat_mul m1 m3).
Proof.
  intros. revert m m1. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  autorewrite with matrix. rewrite H. f_equal. clear H. rewrite mat_transpose_add.
  clear v n0. generalize (mat_transpose m2) as m1. clear m2.
  generalize (mat_transpose m3) as m2. clear m3. intros. revert n m1 m2.
  apply dep_list_ind_2; intros; autorewrite with matrix. 1: easy. simpl. rewrite H.
  autorewrite with vector. f_equal. apply vec_dot_prod_add_l.
Qed.

Lemma mat_mul_add_distr_r: forall {m l n} (m1 m2: Matrix m l) (m3: Matrix l n),
    mat_mul (mat_add m1 m2) m3 = mat_add (mat_mul m1 m3) (mat_mul m2 m3).
Proof.
  intros. revert m m1 m2. apply dep_list_ind_2; intros; autorewrite with matrix.
  1: easy. rewrite H. f_equal. generalize (mat_transpose m3) as mat. intros.
  clear -a b mat. revert n mat.
  apply dep_list_ind_1; intros; simpl; autorewrite with vector. 1: easy.
  rewrite H. f_equal. apply vec_dot_prod_add_r.
Qed.

Lemma mat_transpose_mul: forall {m l n} (m1: Matrix m l) (m2: Matrix l n),
    mat_transpose (mat_mul m1 m2) = mat_mul (mat_transpose m2) (mat_transpose m1).
Proof.
  intros. revert m m1. apply dep_list_ind_1; intros; autorewrite with matrix.
  - generalize (mat_transpose m2) as m. clear m2. revert n.
    apply dep_list_ind_1; intros; simpl. 1: easy. autorewrite with matrix.
    rewrite H. easy.
  - rewrite H. clear H. generalize (mat_transpose m2) as m1. clear m2.
    generalize (mat_transpose v) as m2. clear v. intros. rename n0 into m.
    revert a. apply dep_list_ind_1 with (v := m1); intros; simpl. 1: easy.
    autorewrite with matrix dep_list. rewrite H. f_equal. clear H. simpl. f_equal.
    apply vec_dot_prod_comm.
Qed.

Lemma mat_mul_assoc: forall
    {m k l n} (m1: Matrix m k) (m2: Matrix k l) (m3: Matrix l n),
    mat_mul (mat_mul m1 m2) m3 = mat_mul m1 (mat_mul m2 m3).
Proof.
  intros. revert m m1. apply dep_list_ind_1. 1: easy. intros. autorewrite with matrix.
  rewrite H. f_equal. clear. rewrite mat_transpose_mul.
  generalize (mat_transpose m2) as m1. clear m2. generalize (mat_transpose m3) as m2.
  intros. clear m3. revert n m2. apply dep_list_ind_1. 1: easy. intros.
  autorewrite with matrix. simpl. rewrite H. f_equal. clear. revert a0.
  apply dep_list_ind_1 with (v := m1); intros; dep_list_decomp; simpl;
    autorewrite with vector matrix dep_list. 1: easy.
  generalize (@dep_map (Vector 0) R (vec_dot_prod dep_nil) k (@zero_mat k 0)).
  rewrite H. clear H. generalize (mat_transpose v) as m. intros. clear. revert a a0.
  apply dep_list_ind_1 with (v := m); intros; dep_list_decomp.
  - simpl. autorewrite with vector dep_list. now rewrite Rmult_0_l, Rplus_0_l.
  - autorewrite with vector dep_list. simpl. autorewrite with vector.
    rewrite <- H. clear H. rewrite <- !Rplus_assoc. f_equal.
    rewrite Rmult_plus_distr_r, Rmult_plus_distr_l, (Rmult_comm a2 a4),
    <- Rmult_assoc, !Rplus_assoc. f_equal. apply Rplus_comm.
Qed.

Lemma mat_mul_scal_l: forall a {m l n} (m1: Matrix m l) (m2: Matrix l n),
    mat_scal_mul a (mat_mul m1 m2) = mat_mul (mat_scal_mul a m1) m2.
Proof.
  intros. revert m m1. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  rewrite H. f_equal. generalize (mat_transpose m2). intros. clear.
  revert n m. apply dep_list_ind_1; intros; simpl; autorewrite with vector. 1: easy.
  now rewrite H, vec_dot_prod_scal_l.
Qed.

Lemma mat_mul_scal_r: forall a {m l n} (m1: Matrix m l) (m2: Matrix l n),
    mat_scal_mul a (mat_mul m1 m2) = mat_mul m1 (mat_scal_mul a m2).
Proof.
  intros. revert m m1. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  rewrite H, mat_transpose_scal_mul. f_equal. generalize (mat_transpose m2). intros.
  clear. revert n m. apply dep_list_ind_1; intros; simpl; autorewrite with vector.
  1: easy. now rewrite H, vec_dot_prod_scal_r.
Qed.

Definition mat_vec_mul {m n} (mat: Matrix m n) (v: Vector n): Vector m :=
  dep_map (vec_dot_prod v) mat.

Definition vec_to_col_mat {n} (v: Vector n): Matrix n 1 :=
  dep_list_transpose (dep_cons v dep_nil).

Definition col_mat_to_vec {n} (mat: Matrix n 1): Vector n :=
  dep_hd (dep_list_transpose mat).

Lemma vec_to_col_to_vec: forall {n} (v: Vector n),
    col_mat_to_vec (vec_to_col_mat v) = v.
Proof.
  intros. unfold col_mat_to_vec, vec_to_col_mat.
  rewrite dep_list_transpose_involutive. now simpl.
Qed.

Hint Rewrite @vec_to_col_to_vec: matrix.

Lemma col_to_mat_to_col: forall {n} (mat: Matrix n 1),
    vec_to_col_mat (col_mat_to_vec mat) = mat.
Proof.
  intros. unfold col_mat_to_vec, vec_to_col_mat.
  rewrite <- (dep_list_transpose_involutive mat) at 2.
  generalize (dep_list_transpose mat). intros. clear. dep_list_decomp. now simpl.
Qed.

Hint Rewrite @col_to_mat_to_col: matrix.

Lemma mat_vec_mul_as_mat: forall {m n} (mat: Matrix m n) (v: Vector n),
    mat_vec_mul mat v = col_mat_to_vec (mat_mul mat (vec_to_col_mat v)).
Proof.
  intros. unfold mat_vec_mul, col_mat_to_vec, mat_mul, vec_to_col_mat.
  rewrite mat_transpose_involutive, dep_hd_transpose, dep_map_nest. simpl.
  revert m mat. apply dep_list_ind_1; intros; simpl;
                  [|rewrite H, vec_dot_prod_comm]; easy.
Qed.

Lemma mat_vec_mul_assoc:
  forall {m l n} (m1: Matrix m l) (m2: Matrix l n) (v: Vector n),
    mat_vec_mul m1 (mat_vec_mul m2 v) = mat_vec_mul (mat_mul m1 m2) v.
Proof.
  intros. rewrite !mat_vec_mul_as_mat. autorewrite with matrix.
  now rewrite mat_mul_assoc.
Qed.

Lemma vec_to_col_mat_cons: forall a {n} (v: Vector n),
    vec_to_col_mat (dep_cons a v) = dep_cons (dep_cons a dep_nil) (vec_to_col_mat v).
Proof. intros. unfold vec_to_col_mat. simpl. now autorewrite with dep_list. Qed.

Hint Rewrite @vec_to_col_mat_cons: matrix.

Lemma col_mat_to_vec_cons: forall a {n} (mat: Matrix n 1),
    col_mat_to_vec (dep_cons (dep_cons a dep_nil) mat) =
    dep_cons a (col_mat_to_vec mat).
Proof.
  intros. rewrite <- (vec_to_col_to_vec (dep_cons a (col_mat_to_vec mat))). f_equal.
  now autorewrite with matrix.
Qed.

Hint Rewrite @col_mat_to_vec_cons: matrix.

Lemma vec_add_as_mat: forall {n} (v1 v2: Vector n),
    vec_add v1 v2 = col_mat_to_vec (mat_add (vec_to_col_mat v1) (vec_to_col_mat v2)).
Proof.
  apply dep_list_ind_2; intros; simpl; autorewrite with vector. 1: easy.
  rewrite H. now autorewrite with matrix vector.
Qed.

Lemma vec_scal_mul_as_mat: forall a {n} (v: Vector n),
    vec_scal_mul a v = col_mat_to_vec (mat_scal_mul a (vec_to_col_mat v)).
Proof.
  intros. revert n v.
  apply dep_list_ind_1; intros; autorewrite with matrix vector; [|rewrite H]; easy.
Qed.

Lemma mat_vec_mul_add_r: forall {m n: nat} (mat: Matrix m n) (u v: Vector n),
    mat_vec_mul mat (vec_add u v) = vec_add (mat_vec_mul mat u) (mat_vec_mul mat v).
Proof.
  intros. rewrite !vec_add_as_mat, !mat_vec_mul_as_mat. autorewrite with matrix.
  now rewrite mat_mul_add_distr_l.
Qed.

Lemma mat_vec_mul_add_l: forall {m n: nat} (m1 m2: Matrix m n) (v: Vector n),
    mat_vec_mul (mat_add m1 m2) v = vec_add (mat_vec_mul m1 v) (mat_vec_mul m2 v).
Proof.
  intros. rewrite !vec_add_as_mat, !mat_vec_mul_as_mat. autorewrite with matrix.
  now rewrite mat_mul_add_distr_r.
Qed.

Lemma mat_vec_mul_vec_scal_mul:
  forall {m n: nat} (mat: Matrix m n) (a: R) (v: Vector n),
    mat_vec_mul mat (vec_scal_mul a v) = vec_scal_mul a (mat_vec_mul mat v).
Proof.
  intros. rewrite !vec_scal_mul_as_mat, !mat_vec_mul_as_mat. autorewrite with matrix.
  now rewrite mat_mul_scal_r.
Qed.

Lemma mat_vec_mul_linear_map:
  forall {m n} (mat: Matrix m n), linear_map (mat_vec_mul mat).
Proof.
  intros. red. split; red; intros.
  - apply mat_vec_mul_add_r.
  - apply mat_vec_mul_vec_scal_mul.
Qed.

Fixpoint identity_mat {n: nat}: Matrix n n :=
  match n with
  | O => dep_nil
  | S m => dep_cons (dep_cons 1%R vec_zero)
                    (dep_list_binop (dep_cons (n := m)) vec_zero identity_mat)
  end.

Lemma identity_mat_transpose: forall {n},
    mat_transpose (@identity_mat n) = identity_mat.
Proof.
  induction n; intros; simpl; autorewrite with matrix dep_list; [|rewrite IHn]; easy.
Qed.

Hint Rewrite @identity_mat_transpose: matrix.

Lemma dep_map_dot_prod_cons:
  forall {m n} (mat: Matrix m n) (v1: Vector n) (v2: Vector m) (a: R),
    dep_map (vec_dot_prod (dep_cons a v1)) (dep_list_binop (dep_cons (n:=n)) v2 mat) =
    vec_add (vec_scal_mul a v2) (dep_map (vec_dot_prod v1) mat).
Proof.
  intros. revert m mat v2.
  apply dep_list_ind_2; intros; autorewrite with vector dep_list. 1: easy.
  unfold Vector in *. now rewrite H.
Qed.

Lemma mat_mul_identity_r:
  forall {m n} (mat: Matrix m n), mat_mul mat identity_mat = mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; simpl; autorewrite with matrix.
  1: easy. rewrite H. f_equal. clear. revert n a. apply dep_list_ind_1; intros; simpl.
  1: easy. autorewrite with vector. rewrite Rplus_0_r, Rmult_1_r. f_equal.
  rewrite dep_map_dot_prod_cons, H. now autorewrite with vector.
Qed.

Hint Rewrite @mat_mul_identity_r: matrix.

Definition mat_span {m n} (v1: Vector m) (v2: Vector n): Matrix m n :=
  dep_map (fun x => vec_scal_mul x v2) v1.

Lemma mat_span_cons: forall a {m n} (v1: Vector m) (v2: Vector n),
    mat_span (dep_cons a v1) v2 = dep_cons (vec_scal_mul a v2) (mat_span v1 v2).
Proof. intros. unfold mat_span. now simpl. Qed.

Hint Rewrite @mat_span_cons: matrix.

Lemma mat_mul_col_cons:
  forall {m l n} (m1: Matrix m l) (m2: Matrix l n) (v1: Vector m) (v2: Vector n),
    mat_mul (dep_list_binop (dep_cons (n:=l)) v1 m1) (dep_cons v2 m2) =
    mat_add (mat_span v1 v2) (mat_mul m1 m2).
Proof.
  intros. revert m v1 m1.
  apply dep_list_ind_2; intros; autorewrite with matrix dep_list. 1: easy.
  now rewrite H, dep_map_dot_prod_cons.
Qed.

Hint Rewrite @mat_mul_col_cons: matrix.

Lemma mat_add_zero_r: forall {m n} (mat: Matrix m n), mat_add mat zero_mat = mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  rewrite H. now autorewrite with vector.
Qed.

Hint Rewrite @mat_add_zero_r: matrix.

Lemma mat_add_zero_l: forall {m n} (mat: Matrix m n), mat_add zero_mat mat = mat.
Proof. intros. rewrite mat_add_comm. apply mat_add_zero_r. Qed.

Hint Rewrite @mat_add_zero_l: matrix.

Lemma mat_span_zero_r: forall {m n} (v: Vector m), mat_span v (@vec_zero n) = zero_mat.
Proof.
  intros. revert m v. apply dep_list_ind_1; intros; simpl. 1: easy.
  autorewrite with matrix vector. now rewrite H.
Qed.

Hint Rewrite @mat_span_zero_r: matrix.

Lemma mat_span_col_cons: forall a {m n} (v1: Vector m) (v2: Vector n),
    mat_span v1 (dep_cons a v2) =
    dep_list_binop (dep_cons (n := n)) (vec_scal_mul a v1) (mat_span v1 v2).
Proof.
  intros. revert m v1. apply dep_list_ind_1; intros; autorewrite with matrix vector.
  1: easy. rewrite H. autorewrite with dep_list. now rewrite Rmult_comm.
Qed.

Hint Rewrite @mat_span_col_cons: matrix.

Lemma mat_span_zero_l: forall {m n} (v: Vector n), mat_span (@vec_zero m) v = zero_mat.
Proof.
  intros. revert n v. apply dep_list_ind_1; intros; simpl; autorewrite with matrix.
  1: easy. rewrite H. now autorewrite with matrix vector.
Qed.

Hint Rewrite @mat_span_zero_l: matrix.

Lemma mat_mul_identity_l:
  forall {m n} (mat: Matrix m n), mat_mul identity_mat mat = mat.
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; simpl; autorewrite with matrix.
  1: easy. rewrite dep_map_dot_prod_cons, vec_scal_mul_one. f_equal.
  - rewrite <- (vec_add_id_r a) at 2. f_equal. generalize (mat_transpose v). clear.
    revert n. apply dep_list_ind_1; intros; simpl. 1: easy. rewrite H.
    now autorewrite with vector.
  - now rewrite H.
Qed.

Hint Rewrite @mat_mul_identity_l: matrix.

Lemma mat_vec_mul_identity: forall {n} (v: Vector n), mat_vec_mul identity_mat v = v.
Proof. intros. rewrite mat_vec_mul_as_mat. now autorewrite with matrix. Qed.

Hint Rewrite @mat_vec_mul_identity: matrix.

Lemma mat_vec_mul_col_cons:
  forall {m n} (mat: Matrix m n) (v: Vector n) (sv: Vector m) a,
    mat_vec_mul (dep_list_binop (dep_cons (n:=n)) sv mat) (dep_cons a v) =
    vec_add (vec_scal_mul a sv) (mat_vec_mul mat v).
Proof.
  intros. rewrite !mat_vec_mul_as_mat, vec_add_as_mat. now autorewrite with matrix.
Qed.

Hint Rewrite @mat_vec_mul_col_cons: matrix.

Lemma mat_vec_mul_cons: forall {m n} (mat: Matrix m n) (v1 v2: Vector n),
    mat_vec_mul (dep_cons v1 mat) v2 =
    dep_cons (vec_dot_prod v1 v2) (mat_vec_mul mat v2).
Proof. intros. unfold mat_vec_mul. simpl. now rewrite vec_dot_prod_comm. Qed.

Hint Rewrite @mat_vec_mul_cons: matrix.

Lemma mat_vec_mul_nil: forall {n}, mat_vec_mul (dep_repeat dep_nil n) dep_nil =
                                    vec_zero.
Proof.
  induction n; simpl; autorewrite with matrix. 1: easy.
  autorewrite with matrix vector. now f_equal.
Qed.

Hint Rewrite @mat_vec_mul_nil: matrix.

Lemma mat_vec_mul_zero: forall {m n} (mat: Matrix m n),
    mat_vec_mul mat vec_zero = vec_zero.
Proof.
  induction m; intros; unfold Matrix in *; dep_list_decomp; autorewrite with matrix.
  1: easy. autorewrite with vector. now rewrite IHm.
Qed.

Hint Rewrite @mat_vec_mul_zero: matrix.

Lemma mat_mul_col_cons_2:
  forall {m l n} (m1: Matrix m l) (m2: Matrix l n) (v: Vector l),
    mat_mul m1 (dep_list_binop (dep_cons (n:=n)) v m2) =
    dep_list_binop (dep_cons (n:=n)) (mat_vec_mul m1 v) (mat_mul m1 m2).
Proof.
  intros. revert l m1 m2 v.
  induction l; intros; unfold Matrix, Vector in *; dep_list_decomp;
    autorewrite with matrix vector dep_list; auto.
  destruct (dep_vertical_split m1) as [v [m2 ?]]. subst.
  autorewrite with matrix. rewrite IHl. now autorewrite with matrix.
Qed.

Lemma linear_map_mat: forall {m n} (f: Vector m -> Vector n),
    linear_map f -> forall {l} (mat: Matrix l m) (v: Vector l),
      f (mat_vec_mul (mat_transpose mat) v) =
      mat_vec_mul (mat_transpose (dep_map f mat)) v.
Proof.
  intros. revert l mat v.
  apply dep_list_ind_2; intros; autorewrite with matrix; destruct H as [Ha Hs];
    red in Ha, Hs.
  - rewrite <- (vec_scal_mul_zero_r 0%R) at 1. rewrite Hs. now autorewrite with vector.
  - simpl. autorewrite with matrix. rewrite Ha, Hs. now f_equal.
Qed.

Lemma mat_mul_as_vec_mul: forall {m l n} (m1: Matrix m l) (m2: Matrix l n),
    mat_mul m1 m2 = mat_transpose (dep_map (mat_vec_mul m1) (mat_transpose m2)).
Proof.
  intros. revert m m1. apply dep_list_ind_1; intros; autorewrite with matrix. 1: easy.
  rewrite H. generalize (mat_transpose m2) as mat. clear. revert n.
  apply dep_list_ind_1; intros; autorewrite with matrix; simpl. 1: easy.
  autorewrite with matrix. rewrite <- H. now autorewrite with dep_list.
Qed.

Lemma mat_vec_mul_unique: forall {m n} (m1 m2: Matrix m n),
    (forall v, mat_vec_mul m1 v = mat_vec_mul m2 v) -> m1 = m2.
Proof.
  intros. cut (forall l (m3: Matrix n l), mat_mul m1 m3 = mat_mul m2 m3).
  - intros. rewrite <- mat_mul_identity_r, <- (mat_mul_identity_r m1). apply H0.
  - intros. rewrite !mat_mul_as_vec_mul. f_equal. generalize (mat_transpose m3) as m4.
    clear m3. revert l. apply dep_list_ind_1; intros; simpl; [| rewrite H, H0]; easy.
Qed.

Lemma linear_map_mat_sig: forall {n m} (f: Vector n -> Vector m),
    linear_map f -> {mat: Matrix m n |
                      unique (fun m => forall v, f v = mat_vec_mul m v) mat}.
Proof.
  intros. exists (mat_transpose (dep_map f identity_mat)).
  assert (forall v, f v = mat_vec_mul (mat_transpose (dep_map f identity_mat)) v) by
      (intro; rewrite <- linear_map_mat; auto; now autorewrite with matrix).
  split; auto. intros m2 ?. apply mat_vec_mul_unique. intros.
  now rewrite <- H0, <- H1.
Qed.

Lemma linear_map_mat_iff: forall {n m} (f: Vector n -> Vector m),
    linear_map f <->
    exists ! mat: Matrix m n, forall v, f v = mat_vec_mul mat v.
Proof.
  intros. split; intros.
  - apply linear_map_mat_sig in H. destruct H as [mat ?]. now exists mat.
  - destruct H as [mat [? ?]]. destruct (mat_vec_mul_linear_map mat). red in H1, H2.
    split; red; intros; rewrite !H; easy.
Qed.

Lemma mat_vec_mul_neg: forall {m n} (mat: Matrix m n) (v: Vector n),
    mat_vec_mul mat (vec_neg v) = vec_neg (mat_vec_mul mat v).
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros. 1: easy.
  autorewrite with matrix vector. now rewrite H.
Qed.

Hint Rewrite @mat_vec_mul_neg: matrix.

Definition preserve_dot_prod {m n} (f: Vector m -> Vector n): Prop :=
  forall u v, vec_dot_prod (f u) (f v) = vec_dot_prod u v.

Lemma preserve_dot_prod_linear: forall {m n} (f: Vector m -> Vector n),
    preserve_dot_prod f -> linear_map f.
Proof.
  intros m n f. red. unfold preserve_dot_prod.
  intros; split; red; intros; rewrite <- vec_add_neg_zero_iff; apply vec_dot_prod_zero;
    rewrite vec_dot_prod_add_l, !vec_dot_prod_add_r, !vec_dot_prod_neg_l,
    !vec_dot_prod_neg_r.
  - rewrite !vec_dot_prod_add_l, !vec_dot_prod_add_r, !H, !vec_dot_prod_add_l,
    !vec_dot_prod_add_r. ring.
  - rewrite !vec_dot_prod_scal_l, !vec_dot_prod_scal_r, !H, !vec_dot_prod_scal_l,
    !vec_dot_prod_scal_r. ring.
Qed.

Lemma vec_dot_prod_nest: forall {m n} (v1: Vector m) (v2: Vector n) (mat: Matrix m n),
    vec_dot_prod v1 (dep_map (vec_dot_prod v2) mat) =
    vec_dot_prod v2 (dep_map (vec_dot_prod v1) (mat_transpose mat)).
Proof.
  intros. revert m mat v1.
  apply dep_list_ind_2; intros; autorewrite with matrix vector dep_list. 1: easy.
  unfold Vector in *.
  now rewrite H, dep_map_dot_prod_cons, vec_dot_prod_add_l, vec_dot_prod_scal_r.
Qed.

Lemma vec_dot_prod_mul: forall {m l n} (m1: Matrix l m) (m2: Matrix l n) v1 v2,
    vec_dot_prod (mat_vec_mul m1 v1) (mat_vec_mul m2 v2) =
    vec_dot_prod (mat_vec_mul (mat_mul (mat_transpose m2) m1) v1) v2.
Proof.
  intros. unfold mat_vec_mul at 2. rewrite vec_dot_prod_nest, (vec_dot_prod_comm v2).
  f_equal. rewrite <- mat_vec_mul_assoc. now unfold mat_vec_mul at 2.
Qed.

Lemma mat_vec_mul_preserve_dot_prod: forall {m n} (mat: Matrix m n),
    mat_mul (mat_transpose mat) mat = identity_mat ->
    preserve_dot_prod (mat_vec_mul mat).
Proof.
  intros. red. intros. rewrite vec_dot_prod_mul. rewrite H.
  now autorewrite with matrix.
Qed.

Lemma vec_dot_prod_unique: forall {n} (v1 v2: Vector n),
    (forall u, vec_dot_prod v1 u = vec_dot_prod v2 u) -> v1 = v2.
Proof.
  intros. revert H. apply dep_list_ind_2 with (v3 := v1) (v2 := v2); intros. 1: easy.
  f_equal.
  - specialize (H0 (dep_cons 1%R vec_zero)). autorewrite with vector in H0.
    now rewrite !Rplus_0_r, !Rmult_1_r in H0.
  - apply H. intros. specialize (H0 (dep_cons 0%R u)). autorewrite with vector in H0.
    now rewrite !Rmult_0_r, !Rplus_0_l in H0.
Qed.

Lemma preserve_dot_prod_mat_sig: forall {m n} (f: Vector n -> Vector m),
    preserve_dot_prod f ->
    {mat: Matrix m n |
     unique (fun m => mat_mul (mat_transpose m) m = identity_mat /\
                      forall v, f v = mat_vec_mul m v) mat}.
Proof.
  intros. pose proof H. apply preserve_dot_prod_linear in H0.
  apply linear_map_mat_sig in H0. destruct H0 as [mat [? ?]]. exists mat.
  split; [split|]; auto.
  - red in H.
    assert (forall u v,
               vec_dot_prod (mat_vec_mul (mat_mul (mat_transpose mat) mat) u) v =
               vec_dot_prod u v) by
        (intros; now rewrite <- vec_dot_prod_mul, <- !H0).
    apply mat_vec_mul_unique. intros u. autorewrite with matrix.
    now apply vec_dot_prod_unique.
  - intros. destruct H2. now apply H1.
Qed.

Lemma preserve_dot_prod_mat: forall {m n} (f: Vector n -> Vector m),
    preserve_dot_prod f <->
    exists ! mat: Matrix m n,
      mat_mul (mat_transpose mat) mat = identity_mat /\
      forall v, f v = mat_vec_mul mat v.
Proof.
  intros. split; intros.
  - apply preserve_dot_prod_mat_sig in H. destruct H as [mat ?]. now exists mat.
  - destruct H as [mat [[? ?] ?]]. pose proof (mat_vec_mul_preserve_dot_prod _ H).
    red in H2 |-* . intros. now rewrite !H0.
Qed.

(** * Square Matrix Theory *)

Lemma mat_left_right_inverse_eq: forall {n} (A B C: Matrix n n),
    mat_mul B A = identity_mat -> mat_mul A C = identity_mat -> B = C.
Proof.
  intros. pose proof (mat_mul_assoc B A C). rewrite H, H0 in H1.
  now autorewrite with matrix in H1.
Qed.

Fixpoint alter_sign_helper {n} (r: R) (v: Vector n): Vector n :=
  match v with
  | dep_nil => dep_nil
  | dep_cons h l => dep_cons (r * h)%R (alter_sign_helper (- r)%R l)
  end.

Lemma alter_sign_helper_opp: forall {n} (r: R) (v: Vector n),
    alter_sign_helper (- r) v = vec_scal_mul (- 1)%R (alter_sign_helper r v).
Proof.
  intros. revert n v. apply dep_list_ind_1; intros; simpl. 1: easy.
  autorewrite with vector. rewrite Ropp_involutive, H, vec_scal_mul_assoc.
  replace (-1 * -1)%R with 1%R by ring. rewrite vec_scal_mul_one. f_equal. ring.
Qed.

Definition alter_sign {n} (v: Vector n): Vector n := alter_sign_helper 1%R v.

Lemma alter_sign_cons: forall {n} (a: R) (v: Vector n),
    alter_sign (dep_cons a v) = dep_cons a (vec_scal_mul (-1)%R (alter_sign v)).
Proof.
  intros. unfold alter_sign. simpl. now rewrite alter_sign_helper_opp, Rmult_1_l.
Qed.

Hint Rewrite @alter_sign_cons: vector.

Lemma alter_sign_helper_zero: forall {n} r,
    alter_sign_helper r (@vec_zero n) = vec_zero.
Proof.
  intros. induction n. 1: easy. simpl. rewrite alter_sign_helper_opp.
  unfold vec_zero in *. rewrite IHn. autorewrite with vector. now rewrite Rmult_0_r.
Qed.

Lemma alter_sign_zero: forall {n}, alter_sign (@vec_zero n) = vec_zero.
Proof. intros. unfold alter_sign. apply alter_sign_helper_zero. Qed.

Hint Rewrite @alter_sign_zero: vector.

Lemma alter_sign_scal_mul: forall {n} (a: R) (v: Vector n),
    alter_sign (vec_scal_mul a v) = vec_scal_mul a (alter_sign v).
Proof.
  intros. revert n v. apply dep_list_ind_1; intros; autorewrite with vector. 1: easy.
  rewrite H, !vec_scal_mul_assoc. do 2 f_equal. ring.
Qed.

Lemma alter_sign_vec_add: forall {n} (v1 v2: Vector n),
    alter_sign (vec_add v1 v2) = vec_add (alter_sign v1) (alter_sign v2).
Proof.
  intros. revert n v1 v2. apply dep_list_ind_2; intros; autorewrite with vector.
  1: easy. rewrite H, vec_scal_mul_add_distr_l. easy.
Qed.

(** * Determinant of Square Matrix *)

Fixpoint det {n} (mat: Matrix n n): R :=
  match n as x return (x = n -> R) with
  | O => fun _ => 1%R
  | S m =>
    fun h1 => match mat in (dep_list _ s) return (s = n -> R) with
              | dep_nil =>
                fun h2 => False_rect _ (eq_ind (S m) _ (fun h3 => (O_S m h3)) _ h1 h2)
              | @dep_cons _ n0 h l =>
                fun h2 =>
                  vec_dot_prod
                    (alter_sign h)
                    (eq_rec (S m) _
                            (fun h3 l0 =>
                               eq_rec_r
                                 (fun n1 => Matrix n1 (S m) -> Vector (S m))
                                 (fun l1 => dep_map (@det m)
                                                    (dep_colist (mat_transpose l1)))
                                 (eq_add_S n0 m h3) l0) n h1 h2 l)
              end eq_refl
  end eq_refl.

Open Scope dep_list_scope.

Lemma det_cons: forall {n} (h: Vector (S n)) (l: Matrix n (S n)),
    det (dep_cons h l) = vec_dot_prod (alter_sign h)
                                      (dep_map det (dep_colist (mat_transpose l))).
Proof. intros. easy. Qed.

Hint Rewrite @det_cons: matrix.

Lemma determinant_for_2: forall (a b c d: R),
    det {| {| a; b |} ; {| c; d |} |} = (a * d - b * c)%R.
Proof. intros. vm_compute. ring. Qed.

Lemma determinant_for_3: forall (a b c d e f g h i: R),
    det {| {| a; b; c |}; {| d; e; f |}; {| g; h; i |} |} =
    (a * e * i + b * f * g + c * d * h - c * e * g - b * d * i - a * f * h)%R.
Proof. intros. vm_compute. ring. Qed.

Lemma det_identity: forall {n}, det (@identity_mat n) = 1%R.
Proof.
  induction n. 1: now simpl. simpl identity_mat. rewrite det_cons.
  autorewrite with matrix. destruct n.
  - simpl. vm_compute. ring.
  - autorewrite with dep_list vector. now rewrite IHn, Rmult_1_r, Rplus_0_r.
Qed.

Hint Rewrite @det_identity: matrix.

Lemma det_transpose: forall {n} (A: Matrix n n), det (mat_transpose A) = det A.
Proof.
  intro n. assert (n <= n) by (apply le_n). remember n as m. rewrite Heqm in H at 2.
  clear Heqm. revert m H. induction n; intros. 1: apply le_n_0_eq in H; now subst.
  destruct m. 1: easy. apply le_S_n in H. unfold Matrix in *. dep_step_decomp A.
  autorewrite with matrix. remember (mat_transpose A1) as A. unfold Matrix in *.
  clear A1 HeqA. dep_step_decomp A. destruct m.
  - dep_list_decomp. rewrite dep_colist_nil. simpl. f_equal.
  - autorewrite with dep_list. dep_step_decomp A0.
    autorewrite with vector dep_list matrix. rewrite IHn, !vec_dot_prod_scal_l; auto.
    do 2 f_equal. clear A3. rewrite !dep_map_nest.
    rewrite (dep_map_ext (fun x => vec_dot_prod
                                     (alter_sign A4)
                                     (dep_map det (dep_colist (mat_transpose x))))
                         (fun x => det (dep_cons A4 x))) by
        (intros; now rewrite det_cons).
    rewrite (dep_map_ext (fun x => vec_dot_prod
                                     (alter_sign A1)
                                     (dep_map det (dep_colist (mat_transpose x))))
                         (fun x => det (dep_cons A1 x))) by
        (intros; now rewrite det_cons).
    rewrite <- (dep_map_nest (vec_dot_prod (alter_sign A4))),
    <- (dep_map_nest (vec_dot_prod (alter_sign A1))), <- (dep_map_nest (dep_map det)),
    <- (dep_map_nest (dep_map det) (fun x : dep_list (Vector (S m)) m =>
                                      (dep_colist (mat_transpose x)))).
    rewrite vec_dot_prod_nest. do 2 f_equal. clear A1 A4. unfold Matrix, Vector.
    unfold mat_transpose in *. rewrite dep_list_transpose_double_map, dep_colist_nest.
    rewrite dep_map_double_nest. apply dep_map_ext. intros. apply dep_map_ext, IHn.
    now apply le_Sn_le.
Qed.

Hint Rewrite @det_transpose: matrix.

Lemma dep_colist_mat_mul: forall {m l n} (m1: Matrix (S m) l) (m2: Matrix l n),
    dep_colist (mat_mul m1 m2) = dep_map (fun x => mat_mul x m2) (dep_colist m1).
Proof.
  intros. revert m m1. induction m; intros; unfold Matrix in *.
  - dep_list_decomp. now autorewrite with matrix dep_list.
  - dep_step_decomp m1. autorewrite with matrix dep_list. rewrite IHm. f_equal.
    rewrite !dep_map_nest. apply dep_map_ext. intros. now autorewrite with matrix.
Qed.

Lemma dep_colist_scal: forall {m} (a: R) (v: Vector (S m)),
    dep_colist (vec_scal_mul a v) = dep_map (vec_scal_mul a) (dep_colist v).
Proof.
  intros. induction m; unfold Vector in *.
  - dep_list_decomp. now vm_compute.
  - dep_step_decomp v. autorewrite with vector dep_list. f_equal. rewrite IHm.
    rewrite !dep_map_nest. apply dep_map_ext. intros. now autorewrite with vector.
Qed.

Lemma det_row_mul: forall {n m: nat} (a: R) (m1: Matrix n (n + S m))
                          (m2: Matrix m (n + S m)) (r: Vector (n + S m)),
    det (dep_app m1 (dep_cons (vec_scal_mul a r) m2)) =
    (a * det (dep_app m1 (dep_cons r m2)))%R.
Proof.
  induction n; intros; unfold Matrix in *; dep_list_decomp.
  - simpl. now rewrite alter_sign_scal_mul, vec_dot_prod_scal_l.
  - revert m2 r m0 m3.
    cut (forall (m2 : dep_list (dep_list R (S (n + S m))) m) (r : Vector (S (n + S m)))
                (m0 : dep_list R (S (n + S m)))
                (m3 : dep_list (dep_list R (S (n + S m))) n),
            det (dep_app (dep_cons m0 m3) (dep_cons (vec_scal_mul a r) m2)) =
            (a * det (dep_app (dep_cons m0 m3) (dep_cons r m2)))%R).
    1: intros; apply H. intros. simpl dep_app. autorewrite with matrix.
    rewrite <- vec_dot_prod_scal_r. f_equal. clear m0. unfold mat_transpose.
    rewrite !dep_transpose_app, !dep_colist_app. simpl.
    rewrite !dep_colist_cons_col, dep_colist_scal, <- dep_list_binop_map_1.
    unfold vec_scal_mul at 2. rewrite !dep_map_list_binop, !dep_list_binop_triop.
    apply dep_list_triop_ext. clear -IHn. intros.
    rewrite <- (dep_list_transpose_involutive x), <- (dep_list_transpose_involutive z).
    generalize (dep_list_transpose x). generalize (dep_list_transpose z). clear -IHn.
    intros x z. rewrite <- !mat_transpose_cons_row. unfold mat_transpose.
    rewrite <- !dep_transpose_app, !det_transpose. apply IHn.
Qed.

Lemma dep_colist_vec_add: forall {n} (v1 v2: Vector (S n)),
    dep_colist (vec_add v1 v2) =
    dep_list_binop vec_add (dep_colist v1) (dep_colist v2).
Proof.
  intros. induction n; unfold Vector in *.
  - dep_list_decomp. now vm_compute.
  - dep_step_decomp v1. dep_step_decomp v2. autorewrite with vector dep_list. f_equal.
    rewrite IHn, <- dep_list_binop_map_1, <- dep_list_binop_map_2, dep_map_list_binop.
    apply dep_list_binop_ext. intros. now autorewrite with vector.
Qed.

Lemma det_row_add: forall {n m: nat} (m1: Matrix n (n + S m))
                          (m2: Matrix m (n + S m)) (r1 r2: Vector (n + S m)),
    det (dep_app m1 (dep_cons (vec_add r1 r2) m2)) =
    (det (dep_app m1 (dep_cons r1 m2)) + det (dep_app m1 (dep_cons r2 m2)))%R.
Proof.
  induction n; intros; unfold Matrix in *; dep_list_decomp.
  - simpl dep_app. revert m2 r1 r2.
    cut (forall (m2 : dep_list (dep_list R (S m)) m) (r1 r2 : Vector (S m)),
            det (dep_cons (vec_add r1 r2) m2) =
            (det (dep_cons r1 m2) + det (dep_cons r2 m2))%R); intros. 1: apply H.
    autorewrite with matrix. now rewrite alter_sign_vec_add, vec_dot_prod_add_r.
  - revert m2 r1 r2 m0 m3.
    cut (forall (m2 : dep_list (dep_list R (S (n + S m))) m)
                (r1 r2 : Vector (S (n + S m)))
                (m0 : dep_list R (S (n + S m)))
                (m3 : dep_list (dep_list R (S (n + S m))) n),
            det (dep_app (dep_cons m0 m3) (dep_cons (vec_add r1 r2) m2)) =
            (det (dep_app (dep_cons m0 m3) (dep_cons r1 m2)) +
             det (dep_app (dep_cons m0 m3) (dep_cons r2 m2)))%R); intros. 1: apply H.
    simpl dep_app. autorewrite with matrix. rewrite <- vec_dot_prod_add_l. f_equal.
    clear m0. unfold mat_transpose. rewrite !dep_transpose_app, !dep_colist_app. simpl.
    rewrite !dep_colist_cons_col, dep_colist_vec_add, !dep_map_list_binop,
    !dep_list_binop_triop, dep_list_triop_quadruple.
    unfold vec_add at 2. rewrite <- dep_list_quadruple_split.
    apply dep_list_quadruple_ext. intros. rewrite <- (mat_transpose_involutive w),
    <- (mat_transpose_involutive x), <- !mat_transpose_cons_row. unfold mat_transpose.
    rewrite <- !dep_transpose_app, !det_transpose. apply IHn.
Qed.

Lemma det_dup_first_2: forall {n} (r: Vector (S (S n))) (m: Matrix n (S (S n))),
    det (dep_cons r (dep_cons r m)) = 0%R.
Proof.
  induction n; intros; unfold Matrix in *; unfold Vector in *.
  - dep_list_decomp. vm_compute. ring.
  - rewrite <- det_transpose, !mat_transpose_cons_row. generalize (mat_transpose m).
    clear m. intros. unfold Matrix in *. dep_step_decomp m. dep_step_decomp r.
    rewrite !dep_list_binop_cons. rewrite <- (mat_transpose_involutive m1).
    autorewrite with matrix dep_list vector. ring_simplify. rewrite !dep_map_nest.
    rewrite (dep_map_ext (fun x => 0%R)) by apply IHn. rewrite dep_map_const.
    now autorewrite with vector.
Qed.

Lemma det_swap_first_2: forall {n} (r1 r2: Vector (S (S n))) (m: Matrix n (S (S n))),
    det (dep_cons r1 (dep_cons r2 m)) = (- det (dep_cons r2 (dep_cons r1 m)))%R.
Proof.
  intros. pose proof (det_dup_first_2 (vec_add r1 r2) m).
  pose proof (det_row_add dep_nil (dep_cons (vec_add r1 r2) m)). simpl dep_app in H0.
  rewrite H0 in H. clear H0. revert r1 r2 m H.
  cut (forall (r1 r2 : Vector (1 + (S n))) (m : Matrix n (1 + (S n))),
          (det (dep_cons r1 (dep_cons (vec_add r1 r2) m)) +
           det (dep_cons r2 (dep_cons (vec_add r1 r2) m)))%R = 0%R ->
          det (dep_cons r1 (dep_cons r2 m)) =
          (- det (dep_cons r2 (dep_cons r1 m)))%R); intros. 1: now apply H.
  pose proof (det_row_add {| r1 |} m). simpl dep_app in H0. rewrite H0 in H. clear H0.
  pose proof (det_row_add {| r2 |} m). simpl dep_app in H0. rewrite H0 in H. clear H0.
  rewrite !det_dup_first_2, Rplus_0_r, Rplus_0_l in H. apply Rplus_opp_r_uniq.
  now rewrite Rplus_comm.
Qed.

Lemma det_row_dup_ind:
  forall n m l: nat,
    (forall (m1 : dep_list (dep_list R (n + S (m + S l))) n)
            (m2 : dep_list (dep_list R (n + S (m + S l))) m)
            (m3 : dep_list (dep_list R (n + S (m + S l))) l)
            (r : Vector (n + S (m + S l))),
        det (dep_app m1 (dep_cons r (dep_app m2 (dep_cons r m3)))) = 0%R) ->
    forall (m2 : dep_list (dep_list R (S n + S (m + S l))) m)
           (m3 : dep_list (dep_list R (S n + S (m + S l))) l)
           (r : Vector (S n + S (m + S l))) (m0 : dep_list R (S n + S (m + S l)))
           (m4 : dep_list (dep_list R (S n + S (m + S l))) n),
      det (dep_cons m0 (dep_app m4 (dep_cons r (dep_app m2 (dep_cons r m3))))) = 0%R.
Proof.
  intros n m l IHn.
  cut (forall (m2 : dep_list (dep_list R (S (n + S (m + S l)))) m)
              (m3 : dep_list (dep_list R (S (n + S (m + S l)))) l)
              (r : Vector (S (n + S (m + S l))))
              (m0 : dep_list R (S (n + S (m + S l))))
              (m4 : dep_list (dep_list R (S (n + S (m + S l)))) n),
          det (dep_cons m0 (dep_app m4 (dep_cons r (dep_app m2 (dep_cons r m3))))) =
          0%R); intros. 1: apply H. autorewrite with matrix. unfold mat_transpose.
  rewrite dep_transpose_app, dep_colist_app. simpl.
  rewrite dep_transpose_app. simpl.
  rewrite !dep_colist_cons_col, dep_colist_app, dep_map_list_binop,
  dep_colist_cons_col, !dep_list_binop_triop, dep_list_triop_quadruple'.
  rewrite (dep_list_quadruple_ext (fun _ _ _ _ => 0%R)); intros.
  - rewrite dep_list_quadruple_const. apply vec_dot_prod_zero_r.
  - rewrite <- (mat_transpose_involutive x), <- (mat_transpose_involutive z),
    <- (mat_transpose_involutive w), <- !mat_transpose_cons_row.
    unfold mat_transpose. rewrite <- dep_transpose_app, <- mat_transpose_cons_row.
    unfold mat_transpose. rewrite <- dep_transpose_app, det_transpose. apply IHn.
Qed.

Lemma det_row_dup: forall
    {n m l: nat} (m1: Matrix n (n + S (m + S l))) (m2: Matrix m (n + S (m + S l)))
    (m3: Matrix l (n + S (m + S l))) (r: Vector (n + S (m + S l))),
    det (dep_app m1 (dep_cons r (dep_app m2 (dep_cons r m3)))) = 0%R.
Proof.
  induction n; intros; unfold Matrix in *; dep_list_decomp; simpl dep_app.
  - revert m2 m3 r.
    cut  (forall (m2 : dep_list (dep_list R (S (m + S l))) m)
                 (m3 : dep_list (dep_list R (S (m + S l))) l)
                 (r : Vector (S (m + S l))),
             det (dep_cons r (dep_app m2 (dep_cons r m3))) = 0%R). 1: intros; apply H.
    induction m; intros.
    + dep_list_decomp; simpl dep_app. revert m3 r.
      cut (forall (m3 : dep_list (dep_list R (S (S l))) l) (r : Vector (S (S l))),
              det (dep_cons r (dep_cons r m3)) = 0%R); intros. 1: apply H.
      induction l.
      * unfold Vector in *. dep_list_decomp. vm_compute. ring.
      * apply det_dup_first_2.
    + dep_step_decomp m2. simpl dep_app. rewrite (det_swap_first_2 r m0).
      apply Ropp_eq_0_compat.
      assert
        (forall (m2 : dep_list (dep_list R (1 + (S (m + S l)))) m)
                (m3 : dep_list (dep_list R (1 + (S (m + S l)))) l)
                (r : Vector (1 + (S (m + S l))))
                (m0 : dep_list R (1 + (S (m + S l)))),
            det (dep_cons m0 (dep_app {||}
                                      (dep_cons r (dep_app m2 (dep_cons r m3))))) =
            0%R). { intros. apply (det_row_dup_ind O m l). intros. dep_step_decomp m6.
        simpl dep_app. apply IHm. } simpl dep_app in H. apply H.
  - now apply det_row_dup_ind.
Qed.

Lemma det_row_add_n1m1l:
  forall {n m l : nat} (m1 : Matrix n (n + S (m + S l)))
         (m2 : Matrix m (n + S (m + S l))) (m3 : Matrix l (n + S (m + S l)))
         (r r1 r2 : Vector (n + S (m + S l))),
    det (dep_app m1 (dep_cons r (dep_app m2 (dep_cons (vec_add r1 r2) m3)))) =
    (det (dep_app m1 (dep_cons r (dep_app m2 (dep_cons r1 m3)))) +
     det (dep_app m1 (dep_cons r (dep_app m2 (dep_cons r2 m3)))))%R.
Proof.
  intros. induction n.
  - unfold Matrix in *. dep_list_decomp. simpl dep_app. revert m2 m3 r1 r2 r.
    cut (forall (m2 : dep_list (dep_list R (S m + S l)) m)
                (m3 : dep_list (dep_list R (S m + S l)) l)
                (r1 r2 : Vector (S m + S l)) (r : dep_list R (S m + S l)),
            det (dep_cons r (dep_app m2 (dep_cons (vec_add r1 r2) m3))) =
            (det (dep_cons r (dep_app m2 (dep_cons r1 m3))) +
             det (dep_cons r (dep_app m2 (dep_cons r2 m3))))%R); intros. 1: apply H.
    rewrite !dep_cons_app. apply det_row_add.
  - unfold Matrix in *. dep_step_decomp m1. simpl dep_app. revert m2 m3 r r1 r2 m0 m4.
    cut (forall (m2 : dep_list (dep_list R (S (n + S (m + S l)))) m)
                (m3 : dep_list (dep_list R (S (n + S (m + S l)))) l)
                (r r1 r2 m0: dep_list R (S (n + S (m + S l))))
                (m4 : dep_list (dep_list R (S (n + S (m + S l)))) n),
                      det
                        (dep_cons
                           m0
                           (dep_app
                              m4 (dep_cons
                                    r (dep_app m2 (dep_cons (vec_add r1 r2) m3))))) =
                      (det (dep_cons
                              m0 (dep_app
                                    m4 (dep_cons r (dep_app m2 (dep_cons r1 m3))))) +
                       det (dep_cons
                              m0 (dep_app
                                    m4 (dep_cons
                                          r (dep_app m2 (dep_cons r2 m3))))))%R).
    1: intros; apply H. intros. autorewrite with matrix. rewrite <- vec_dot_prod_add_l.
    f_equal. clear m0. unfold mat_transpose.
    rewrite !dep_transpose_app, !dep_colist_app. simpl.
    rewrite !dep_transpose_app. simpl.
    rewrite !dep_colist_cons_col, !dep_colist_app, !dep_map_list_binop,
    !dep_colist_cons_col, dep_colist_vec_add, !dep_list_binop_triop,
    dep_list_triop_quadruple, !dep_list_triop_quintuple, dep_list_tri_quad_sextuple.
    rewrite
      (dep_list_sextuple_ext
         (fun (x : dep_list (dep_list R n) (n + S (m + S l)))
              (y : dep_list R (n + S (m + S l)))
              (z : dep_list (dep_list R m) (n + S (m + S l)))
              (w v : Vector (n + S (m + S l)))
              (u : dep_list (dep_list R l) (n + S (m + S l))) =>
            (det (dep_app
                    (dep_list_transpose x)
                    (dep_cons y (dep_app (dep_list_transpose z)
                                         (dep_cons w (dep_list_transpose u))))) +
             det (dep_app
                    (dep_list_transpose x)
                    (dep_cons y (dep_app (dep_list_transpose z)
                                         (dep_cons v (dep_list_transpose u))))))%R)).
    + rewrite dep_list_sextuple_split. unfold vec_add.
      f_equal; apply dep_list_quintuple_ext; intros; unfold Vector in *;
      rewrite <- det_transpose; unfold mat_transpose;
      rewrite dep_transpose_app, dep_transpose_cons_row, dep_transpose_app,
      dep_transpose_cons_row; now autorewrite with dep_list.
    + intros.
      rewrite <- (dep_list_transpose_involutive x) at 1.
      rewrite <- (dep_list_transpose_involutive z) at 1.
      rewrite <- (dep_list_transpose_involutive u) at 1.
      generalize (dep_list_transpose x). generalize (dep_list_transpose z).
      generalize (dep_list_transpose u). clear -IHn. intros u z x.
      rewrite <- !mat_transpose_cons_row. unfold mat_transpose.
      rewrite <- !dep_transpose_app, <- !dep_transpose_cons_row, <- !dep_transpose_app.
      now rewrite det_transpose, IHn.
Qed.

Lemma det_swap_row: forall
    {n m l: nat} (m1: Matrix n (n + S (m + S l))) (m2: Matrix m (n + S (m + S l)))
    (m3: Matrix l (n + S (m + S l))) (r1 r2: Vector (n + S (m + S l))),
    det (dep_app m1 (dep_cons r1 (dep_app m2 (dep_cons r2 m3)))) =
    (- det (dep_app m1 (dep_cons r2 (dep_app m2 (dep_cons r1 m3)))))%R.
Proof.
  intros. pose proof (det_row_dup m1 m2 m3 (vec_add r1 r2)).
  rewrite det_row_add, !det_row_add_n1m1l, !det_row_dup, Rplus_0_l, Rplus_0_r
    in H. apply Rplus_opp_r_uniq. now rewrite Rplus_comm.
Qed.

Lemma det_row_mul_n1m1l:
  forall {n m l : nat} (m1 : Matrix n (n + S (m + S l)))
         (m2 : Matrix m (n + S (m + S l))) (m3 : Matrix l (n + S (m + S l)))
         (r1 r2 : Vector (n + S (m + S l))) (a: R),
    det (dep_app m1 (dep_cons r1 (dep_app m2 (dep_cons (vec_scal_mul a r2) m3)))) =
    (a * det (dep_app m1 (dep_cons r1 (dep_app m2 (dep_cons r2 m3)))))%R.
Proof.
  intros. induction n.
  - unfold Matrix in *. dep_list_decomp. simpl dep_app. revert m2 m3 r1 r2.
    cut (forall (m2 : dep_list (dep_list R (S m + S l)) m)
                (m3 : dep_list (dep_list R (S m + S l)) l)
                (r1 r2 : Vector (S m + S l)),
            det (dep_cons r1 (dep_app m2 (dep_cons (vec_scal_mul a r2) m3))) =
            (a * det (dep_cons r1 (dep_app m2 (dep_cons r2 m3))))%R); intros.
    1: apply H. now rewrite !dep_cons_app, det_row_mul.
  - unfold Matrix in *. dep_step_decomp m1. simpl dep_app. revert m2 m3 r1 r2 m0 m4.
    cut (forall (m2 : dep_list (dep_list R (S (n + S (m + S l)))) m)
                (m3 : dep_list (dep_list R (S (n + S (m + S l)))) l)
                (r1 r2 : Vector (S (n + S (m + S l))))
                (m0 : dep_list R (S (n + S (m + S l))))
                (m4 : dep_list (dep_list R (S (n + S (m + S l)))) n),
            det (dep_cons
                   m0 (dep_app
                         m4 (dep_cons
                               r1 (dep_app m2 (dep_cons (vec_scal_mul a r2) m3))))) =
            (a * det (dep_cons
                        m0 (dep_app
                              m4 (dep_cons r1 (dep_app m2 (dep_cons r2 m3))))))%R).
    1: intros; apply H. intros. autorewrite with matrix.
    rewrite <- vec_dot_prod_scal_r. f_equal. clear m0. unfold mat_transpose.
    rewrite !dep_transpose_app, !dep_colist_app. simpl.
    rewrite !dep_transpose_app. simpl.
    rewrite !dep_colist_cons_col, !dep_colist_app, !dep_map_list_binop,
    !dep_colist_cons_col, !dep_colist_scal, <- dep_list_binop_map_1,
    !dep_list_binop_triop, !dep_list_triop_quintuple.
    rewrite
      (dep_list_quintuple_ext
         (fun (x : dep_list (dep_list R n) (n + S (m + S l)))
              (y : dep_list R (n + S (m + S l)))
              (z : dep_list (dep_list R m) (n + S (m + S l)))
              (w : dep_list R (n + S (m + S l)))
              (v : dep_list (dep_list R l) (n + S (m + S l))) =>
            (a * det (dep_list_binop
                        dep_app x
                        (dep_list_binop
                           (dep_cons (n:=m + S l)) y
                           (dep_list_binop
                              dep_app z (dep_list_binop (dep_cons (n:=l)) w v)))))%R)).
    + now rewrite dep_list_quintuple_constant_split.
    + intros.
      rewrite <- (dep_list_transpose_involutive x). generalize (dep_list_transpose x).
      rewrite <- (dep_list_transpose_involutive z). generalize (dep_list_transpose z).
      rewrite <- (dep_list_transpose_involutive v). generalize (dep_list_transpose v).
      clear -IHn. intros v z x. rewrite <- !mat_transpose_cons_row.
      unfold mat_transpose. rewrite <- !dep_transpose_app, <- !dep_transpose_cons_row,
                            <- !dep_transpose_app. now rewrite !det_transpose, IHn.
Qed.

Lemma det_row_add_row_1:
  forall {n m l : nat} (m1 : Matrix n (n + S (m + S l)))
         (m2 : Matrix m (n + S (m + S l))) (m3 : Matrix l (n + S (m + S l)))
         (r1 r2 : Vector (n + S (m + S l))) (a: R),
    det (dep_app
           m1 (dep_cons r1 (dep_app
                              m2 (dep_cons (vec_add r2 (vec_scal_mul a r1)) m3)))) =
    det (dep_app m1 (dep_cons r1 (dep_app m2 (dep_cons r2 m3)))).
Proof.
  intros. rewrite det_row_add_n1m1l, det_row_mul_n1m1l, det_row_dup. ring.
Qed.

Lemma det_row_add_row_2:
  forall {n m l : nat} (m1 : Matrix n (n + S (m + S l)))
         (m2 : Matrix m (n + S (m + S l))) (m3 : Matrix l (n + S (m + S l)))
         (r1 r2 : Vector (n + S (m + S l))) (a: R),
    det (dep_app
           m1 (dep_cons (vec_add r1 (vec_scal_mul a r2)) (dep_app
                                                            m2 (dep_cons r2 m3)))) =
    det (dep_app m1 (dep_cons r1 (dep_app m2 (dep_cons r2 m3)))).
Proof.
  intros. rewrite det_row_add, det_row_mul, det_row_dup. ring.
Qed.

(** *Triangular Matrix *)

Fixpoint diagonal {n: nat} (mat: Matrix n n) {struct n}: Vector n :=
  match n as x return (x = n -> Vector x) with
  | O => fun h1 => dep_nil
  | S m =>
    fun h1 =>
      match mat in (dep_list _ s) return (s = n -> Vector (S m)) with
      | dep_nil =>
        fun h2 => False_rect _ (eq_ind (S m) _ (fun h3 => (O_S m h3)) _ h1 h2)
      | @dep_cons _ n0 h l =>
        fun h2 =>
          eq_rec (S m) _
                 (fun (h0 : dep_list R (S m))
                      (l0 : dep_list (dep_list R (S m)) n0)
                      (h3 : S n0 = S m) =>
                    eq_rec_r _
                             (fun l1 =>
                                dep_cons (dep_hd h0) (diagonal (dep_map dep_tl l1)))
                             (eq_add_S _ _ h3) l0) n h1 h l h2
      end eq_refl
  end eq_refl.

Lemma diag_cons: forall {n} (h: Vector (S n)) (l: Matrix n (S n)),
    diagonal (dep_cons h l) = dep_cons (dep_hd h) (diagonal (dep_map dep_tl l)).
Proof. intros. easy. Qed.

Hint Rewrite @diag_cons: matrix.

Lemma diag_transpose: forall {n} (mat: Matrix n n),
    diagonal (mat_transpose mat) = diagonal mat.
Proof.
  induction n; intros; unfold Matrix in *; dep_list_decomp. 1: easy.
  autorewrite with matrix. simpl dep_hd. rename mat2 into a.
  destruct (dep_vertical_split mat1) as [v [mat2 ?]]. subst mat1.
  autorewrite with matrix dep_list. simpl dep_hd. now rewrite IHn.
Qed.

Hint Rewrite @diag_transpose: matrix.

Inductive ut_sigT: {n: nat & Matrix n n} -> Prop :=
| UT_O: ut_sigT (existT _ O (@dep_nil (dep_list R 0)))
| UT_Sn: forall
    (n: nat) (m: Matrix n n) (v: Vector (S n)),
    ut_sigT (existT (fun x => Matrix x x) n m) ->
    ut_sigT (existT _ (S n)
                    (dep_cons v (dep_list_binop (dep_cons (n := n)) vec_zero m))).

Definition upper_triangular {n: nat} (mat: Matrix n n): Prop :=
  ut_sigT (existT (fun x => Matrix x x) n mat).

Lemma upper_triangular_det: forall {n} (mat: Matrix n n),
    upper_triangular mat -> det mat = vec_prod (diagonal mat).
Proof.
  induction n; intros; unfold Matrix in *. 1: now dep_list_decomp.
  unfold upper_triangular in H. inversion H. subst. unfold Vector in *. clear H2.
  dep_step_decomp v0. autorewrite with matrix vector dep_list. simpl dep_hd.
  rewrite <- IHn by (now red). clear. unfold Matrix in *. destruct n.
  - dep_list_decomp. vm_compute. ring.
  - autorewrite with dep_list vector. rewrite det_transpose.
    rewrite <- (Rplus_0_r (v1 * det m0)%R) at 2. f_equal.
    rewrite dep_map_nest, (dep_map_ext (fun x => 0%R)).
    + rewrite dep_map_const. now autorewrite with vector.
    + intros. now autorewrite with matrix vector.
Qed.

Lemma upper_triangular_mult: forall {n} (m1 m2: Matrix n n),
    upper_triangular m1 -> upper_triangular m2 -> upper_triangular (mat_mul m1 m2).
Proof.
  unfold upper_triangular. induction n; intros.
  - unfold Matrix in *. dep_list_decomp. clear. autorewrite with matrix. constructor.
  - inversion H. apply inj_pair2_eq_dec in H3. 2: exact Nat.eq_dec. subst.
    inversion H0. apply inj_pair2_eq_dec in H4. 2: exact Nat.eq_dec. subst.
    autorewrite with matrix.
    cut (mat_mul m0 (dep_list_binop (dep_cons (n:=n)) vec_zero m1) =
         dep_list_binop (dep_cons (n := n)) vec_zero (mat_mul m0 m1)).
    + intros. rewrite H1. constructor. now apply IHn.
    + rewrite !mat_mul_as_vec_mul. now autorewrite with matrix dep_list.
Qed.

Lemma upper_triangular_diag: forall {n} (m1 m2: Matrix n n),
    upper_triangular m1 -> upper_triangular m2 ->
    diagonal (mat_mul m1 m2) = dep_list_binop Rmult (diagonal m1) (diagonal m2).
Proof.
  unfold upper_triangular. induction n; intros.
  - unfold Matrix in *. dep_list_decomp. now vm_compute.
  - inversion H. apply inj_pair2_eq_dec in H3. 2: exact Nat.eq_dec. subst.
    inversion H0. apply inj_pair2_eq_dec in H4. 2: exact Nat.eq_dec. subst.
    assert (mat_mul m0 (dep_list_binop (dep_cons (n:=n)) vec_zero m1) =
            dep_list_binop (dep_cons (n := n)) vec_zero (mat_mul m0 m1)) by
        (rewrite !mat_mul_as_vec_mul; now autorewrite with matrix dep_list).
    autorewrite with matrix dep_list. rewrite H1. clear H1. autorewrite with dep_list.
    rewrite IHn; auto. f_equal. clear. unfold Vector in *. dep_list_decomp.
    simpl. autorewrite with vector. ring.
Qed.

Lemma upper_triangular_det_mul: forall {n} (m1 m2: Matrix n n),
    upper_triangular m1 -> upper_triangular m2 ->
    det (mat_mul m1 m2) = (det m1 * det m2)%R.
Proof.
  intros. rewrite !upper_triangular_det; auto.
  - rewrite upper_triangular_diag; auto. generalize (diagonal m1).
    generalize (diagonal m2). clear. revert n. apply dep_list_ind_2.
    + vm_compute. ring.
    + intros. autorewrite with vector dep_list. rewrite H. ring.
  - now apply upper_triangular_mult.
Qed.

Lemma upper_triangular_spec: forall {n} (mat: Matrix n n),
    upper_triangular mat <->
    forall i j, i < j < n ->
                dep_nth j (dep_nth i (mat_transpose mat) vec_zero) 0%R = 0%R.
Proof.
  induction n; intros; split; intros; unfold Matrix in *.
  - destruct H0. inversion H1.
  - dep_list_decomp. constructor.
  - red in H. inversion H. subst. apply inj_pair2_eq_dec in H3. 2: exact Nat.eq_dec.
    subst. unfold upper_triangular in IHn. rewrite IHn in H2. clear IHn H.
    unfold Vector in *. dep_list_decomp. autorewrite with matrix dep_list.
    destruct H0. destruct i.
    + destruct j. 1: inversion H. simpl dep_nth. unfold vec_zero. apply dep_nth_repeat.
      now apply lt_S_n in H0.
    + destruct j. 1: inversion H. apply lt_S_n in H. apply lt_S_n in H0.
      simpl dep_nth at 2. rewrite (dep_nth_list_binop _ _ _ _ 0%R vec_zero); auto.
      simpl. now apply H2.
  - dep_step_decomp mat. rename mat0 into v1. rename mat1 into mat.
    destruct (dep_vertical_split mat) as [v2 [mat1 ?]]. subst. red. dep_list_decomp.
    pose proof H. autorewrite with matrix dep_list in H. specialize (H O). simpl in H.
    assert (v2 = vec_zero). {
      rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 0%R), (dep_nth_indep _ _ d2 0%R); auto.
      clear d1 d2. unfold vec_zero. rewrite dep_nth_repeat; auto. specialize (H (S i)).
      simpl in H. apply H. split; [apply Nat.lt_0_succ | now apply lt_n_S]. } subst v2.
    constructor. autorewrite with matrix dep_list in H0.
    unfold upper_triangular in IHn. rewrite IHn. intros.
    assert (S i < S j < S n) by (destruct H1; now split; apply lt_n_S).
    specialize (H0 _ _ H2). simpl dep_nth at 2 in H0.
    now rewrite (dep_nth_list_binop _ _ _ _ 0%R vec_zero) in H0.
Qed.

Definition lower_triangular {n: nat} (mat: Matrix n n): Prop :=
  upper_triangular (mat_transpose mat).

Lemma lower_triangular_det: forall {n} (mat: Matrix n n),
    lower_triangular mat -> det mat = vec_prod (diagonal mat).
Proof.
  intros. red in H. apply upper_triangular_det in H. now autorewrite with matrix in H.
Qed.

Lemma lower_triangular_mult: forall {n} (m1 m2: Matrix n n),
    lower_triangular m1 -> lower_triangular m2 -> lower_triangular (mat_mul m1 m2).
Proof.
  intros. red in H, H0 |- *. rewrite mat_transpose_mul.
  now apply upper_triangular_mult.
Qed.

Lemma lower_triangular_diag: forall {n} (m1 m2: Matrix n n),
    lower_triangular m1 -> lower_triangular m2 ->
    diagonal (mat_mul m1 m2) = dep_list_binop Rmult (diagonal m1) (diagonal m2).
Proof.
  unfold lower_triangular. intros.
  rewrite <- diag_transpose, <- (diag_transpose m1), <- (diag_transpose m2),
  mat_transpose_mul, dep_list_binop_comm.
  - now apply upper_triangular_diag.
  - apply Rmult_comm.
Qed.

Lemma lower_triangular_det_mul: forall {n} (m1 m2: Matrix n n),
    lower_triangular m1 -> lower_triangular m2 ->
    det (mat_mul m1 m2) = (det m1 * det m2)%R.
Proof.
  intros. red in H, H0. pose proof (upper_triangular_det_mul _ _ H0 H).
  now rewrite <- mat_transpose_mul, !det_transpose, Rmult_comm in H1.
Qed.

Lemma lower_triangular_spec: forall {n} (mat: Matrix n n),
    lower_triangular mat <->
    forall i j, i < j < n -> dep_nth j (dep_nth i mat vec_zero) 0%R = 0%R.
Proof.
  intros. unfold lower_triangular. rewrite upper_triangular_spec.
  now autorewrite with matrix.
Qed.

Lemma upper_dual_rev_lower: forall {n} (m1 m2: Matrix n n),
    upper_triangular m1 -> dual_rev_rel m1 m2 -> lower_triangular m2.
Proof.
  intros. rewrite upper_triangular_spec in H. rewrite lower_triangular_spec. intros.
  red in H0. destruct H0 as [m3 [? ?]]. red in H0, H2.
  pose proof (ltlt_sub1_lt i j n H1). specialize (H _ _ H3). destruct H3.
  specialize (H2 vec_zero _ H4). destruct H1.
  assert (i < n) by (eapply lt_trans; eauto). rewrite lt_sub1_sub1_sub_eq in H2; auto.
  specialize (H0 _ vec_zero H4). rewrite H2 in H0. red in H0.
  assert (n - 1 - j < n) by (eapply lt_trans; eauto). specialize (H0 0%R _ H7).
  rewrite lt_sub1_sub1_sub_eq in H0; auto.
  rewrite (dep_nth_transpose vec_zero) in H; auto. now rewrite H0 in H.
Qed.

Lemma lower_dual_rev_upper: forall {n} (m1 m2: Matrix n n),
    lower_triangular m1 -> dual_rev_rel m1 m2 -> upper_triangular m2.
Proof.
  intros. rewrite lower_triangular_spec in H. rewrite upper_triangular_spec. intros.
  red in H0. destruct H0 as [m3 [? ?]]. red in H0, H2.
  pose proof (ltlt_sub1_lt i j n H1). specialize (H _ _ H3). destruct H3, H1.
  assert (i < n) by (eapply lt_trans; eauto).
  rewrite (dep_nth_transpose vec_zero); auto.
  assert (n - 1 - j < n) by (eapply lt_trans; eauto).
  specialize (H2 vec_zero _ H7). rewrite lt_sub1_sub1_sub_eq in H2; auto.
  specialize (H0 _ vec_zero H7). rewrite H2 in H0. red in H0. specialize (H0 0%R _ H4).
  rewrite lt_sub1_sub1_sub_eq in H0; auto. now rewrite H0 in H.
Qed.

(** * Elementary Row Operations *)

Definition row_op_mul (a: R) (i: nat) {m n: nat} (mat1 mat2: Matrix m n): Prop :=
  i < m /\ a <> 0%R /\
  (forall j, j <> i -> dep_nth j mat1 vec_zero = dep_nth j mat2 vec_zero) /\
  dep_nth i mat2 vec_zero = vec_scal_mul a (dep_nth i mat1 vec_zero).

Lemma row_op_mul_spec:
  forall (a: R) {m n l: nat} (mat1 mat2: Matrix m l) (mat3 mat4: Matrix n l)
         (v1 v2: Vector l),
    row_op_mul a m (dep_app mat1 (dep_cons v1 mat3))
                   (dep_app mat2 (dep_cons v2 mat4)) <->
    a <> 0%R /\ mat1 = mat2 /\ v2 = vec_scal_mul a v1 /\ mat3 = mat4.
Proof.
  intros. split; intros; destruct H as [? [? [? ?]]].
  - split; [|split; [|split]]; unfold Matrix in *; auto.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_app_1 _ mat1 (dep_cons v1 mat3)); auto.
      rewrite (dep_nth_app_1 _ mat2 (dep_cons v2 mat4)); auto.
      now apply H1, Nat.lt_neq.
    + now rewrite !dep_nth_app_cons in H2.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_cons _ mat3 v1), (dep_nth_cons _ mat4 v2),
      (dep_nth_app_2 _ mat1 (dep_cons v1 mat3)),
      (dep_nth_app_2 _ mat2 (dep_cons v2 mat4)). apply H1, S_plus_neq.
  - subst. split; [|split; [|split]]; auto.
    + apply lt_plus_S_l.
    + intros. destruct (lt_eq_lt_dec j m) as [[? | ?] | ?].
      * now rewrite <- !dep_nth_app_1.
      * exfalso. now apply H0.
      * decomp_lt_subst. now rewrite <- !dep_nth_app_2, <- !dep_nth_cons.
    + now rewrite !dep_nth_app_cons.
Qed.

Lemma row_op_mul_det: forall a i {n: nat} (mat1 mat2: Matrix n n),
    row_op_mul a i mat1 mat2 -> det mat1 = (/ a * det mat2)%R.
Proof.
  intros. pose proof H. destruct H as [? _]. decomp_lt_subst.
  unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  apply row_op_mul_spec in H0. destruct H0 as [? [? [? ?]]]. subst.
  rewrite det_row_mul, <- Rmult_assoc, Rinv_l, Rmult_1_l; auto.
Qed.

Lemma row_op_mul_comm_mul:
  forall a i {m n l: nat} (A A': Matrix m n) (B: Matrix n l),
    row_op_mul a i A A' -> row_op_mul a i (mat_mul A B) (mat_mul A' B).
Proof.
  intros. pose proof H. destruct H as [? _]. decomp_lt_subst.
  unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  apply row_op_mul_spec in H0. destruct H0 as [? [? [? ?]]]. subst.
  autorewrite with matrix. rewrite row_op_mul_spec. split;[|split;[|split]]; auto.
  unfold vec_scal_mul at 2. rewrite dep_map_nest. apply dep_map_ext. intros.
  apply vec_dot_prod_scal_l.
Qed.

Lemma row_op_mul_unique: forall a i {m n: nat} (mat mat1 mat2: Matrix m n),
    row_op_mul a i mat mat1 -> row_op_mul a i mat mat2 -> mat1 = mat2.
Proof.
  intros. pose proof H. destruct H1 as [? _]. decomp_lt_subst.
  unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  rewrite row_op_mul_spec in H, H0. destruct H0 as [? [? [? ?]]].
  destruct H as [? [? [? ?]]]. now subst.
Qed.

Lemma row_op_mul_exists: forall a i {m n: nat} (mat: Matrix m n),
    i < m -> a <> 0%R -> exists mat', row_op_mul a i mat mat'.
Proof.
  intros. decomp_lt_subst. unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  exists (dep_app mat0 (dep_cons (vec_scal_mul a mat2) mat3)).
  rewrite row_op_mul_spec. easy.
Qed.

Lemma row_op_mul_cons: forall a i {m n: nat} (mat1 mat2: Matrix m n) v,
    row_op_mul a i mat1 mat2 ->
    row_op_mul a (S i) (dep_cons v mat1) (dep_cons v mat2).
Proof.
  intros. pose proof H. destruct H0 as [? _]. decomp_lt_subst. unfold Matrix in *.
  dep_add_decomp. dep_list_decomp. rewrite row_op_mul_spec in H.
  destruct H as [? [? [? ?]]]. subst. rewrite !dep_cons_app.
  now rewrite (row_op_mul_spec a (dep_cons v mat1) (dep_cons v mat1) mat5 mat5).
Qed.

Lemma row_op_mul_cons_col: forall a i {m n: nat} (mat1 mat2: Matrix m n),
    row_op_mul a i mat1 mat2 ->
    row_op_mul a i (dep_list_binop (dep_cons (n := n)) vec_zero mat1)
                   (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. pose proof H. destruct H0 as [? _]. decomp_lt_subst. unfold Matrix in *.
  rewrite vec_zero_app, vec_zero_cons. dep_add_decomp. dep_list_decomp.
  rewrite !dep_list_binop_app, !dep_list_binop_cons. rewrite row_op_mul_spec in *.
  destruct H as [? [? [? ?]]]. subst. autorewrite with vector. now rewrite Rmult_0_r.
Qed.

Lemma row_op_mul_row_rev: forall a i {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_mul a i mat1 mat2 -> row_rev_rel mat1 mat3 -> row_rev_rel mat2 mat4 ->
    row_op_mul a i mat3 mat4.
Proof.
  intros. unfold row_op_mul, row_rev_rel in *. destruct H as [? [? [? ?]]].
  split; [|split; [|split]]; auto; intros.
  - destruct (le_lt_dec m j).
    + now rewrite !dep_nth_overflow.
    + specialize (H3 _ H5). specialize (H0 _ vec_zero l). specialize (H1 _ vec_zero l).
      rewrite H3 in H0. eapply rev_rel_unique; eauto.
  - specialize (H0 _ vec_zero H). specialize (H1 _ vec_zero H). rewrite H4 in H1.
    rewrite <- (rev_rel_vec_scal_mul_iff a) in H0; auto.
    eapply rev_rel_unique; eauto.
Qed.

Lemma row_op_mul_rev: forall a i {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_mul a i mat1 mat2 -> rev_rel mat1 mat3 -> rev_rel mat2 mat4 ->
    row_op_mul a (m - 1 - i) mat3 mat4.
Proof.
  intros. unfold row_op_mul, rev_rel in *. destruct H as [? [? [? ?]]].
  split; [|split; [|split]]; [apply lt_sub_1_sub_lt | idtac..]; auto; intros.
  - destruct (le_lt_dec m j). 1: now rewrite !dep_nth_overflow.
    pose proof (lt_sub_1_sub_lt _ _ l). specialize (H0 vec_zero _ H6).
    specialize (H1 vec_zero _ H6). rewrite lt_sub1_sub1_sub_eq in H0, H1; auto.
    assert (m - 1 - j <> i). {
      intro. apply H5. subst i. now rewrite lt_sub1_sub1_sub_eq. }
    specialize (H3 _ H7). now rewrite H0, H1 in H3.
  - specialize (H0 vec_zero _ H). specialize (H1 vec_zero _ H).
    now rewrite <- H0, <- H1.
Qed.

Lemma row_op_mul_dual_rev: forall a i {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_mul a i mat1 mat2 -> dual_rev_rel mat1 mat3 -> dual_rev_rel mat2 mat4 ->
    row_op_mul a (m - 1 - i) mat3 mat4.
Proof.
  intros. unfold dual_rev_rel in *. destruct H0 as [mat5 [? ?]].
  destruct H1 as [mat6 [? ?]]. assert (row_op_mul a i mat5 mat6) by
      (eapply row_op_mul_row_rev; eauto). eapply row_op_mul_rev; eauto.
Qed.

Definition row_op_swap (i j: nat) {m n: nat} (mat1 mat2: Matrix m n): Prop :=
  i < j < m /\
  (forall k, k <> i -> k <> j -> dep_nth k mat1 vec_zero = dep_nth k mat2 vec_zero) /\
  dep_nth i mat1 vec_zero = dep_nth j mat2 vec_zero /\
  dep_nth j mat1 vec_zero = dep_nth i mat2 vec_zero.

Lemma row_op_swap_spec:
  forall {n m l k: nat} (m1 m2: Matrix n k) (m3 m4: Matrix m k)
         (m5 m6: Matrix l k) (v1 v2 v3 v4: Vector k),
    row_op_swap n (n + S m)
                    (dep_app m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5))))
                    (dep_app m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))) <->
    m1 = m2 /\ m3 = m4 /\ m5 = m6 /\ v1 = v4 /\ v3 = v2.
Proof.
  intros. split; intros.
  - destruct H as [? [? [? ?]]]. split; [|split;[|split;[|split]]]; unfold Matrix in *.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_app_1 _ m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5)))),
      (dep_nth_app_1 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H0; apply Nat.lt_neq; [|apply Nat.lt_lt_add_r]; easy.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_app_1 _ m3 (dep_cons v3 m5)),
      (dep_nth_app_1 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _  (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H0. 1: apply S_plus_neq. now apply neq_nSl_nSm, Nat.lt_neq.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_cons _ _ v3), (dep_nth_cons _ m6 v4),
      (dep_nth_app_2 _ m3), (dep_nth_app_2 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _ (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))).
      apply H0. 1: apply S_plus_neq. apply neq_nSl_nSm, S_plus_neq.
    + now rewrite <- dep_nth_app_2, <- dep_nth_cons, !dep_nth_app_cons in H1.
    + now rewrite <- dep_nth_app_2, <- dep_nth_cons, !dep_nth_app_cons in H2.
  - destruct H as [? [? [? [? ?]]]]. subst.
    split; [|split; [|split]]; unfold Matrix in *.
    + split. 1: apply lt_plus_S_l. apply plus_lt_compat_l, lt_n_S, lt_plus_S_l.
    + intros. rename k0 into j. destruct (lt_eq_lt_dec j n) as [[? | ?] | ?].
      * now rewrite <- !dep_nth_app_1.
      * exfalso. now apply H.
      * decomp_lt_subst. clear H. destruct (lt_eq_lt_dec k0 m) as [[? | ?] | ?].
        -- now rewrite <- !dep_nth_app_2, <- !dep_nth_cons, <- !dep_nth_app_1.
        -- exfalso. apply H0. now subst.
        -- clear H0. rewrite <- !dep_nth_app_2. simpl. decomp_lt_subst.
           rewrite <- !dep_nth_app_2. now simpl.
    + rewrite dep_nth_app_cons, <- dep_nth_app_2. simpl. now rewrite dep_nth_app_cons.
    + rewrite dep_nth_app_cons, <- dep_nth_app_2. simpl. now rewrite dep_nth_app_cons.
Qed.

Lemma row_op_swap_det: forall i j {n: nat} (mat1 mat2: Matrix n n),
    row_op_swap i j mat1 mat2 -> det mat1 = (- det mat2)%R.
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [l ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst n.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_spec in H.
  destruct H as [? [? [? [? ?]]]]. subst. apply det_swap_row.
Qed.

Lemma row_op_swap_comm_mul:
  forall i j {m n l: nat} (A A': Matrix m n) (B: Matrix n l),
    row_op_swap i j A A' -> row_op_swap i j (mat_mul A B) (mat_mul A' B).
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [o ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_spec in H.
  destruct H as [? [? [? [? ?]]]]. subst. autorewrite with matrix.
  rewrite row_op_swap_spec. easy.
Qed.

Lemma row_op_swap_unique: forall i j {m n: nat} (mat mat1 mat2: Matrix m n),
    row_op_swap i j mat mat1 -> row_op_swap i j mat mat2 -> mat1 = mat2.
Proof.
  intros. pose proof H. destruct H1 as [[? ?] _]. decomp_lt_subst' H1.
  apply lt_exists_S_diff in H2. destruct H2 as [o ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H1. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_spec in H, H0.
  destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? [? [? ?]]]]. now subst.
Qed.

Lemma row_op_swap_exists: forall i j {m n: nat} (mat: Matrix m n),
    i < j < m -> exists mat', row_op_swap i j mat mat'.
Proof.
  intros. destruct H. decomp_lt_subst' H. apply lt_exists_S_diff in H0.
  destruct H0 as [o ?]. rewrite plus_assoc_reverse, plus_Sn_m in H. subst m.
  unfold Matrix in *. do 2 (dep_add_decomp; dep_list_decomp).
  exists (dep_app mat0 (dep_cons mat3 (dep_app mat1 (dep_cons mat2 mat5)))).
  rewrite row_op_swap_spec. easy.
Qed.

Lemma row_op_swap_cons: forall i j {m n: nat} (mat1 mat2: Matrix m n) v,
    row_op_swap i j mat1 mat2 ->
    row_op_swap (S i) (S j) (dep_cons v mat1) (dep_cons v mat2).
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [l ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite <- plus_Sn_m.
  rewrite dep_cons_app, (dep_cons_app v). rewrite row_op_swap_spec in H.
  destruct H as [? [? [? [? ?]]]]. subst.
  now rewrite (row_op_swap_spec (dep_cons v mat1) (dep_cons v mat1) mat6 mat6
                                    mat9 mat9 mat5 mat2 mat2 mat5).
Qed.

Lemma row_op_swap_cons_col: forall i j {m n: nat} (mat1 mat2: Matrix m n),
    row_op_swap i j mat1 mat2 ->
    row_op_swap i j (dep_list_binop (dep_cons (n := n)) vec_zero mat1)
                    (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [l ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_spec in H.
  rewrite vec_zero_app, vec_zero_cons, vec_zero_app, vec_zero_cons,
  !dep_list_binop_app, !dep_list_binop_cons, !dep_list_binop_app, !dep_list_binop_cons.
  destruct H as [? [? [? [? ?]]]]. subst. now rewrite row_op_swap_spec.
Qed.

Lemma row_op_swap_row_rev: forall i j {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_swap i j mat1 mat2 -> row_rev_rel mat1 mat3 -> row_rev_rel mat2 mat4 ->
    row_op_swap i j mat3 mat4.
Proof.
  intros. unfold row_op_swap, row_rev_rel in *. destruct H as [[? ?] [? [? ?]]].
  split; [|split; [|split]]; auto; intros; assert (i < m) by (eapply lt_trans; eauto).
  - destruct (le_lt_dec m k).
    + now rewrite !dep_nth_overflow.
    + specialize (H3 _ H6 H7). specialize (H0 _ vec_zero l).
      specialize (H1 _ vec_zero l). rewrite H3 in H0. eapply rev_rel_unique; eauto.
  - specialize (H0 _ vec_zero H6). specialize (H1 _ vec_zero H2). rewrite H4 in H0.
    eapply rev_rel_unique; eauto.
  - specialize (H0 _ vec_zero H2). specialize (H1 _ vec_zero H6). rewrite H5 in H0.
    eapply rev_rel_unique; eauto.
Qed.

Lemma row_op_swap_rev: forall i j {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_swap i j mat1 mat2 -> rev_rel mat1 mat3 -> rev_rel mat2 mat4 ->
    row_op_swap (m - 1 - j) (m - 1 - i) mat3 mat4.
Proof.
  intros. unfold row_op_swap, rev_rel in *. destruct H as [[? ?] [? [? ?]]].
  split; [|split; [|split]]; intros; assert (i < m) by (eapply lt_trans; eauto).
  - now apply ltlt_sub1_lt.
  - destruct (le_lt_dec m k). 1: now rewrite !dep_nth_overflow.
    pose proof (lt_sub_1_sub_lt _ _ l). specialize (H0 vec_zero _ H9).
    specialize (H1 vec_zero _ H9). rewrite lt_sub1_sub1_sub_eq in H0, H1; auto.
    assert (forall o, k <> m - 1 - o -> m - 1 - k <> o). {
      intros. intro. apply H10. subst o. now rewrite lt_sub1_sub1_sub_eq. }
    apply H10 in H6. apply H10 in H7. specialize (H3 _ H7 H6).
    now rewrite H0, H1 in H3.
  - specialize (H0 vec_zero _ H2). specialize (H1 vec_zero _ H6).
    now rewrite <- H0, <- H1.
  - specialize (H0 vec_zero _ H6). specialize (H1 vec_zero _ H2).
    now rewrite <- H0, <- H1.
Qed.

Lemma row_op_swap_dual_rev: forall i j {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_swap i j mat1 mat2 -> dual_rev_rel mat1 mat3 -> dual_rev_rel mat2 mat4 ->
    row_op_swap (m - 1 - j) (m - 1 - i) mat3 mat4.
Proof.
  intros. unfold dual_rev_rel in *. destruct H0 as [mat5 [? ?]].
  destruct H1 as [mat6 [? ?]]. assert (row_op_swap i j mat5 mat6) by
      (eapply row_op_swap_row_rev; eauto). eapply row_op_swap_rev; eauto.
Qed.

Definition row_op_add (a: R) (i j: nat) {m n: nat} (mat1 mat2: Matrix m n): Prop :=
  i < m /\ j < m /\ i <> j /\
  (forall k, k <> j -> dep_nth k mat1 vec_zero = dep_nth k mat2 vec_zero) /\
  dep_nth j mat2 vec_zero = vec_add (dep_nth j mat1 vec_zero)
                                    (vec_scal_mul a (dep_nth i mat1 vec_zero)).

Lemma row_op_add_spec_1:
  forall {n m l k: nat} (a: R) (m1 m2: Matrix n k) (m3 m4: Matrix m k)
         (m5 m6: Matrix l k) (v1 v2 v3 v4: Vector k),
    row_op_add a n (n + S m)
                   (dep_app m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5))))
                   (dep_app m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))) <->
    m1 = m2 /\ v1 = v2 /\ m3 = m4 /\ m5 = m6 /\ v4 = vec_add v3 (vec_scal_mul a v1).
Proof.
  intros; split; intros; destruct H as [? [? [? [? ?]]]].
  - unfold Matrix in *. split; [|split; [|split; [|split]]].
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_app_1 _ m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5)))),
      (dep_nth_app_1 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2. now apply Nat.lt_neq, Nat.lt_lt_add_r.
    + specialize (H2 _ H1). now rewrite !dep_nth_app_cons in H2.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_app_1 _ m3 (dep_cons v3 m5)),
      (dep_nth_app_1 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _  (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2. now apply neq_nSl_nSm, Nat.lt_neq.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_cons _ _ v3), (dep_nth_cons _ m6 v4),
      (dep_nth_app_2 _ m3), (dep_nth_app_2 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _ (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))).
      apply H2. apply neq_nSl_nSm, S_plus_neq.
    + now rewrite <- !dep_nth_app_2, <- !dep_nth_cons, !dep_nth_app_cons in H3.
  - subst. split; [|split; [|split; [|split]]].
    + apply lt_plus_S_l.
    + rewrite <- plus_Sn_m, Nat.add_assoc. apply lt_plus_S_l.
    + apply Nat.lt_neq, lt_plus_S_l.
    + intro j; intros. destruct (lt_eq_lt_dec j n) as [[? | ?] | ?].
      * now rewrite <- !dep_nth_app_1.
      * subst. now rewrite !dep_nth_app_cons.
      * decomp_lt_subst. destruct (lt_eq_lt_dec k0 m) as [[? | ?] | ?].
        -- now rewrite <- !dep_nth_app_2, <- !dep_nth_cons, <- !dep_nth_app_1.
        -- exfalso. apply H. now subst.
        -- clear H. rewrite <- !dep_nth_app_2. simpl. decomp_lt_subst.
           rewrite <- !dep_nth_app_2. now simpl.
    + rewrite !dep_nth_app_cons, <- !dep_nth_app_2. simpl.
      now rewrite !dep_nth_app_cons.
Qed.

Lemma row_op_add_spec_2:
  forall {n m l k: nat} (a: R) (m1 m2: Matrix n k) (m3 m4: Matrix m k)
         (m5 m6: Matrix l k) (v1 v2 v3 v4: Vector k),
    row_op_add a (n + S m) n
                   (dep_app m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5))))
                   (dep_app m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))) <->
    m1 = m2 /\ v3 = v4 /\ m3 = m4 /\ m5 = m6 /\ v2 = vec_add v1 (vec_scal_mul a v3).
Proof.
  intros; split; intros; destruct H as [? [? [? [? ?]]]].
  - unfold Matrix in *. split; [|split; [|split; [|split]]].
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_app_1 _ m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5)))),
      (dep_nth_app_1 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2. now apply Nat.lt_neq.
    + specialize (H2 _ H1).
      now rewrite <- !dep_nth_app_2, <- !dep_nth_cons, !dep_nth_app_cons in H2.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_app_1 _ m3 (dep_cons v3 m5)),
      (dep_nth_app_1 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _  (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2, not_eq_sym, Nat.lt_neq, lt_plus_S_l.
    + rewrite <- dep_nth_eq_iff. intros.
      rewrite (dep_nth_indep _ _ d1 vec_zero), (dep_nth_indep _ _ d2 vec_zero); auto.
      rewrite (dep_nth_cons _ _ v3), (dep_nth_cons _ m6 v4),
      (dep_nth_app_2 _ m3), (dep_nth_app_2 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _ (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))).
      apply H2, not_eq_sym, Nat.lt_neq, lt_plus_S_l.
    + now rewrite <- !dep_nth_app_2, <- !dep_nth_cons, !dep_nth_app_cons in H3.
  - subst. split; [|split; [|split; [|split]]].
    + rewrite <- plus_Sn_m, Nat.add_assoc. apply lt_plus_S_l.
    + apply lt_plus_S_l.
    + apply not_eq_sym, Nat.lt_neq, lt_plus_S_l.
    + intro j; intros. destruct (lt_eq_lt_dec j n) as [[? | ?] | ?].
      * now rewrite <- !dep_nth_app_1.
      * now subst.
      * decomp_lt_subst. clear H. destruct (lt_eq_lt_dec k0 m) as [[? | ?] | ?].
        -- now rewrite <- !dep_nth_app_2, <- !dep_nth_cons, <- !dep_nth_app_1.
        -- subst. now rewrite <- !dep_nth_app_2, <- !dep_nth_cons.
        -- rewrite <- !dep_nth_app_2. simpl. decomp_lt_subst.
           rewrite <- !dep_nth_app_2. now simpl.
    + rewrite !dep_nth_app_cons, <- !dep_nth_app_2. simpl.
      now rewrite dep_nth_app_cons.
Qed.

Lemma row_op_add_det: forall a i j {n: nat} (mat1 mat2: Matrix n n),
    row_op_add a i j mat1 mat2 -> det mat1 = det mat2.
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [l ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst n.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst. rewrite H0. now rewrite det_row_add_row_1.
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [l ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst n.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst. rewrite H3. now rewrite det_row_add_row_2.
Qed.

Lemma dep_map_dot_prod_add: forall {m n} (mat: Matrix m n) (v1 v2: Vector n),
    dep_map (vec_dot_prod (vec_add v1 v2)) mat =
    vec_add (dep_map (vec_dot_prod v1) mat) (dep_map (vec_dot_prod v2) mat).
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; simpl; autorewrite with vector.
  1: easy. now rewrite H, vec_dot_prod_add_r.
Qed.

Lemma dep_map_dot_prod_scal_mul: forall {m n} (mat: Matrix m n) (a: R) (v: Vector n),
    dep_map (vec_dot_prod (vec_scal_mul a v)) mat =
    vec_scal_mul a (dep_map (vec_dot_prod v) mat).
Proof.
  intros. revert m mat. apply dep_list_ind_1; intros; simpl; autorewrite with vector.
  1: easy. now rewrite H, vec_dot_prod_scal_l.
Qed.

Lemma row_op_add_comm_mul:
  forall a i j {m n l: nat} (A A': Matrix m n) (B: Matrix n l),
    row_op_add a i j A A' -> row_op_add a i j (mat_mul A B) (mat_mul A' B).
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst. autorewrite with matrix.
    now rewrite row_op_add_spec_1, dep_map_dot_prod_add, dep_map_dot_prod_scal_mul.
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst. autorewrite with matrix.
    now rewrite row_op_add_spec_2, dep_map_dot_prod_add, dep_map_dot_prod_scal_mul.
Qed.

Lemma row_op_add_unique: forall a i j {m n: nat} (mat mat1 mat2: Matrix m n),
    row_op_add a i j mat mat1 -> row_op_add a i j mat mat2 -> mat1 = mat2.
Proof.
  intros. pose proof H. destruct H1 as [? [? [? _]]]. apply not_eq in H3. destruct H3.
  - clear H1. decomp_lt_subst' H3. apply lt_exists_S_diff in H2. unfold Matrix in *.
    destruct H2 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H1. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_1 in H, H0.
    destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? [? [? ?]]]]. now subst.
  - clear H2. decomp_lt_subst' H3. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H1. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_2 in H, H0.
    destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? [? [? ?]]]]. now subst.
Qed.

Lemma row_op_add_exists: forall a i j {m n: nat} (mat: Matrix m n),
    i < m -> j < m -> i <> j -> exists mat', row_op_add a i j mat mat'.
Proof.
  intros. apply not_eq in H1. destruct H1.
  - clear H. decomp_lt_subst' H1. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H. subst m.
    do 2 (dep_add_decomp; dep_list_decomp).
    exists (dep_app
              mat0 (dep_cons
                      mat2 (dep_app
                              mat1 (dep_cons
                                      (vec_add mat3 (vec_scal_mul a mat2)) mat5)))).
    now rewrite row_op_add_spec_1.
  - clear H0. decomp_lt_subst' H1. apply lt_exists_S_diff in H. unfold Matrix in *.
    destruct H as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H. subst m.
    do 2 (dep_add_decomp; dep_list_decomp).
    exists (dep_app mat0 (dep_cons (vec_add mat2 (vec_scal_mul a mat3))
                                   (dep_app mat1 (dep_cons mat3 mat5)))).
    now rewrite row_op_add_spec_2.
Qed.

Lemma row_op_add_cons: forall a i j {m n: nat} (mat1 mat2: Matrix m n) v,
    row_op_add a i j mat1 mat2 ->
    row_op_add a (S i) (S j) (dep_cons v mat1) (dep_cons v mat2).
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite <- plus_Sn_m.
    rewrite dep_cons_app, (dep_cons_app v). rewrite row_op_add_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst.
    now rewrite (row_op_add_spec_1
                   a (dep_cons v mat1) (dep_cons v mat1) mat6 mat6 mat9 mat9
                   mat2 mat2 mat8 (vec_add mat8 (vec_scal_mul a mat2))).
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite <- plus_Sn_m.
    rewrite dep_cons_app, (dep_cons_app v). rewrite row_op_add_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst.
    now rewrite (row_op_add_spec_2
                   a (dep_cons v mat1) (dep_cons v mat1) mat6 mat6 mat9 mat9
                   mat4 (vec_add mat4 (vec_scal_mul a mat5)) mat5 mat5).
Qed.

Lemma row_op_add_cons_col: forall a i j {m n: nat} (mat1 mat2: Matrix m n),
    row_op_add a i j mat1 mat2 ->
    row_op_add a i j (dep_list_binop (dep_cons (n := n)) vec_zero mat1)
                   (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp).
    rewrite vec_zero_app, vec_zero_cons, vec_zero_app, vec_zero_cons,
    !dep_list_binop_app, !dep_list_binop_cons, !dep_list_binop_app,
    !dep_list_binop_cons. rewrite row_op_add_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst. rewrite row_op_add_spec_1.
    autorewrite with vector. now rewrite Rplus_0_l, Rmult_0_r.
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp).
    rewrite vec_zero_app, vec_zero_cons, vec_zero_app, vec_zero_cons,
    !dep_list_binop_app, !dep_list_binop_cons, !dep_list_binop_app,
    !dep_list_binop_cons. rewrite row_op_add_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst. rewrite row_op_add_spec_2.
    autorewrite with vector. now rewrite Rplus_0_l, Rmult_0_r.
Qed.

Lemma row_op_add_cons_Oi: forall
    {m n} a i (mat1 mat2: Matrix m n) (v1 v2: Vector n),
    row_op_add a O i (dep_cons v1 mat1) (dep_cons v2 mat2) ->
    v1 = v2 /\
    (forall d, dep_nth (i - 1) mat2 d =
               vec_add (dep_nth (i - 1) mat1 d) (vec_scal_mul a v1)) /\
    (forall j d, j <> i - 1 -> dep_nth j mat1 d = dep_nth j mat2 d).
Proof.
  intros. assert (forall (v: Vector n) (mat: Matrix m n),
                     dep_cons v mat = dep_app dep_nil (dep_cons v mat)) by (now simpl).
  rewrite H0, (H0 v2 mat2) in H. clear H0. pose proof H. destruct H0 as [_ [? [? _]]].
  destruct i. 1: exfalso; now apply H1. clear H1. simpl. rewrite <- minus_n_O.
  apply lt_S_n in H0. decomp_lt_subst. unfold Matrix in *. dep_add_decomp.
  dep_list_decomp. rewrite <- (plus_O_n (S i)) in H.
  pose proof (row_op_add_spec_1 a dep_nil dep_nil mat0 mat1 mat6 mat5 v1 v2 mat4
                                    mat2). rewrite H0 in H. clear H0.
  destruct H as [_ [? [? [? ?]]]]. subst. split; [|split]; intros; auto.
  - now rewrite !dep_nth_app_cons.
  - destruct (lt_eq_lt_dec j i) as [[? | ?] | ?].
    + now rewrite <- !dep_nth_app_1.
    + exfalso. now apply H.
    + clear H. decomp_lt_subst. rewrite <- !dep_nth_app_2. now simpl.
Qed.

Lemma row_op_add_cons_iO: forall
    {m n} a i (mat1 mat2: Matrix m n) (v1 v2: Vector n),
    row_op_add a i O (dep_cons v1 mat1) (dep_cons v2 mat2) ->
    v2 = vec_add v1 (vec_scal_mul a (dep_nth (i-1) mat1 vec_zero)) /\ mat1 = mat2.
Proof.
  intros. assert (forall (v: Vector n) (mat: Matrix m n),
                     dep_cons v mat = dep_app dep_nil (dep_cons v mat)) by (now simpl).
  rewrite H0, (H0 v2 mat2) in H. clear H0. pose proof H. destruct H0 as [? [_ [? _]]].
  destruct i. 1: exfalso; now apply H1. clear H1. simpl. rewrite <- minus_n_O.
  apply lt_S_n in H0. decomp_lt_subst. unfold Matrix in *. dep_add_decomp.
  dep_list_decomp. rewrite <- (plus_O_n (S i)) in H.
  pose proof (row_op_add_spec_2 a dep_nil dep_nil mat0 mat1 mat6 mat5 v1 v2 mat4
                                    mat2). rewrite H0 in H. clear H0.
  destruct H as [_ [? [? [? ?]]]]. subst. now rewrite dep_nth_app_cons.
Qed.

Lemma row_op_add_row_rev: forall a i j {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_add a i j mat1 mat2 -> row_rev_rel mat1 mat3 -> row_rev_rel mat2 mat4 ->
    row_op_add a i j mat3 mat4.
Proof.
  intros. unfold row_op_add, row_rev_rel in *. destruct H as [? [? [? [? ?]]]].
  split; [|split; [|split; [|split]]]; auto; intros.
  - destruct (le_lt_dec m k). 1: now rewrite !dep_nth_overflow.
    specialize (H4 _ H6). specialize (H0 _ vec_zero l). specialize (H1 _ vec_zero l).
    rewrite H4 in H0. eapply rev_rel_unique; eauto.
  - pose proof (H0 _ vec_zero H). specialize (H0 _ vec_zero H2).
    specialize (H1 _ vec_zero H2). apply (rev_rel_vec_scal_mul a) in H6.
    pose proof (rev_rel_vec_add H0 H6). clear H0 H6. rewrite <- H5 in H7.
    eapply rev_rel_unique; eauto.
Qed.

Lemma row_op_add_rev: forall a i j {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_add a i j mat1 mat2 -> rev_rel mat1 mat3 -> rev_rel mat2 mat4 ->
    row_op_add a (m - 1 - i) (m - 1 - j) mat3 mat4.
Proof.
  intros. unfold row_op_add, rev_rel in *. destruct H as [? [? [? [? ?]]]].
  split; [|split; [|split; [|split]]]; intros.
  - now apply lt_sub_1_sub_lt.
  - now apply lt_sub_1_sub_lt.
  - intro. apply H3. rewrite <- (lt_sub1_sub1_sub_eq i m); auto.
    rewrite <- (lt_sub1_sub1_sub_eq j m); [rewrite H6 |]; easy.
  - destruct (le_lt_dec m k). 1: now rewrite !dep_nth_overflow.
    pose proof (lt_sub_1_sub_lt _ _ l). specialize (H0 vec_zero _ H7).
    specialize (H1 vec_zero _ H7). rewrite lt_sub1_sub1_sub_eq in H0, H1; auto.
    assert (m - 1 - k <> j). {
      intro. apply H6. subst j. now rewrite lt_sub1_sub1_sub_eq. }
    specialize (H4 _ H8). now rewrite H0, H1 in H4.
  - pose proof (H0 vec_zero _ H). specialize (H0 vec_zero _ H2).
    specialize (H1 vec_zero _ H2). now rewrite <- H0, <- H1, <- H6.
Qed.

Lemma row_op_add_dual_rev: forall a i j {m n: nat} (mat1 mat2 mat3 mat4: Matrix m n),
    row_op_add a i j mat1 mat2 -> dual_rev_rel mat1 mat3 -> dual_rev_rel mat2 mat4 ->
    row_op_add a (m - 1 - i) (m - 1 - j) mat3 mat4.
Proof.
  intros. unfold dual_rev_rel in *. destruct H0 as [mat5 [? ?]].
  destruct H1 as [mat6 [? ?]]. assert (row_op_add a i j mat5 mat6) by
      (eapply row_op_add_row_rev; eauto). eapply row_op_add_rev; eauto.
Qed.

Inductive ElmtryRowOp: Set :=
| MultiplyRow: R -> nat -> ElmtryRowOp
| SwapRow: nat -> nat -> ElmtryRowOp
| AddRow: R -> nat -> nat -> ElmtryRowOp.

Fixpoint coeff_of_eros (l: list ElmtryRowOp): R :=
  match l with
  | nil => 1%R
  | MultiplyRow a _ :: l' => (/ a * coeff_of_eros l')%R
  | SwapRow _ _ :: l' => (- coeff_of_eros l')%R
  | AddRow _ _ _ :: l' => coeff_of_eros l'
  end.

Definition legal_ero (m: nat) (ero: ElmtryRowOp): Prop :=
  match ero with
  | MultiplyRow a i => a <> 0%R /\ i < m
  | SwapRow i j => i < j < m
  | AddRow a i j => i < m /\ j < m /\ i <> j
  end.

Inductive SeqElmtryRowOpRel {m n: nat}:
    Matrix m n -> list ElmtryRowOp -> Matrix m n -> Prop :=
| seror_nil: forall (mat: Matrix m n), SeqElmtryRowOpRel mat List.nil mat
| seror_mul_cons: forall (m1 m2 m3: Matrix m n) a i l,
    row_op_mul a i m1 m2 -> SeqElmtryRowOpRel m2 l m3 ->
    SeqElmtryRowOpRel m1 (MultiplyRow a i :: l) m3
| seror_swap_cons: forall (m1 m2 m3: Matrix m n) i j l,
    row_op_swap i j m1 m2 -> SeqElmtryRowOpRel m2 l m3 ->
    SeqElmtryRowOpRel m1 (SwapRow i j :: l) m3
| seror_add_cons: forall (m1 m2 m3: Matrix m n) a i j l,
    row_op_add a i j m1 m2 -> SeqElmtryRowOpRel m2 l m3 ->
    SeqElmtryRowOpRel m1 (AddRow a i j :: l) m3.

Lemma seror_det: forall {n: nat} (mat1 mat2: Matrix n n) (l: list ElmtryRowOp),
    SeqElmtryRowOpRel mat1 l mat2 -> det mat1 = (coeff_of_eros l * det mat2)%R.
Proof.
  intros. induction H; simpl.
  - ring.
  - apply row_op_mul_det in H. rewrite IHSeqElmtryRowOpRel in H. rewrite H. ring.
  - apply row_op_swap_det in H. rewrite IHSeqElmtryRowOpRel in H. rewrite H. ring.
  - apply row_op_add_det in H. rewrite IHSeqElmtryRowOpRel in H. rewrite H. ring.
Qed.

Lemma seror_comm_mul: forall {m n l: nat} (A A': Matrix m n) (B: Matrix n l) li,
    SeqElmtryRowOpRel A li A' -> SeqElmtryRowOpRel (mat_mul A B) li (mat_mul A' B).
Proof.
  intros. induction H.
  - constructor.
  - apply seror_mul_cons with (mat_mul m2 B); [apply row_op_mul_comm_mul|]; easy.
  - apply seror_swap_cons with (mat_mul m2 B); [apply row_op_swap_comm_mul|]; easy.
  - apply seror_add_cons with (mat_mul m2 B); [apply row_op_add_comm_mul|]; easy.
Qed.

Lemma seror_cons: forall {m n: nat} (mat1 mat2: Matrix m n) (v: Vector n) li,
    SeqElmtryRowOpRel mat1 li mat2 ->
    exists li', SeqElmtryRowOpRel (dep_cons v mat1) li' (dep_cons v mat2).
Proof.
  intros. induction H; [|destruct IHSeqElmtryRowOpRel..].
  - exists nil. constructor.
  - apply (row_op_mul_cons _ _ _ _ v) in H. exists (MultiplyRow a (S i) :: x).
    now apply seror_mul_cons with (dep_cons v m2).
  - apply (row_op_swap_cons _ _ _ _ v) in H. exists (SwapRow (S i) (S j) :: x).
    now apply seror_swap_cons with (dep_cons v m2).
  - apply (row_op_add_cons _ _ _ _ _ v) in H. exists (AddRow a (S i) (S j) :: x).
    now apply seror_add_cons with (dep_cons v m2).
Qed.

Lemma seror_cons_col: forall {m n: nat} (mat1 mat2: Matrix m n) li,
    SeqElmtryRowOpRel mat1 li mat2 ->
    SeqElmtryRowOpRel (dep_list_binop (dep_cons (n := n)) vec_zero mat1) li
                      (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. induction H.
  - constructor.
  - apply row_op_mul_cons_col in H.
    now apply seror_mul_cons with (dep_list_binop (dep_cons (n:=n)) vec_zero m2).
  - apply row_op_swap_cons_col in H.
    now apply seror_swap_cons with (dep_list_binop (dep_cons (n:=n)) vec_zero m2).
  - apply row_op_add_cons_col in H.
    now apply seror_add_cons with (dep_list_binop (dep_cons (n:=n)) vec_zero m2).
Qed.

Lemma seror_trans: forall {m n: nat} (m1 m2 m3: Matrix m n) l1 l2,
    SeqElmtryRowOpRel m1 l1 m2 -> SeqElmtryRowOpRel m2 l2 m3 ->
    SeqElmtryRowOpRel m1 (l1 ++ l2) m3.
Proof.
  intros. revert m1 m2 m3 l2 H H0.
  induction l1; intros; inversion H; subst; [|rewrite <- app_comm_cons..].
  - now simpl.
  - apply seror_mul_cons with m4; auto. apply IHl1 with m2; auto.
  - apply seror_swap_cons with m4; auto. apply IHl1 with m2; auto.
  - apply seror_add_cons with m4; auto. apply IHl1 with m2; auto.
Qed.

Lemma seror_app: forall {m n: nat} (m1 m3: Matrix m n) l1 l2,
    SeqElmtryRowOpRel m1 (l1 ++ l2) m3 -> exists m2,
      SeqElmtryRowOpRel m1 l1 m2 /\ SeqElmtryRowOpRel m2 l2 m3.
Proof.
  intros. revert m1 m3 l2 H. induction l1; intros.
  - exists m1. simpl in *. split; auto. constructor.
  - rewrite <- app_comm_cons in H.
    inversion H; subst; specialize (IHl1 _ _ _ H5); destruct IHl1 as [m4 [? ?]];
      exists m4; split; auto.
    + now apply seror_mul_cons with m2.
    + now apply seror_swap_cons with m2.
    + now apply seror_add_cons with m2.
Qed.

Lemma seror_exists: forall {m n: nat} (mat: Matrix m n) l,
    Forall (legal_ero m) l -> exists mat', SeqElmtryRowOpRel mat l mat'.
Proof.
  intros. revert mat. induction H; intros.
  - exists mat. constructor.
  - rename IHForall into IHl. destruct x; simpl in H.
    + destruct H. destruct (row_op_mul_exists _ _ mat H1 H) as [mat1 ?].
      destruct (IHl mat1) as [mat2 ?]. exists mat2.
      now apply seror_mul_cons with mat1.
    + destruct (row_op_swap_exists _ _ mat H) as [mat1 ?].
      destruct (IHl mat1) as [mat2 ?]. exists mat2.
      now apply seror_swap_cons with mat1.
    + destruct H as [? [? ?]].
      destruct (row_op_add_exists r _ _ mat H H1 H2) as [mat1 ?].
      destruct (IHl mat1) as [mat2 ?]. exists mat2. now apply seror_add_cons with mat1.
Qed.

Lemma mat_seror_O_S_col_some: forall
    {m n : nat} (mat1 mat2: Matrix m n) (a : R) (v1 : Vector n) (cv rv: Vector m)
    (v2 : Vector (S n)) (l : list nat) (f: nat -> R),
  NoDup l -> (forall i, In i l -> 1 <= i <= m) ->
  SeqElmtryRowOpRel
    (dep_cons (dep_cons a v1) (dep_list_binop (dep_cons (n:=n)) cv mat1))
    (map (fun i : nat => AddRow (f i) 0 i) l)
    (dep_cons v2 (dep_list_binop (dep_cons (n:=n)) rv mat2)) ->
  v2 = dep_cons a v1 /\
  forall i,
    (In i l -> dep_nth (i - 1) rv 0%R = (dep_nth (i - 1) cv 0%R + (f i) * a)%R /\
               dep_nth (i - 1) mat2 vec_zero =
               vec_add (dep_nth (i - 1) mat1 vec_zero) (vec_scal_mul (f i) v1)) /\
    (~ In i l -> 1 <= i -> dep_nth (i - 1) rv 0%R = dep_nth (i - 1) cv 0%R /\
                           dep_nth (i - 1) mat2 vec_zero =
                           dep_nth (i - 1) mat1 vec_zero).
Proof.
  intros. revert l cv mat1 mat2 H H0 H1. induction l; intros.
  - simpl in H1. inversion H1. apply inj_pair2_eq_dec in H5. 2: apply Nat.eq_dec.
    subst. apply dep_list_binop_cons_eq in H5. destruct H5. subst.
    split; intros; [|split; intros]; auto. inversion H2.
  - rename a0 into j. simpl in H1. inversion H1. subst. clear H1. unfold Matrix in *.
    dep_step_decomp m2. destruct (dep_vertical_split m1) as [cv1 [mat3 ?]]. subst m1.
    apply row_op_add_cons_Oi in H8. destruct H8 as [? [? ?]]. subst m0.
    rewrite NoDup_cons_iff in H. destruct H.
    assert (forall i : nat, In i l -> 1 <= i <= m) by (intros; apply H0; now right).
    specialize (IHl _ _ _ H1 H4 H9). destruct IHl. split; auto. intros.
    specialize (H2 (dep_cons 0%R vec_zero)). specialize (H6 i). destruct H6.
    rewrite !(dep_nth_list_binop _ _ _ _ 0%R vec_zero) in H2; auto.
    autorewrite with vector in H2. apply dep_cons_eq_inv in H2. destruct H2 as [? ?].
    assert (forall k, k <> j - 1 ->
                      dep_nth k cv 0%R = dep_nth k cv1 0%R /\
                      dep_nth k mat1 vec_zero = dep_nth k mat3 vec_zero). {
      intros. specialize (H3 k vec_zero H10).
      rewrite !(dep_nth_list_binop _ _ _ _ 0%R vec_zero) in H3; auto.
      apply dep_cons_eq_inv in H3. now destruct H3. } clear H3 H9. split; intros.
    + simpl in H3. unfold Vector in *. destruct H3.
      * subst. rewrite <- H2, <- H8. destruct (H0 _ (in_eq i l)). now apply H7.
      * specialize (H6 H3). destruct H6. rewrite H6, H9.
        specialize (H4 _ H3). destruct H4. specialize (H0 _ (in_eq j l)).
        destruct H0. assert (i - 1 <> j - 1). {
          intro. rewrite <- (Nat.add_cancel_r _ _ 1), !Nat.sub_add in H13; auto.
          subst. now apply H. } destruct (H10 _ H13). now rewrite H14, H15.
    + assert (~ In i l) by (intro; now apply H3, in_cons).
      assert (i - 1 <> j - 1). {
        intro. destruct (H0 _ (in_eq j l)).
        rewrite <- (Nat.add_cancel_r _ _ 1), !Nat.sub_add in H12; auto.
        subst. apply H3, in_eq. } destruct (H10 _ H12). destruct (H7 H11 H9).
      now rewrite H13, H14, H15, H16.
Qed.

Lemma mat_seror_clear_col_not_zero: forall
    {m n} (mat1: Matrix m n) (a: R) (v1: Vector n) (cv: Vector m),
    a <> 0%R ->
    exists l mat2,
      SeqElmtryRowOpRel
        (dep_cons (dep_cons a v1) (dep_list_binop (dep_cons (n := n)) cv mat1)) l
        (dep_cons (dep_cons a v1) (dep_list_binop (dep_cons (n := n)) vec_zero mat2)).
Proof.
  intros. remember (map (fun i => AddRow (-dep_nth (i-1) cv 0%R * / a) O i) (seq 1 m)).
  exists l. assert (Forall (legal_ero (S m)) l). {
    subst l. clear. rewrite Forall_forall. intros. rewrite in_map_iff in H.
    destruct H as [i [? ?]]. subst x. simpl. apply in_seq in H0.
    rewrite (Nat.add_1_l m) in H0. destruct H0.
    split; [|split]; [|easy|now apply lt_0_neq]. unfold lt. apply le_n_S, Nat.le_0_l. }
  destruct (seror_exists
              (dep_cons (dep_cons a v1) (dep_list_binop (dep_cons (n:=n)) cv mat1))
              _ H0) as [mat3 ?]. unfold Matrix in *. clear H0. dep_step_decomp mat3.
  destruct (dep_vertical_split mat2) as [v3 [mat' ?]]. subst mat2. subst l.
  assert (forall i : nat, In i (seq 1 m) -> 1 <= i <= m). {
    intros. rewrite in_seq in H0. destruct H0. split; auto. apply lt_n_Sm_le.
    now rewrite <- Nat.add_1_l. } pose proof H1.
  apply mat_seror_O_S_col_some in H1; auto. 2: apply seq_NoDup. destruct H1. subst.
  cut (v3 = vec_zero). 1: { intros; subst v3; now exists mat'. } clear -H3 H.
  rewrite <- dep_nth_eq_iff. intros. specialize (H3 (S i)). destruct H3.
  rewrite (dep_nth_indep _ _ d1 0%R); auto. rewrite (dep_nth_indep _ _ d2 0%R); auto.
  simpl in H1. rewrite Nat.sub_0_r, Rmult_assoc, Rinv_l, Rmult_1_r in H1; auto.
  rewrite Rplus_opp_r in H1. unfold vec_zero. rewrite dep_nth_repeat; auto.
  assert (In (S i) (seq 1 m)). {
    rewrite in_seq, (Nat.add_1_l m).
    split; [apply le_n_S, Nat.le_0_l | now apply lt_n_S]. } now destruct (H1 H3).
Qed.

Lemma mat_seror_clear_col_not_vec_zero: forall
    {m n} (mat1: Matrix m n) (v1: Vector (S n)) (cv: Vector m),
    cv <> vec_zero ->
    exists v2 l mat2,
      SeqElmtryRowOpRel
        (dep_cons v1 (dep_list_binop (dep_cons (n := n)) cv mat1)) l
        (dep_cons v2 (dep_list_binop (dep_cons (n := n)) vec_zero mat2)).
Proof.
  intros. unfold Vector in *. dep_list_decomp. rename v0 into a. rename v2 into v1.
  destruct (Req_dec a 0%R). apply vec_neq_zero in H. destruct H as [i [? ?]].
  2: exists (dep_cons a v1); now apply mat_seror_clear_col_not_zero. subst a.
  assert (exists mat3,
             row_op_add
               1%R (S i) O
               (dep_cons (dep_cons 0%R v1) (dep_list_binop (dep_cons (n:=n)) cv mat1))
               mat3). {
    apply row_op_add_exists; [now apply lt_n_S | apply Nat.lt_0_succ |].
    apply Nat.neq_succ_0. } destruct H0 as [mat3 ?]. unfold Matrix in *.
  dep_list_decomp. rename mat3 into a. rename mat4 into v2. pose proof H0.
  apply row_op_add_cons_iO in H2. destruct H2. simpl in H2.
  rewrite Nat.sub_0_r in H2. autorewrite with vector in H2.
  rewrite dep_nth_list_binop with (d1 := 0%R) (d2 := @vec_zero n) in H2; auto.
  autorewrite with vector in H2. apply dep_cons_eq_inv in H2. destruct H2 as [? _].
  rewrite Rplus_0_l in H2. rewrite <- H2 in H1. clear H2. subst mat2.
  destruct (mat_seror_clear_col_not_zero mat1 a v2 cv H1) as [l' [mat3 ?]].
  exists (dep_cons a v2), (AddRow 1 (S i) O :: l'), mat3.
  now apply seror_add_cons with
      (dep_cons (dep_cons a v2) (dep_list_binop (dep_cons (n:=n)) cv mat1)).
Qed.

Lemma mat_seror_upper_triangular: forall {n} (mat: Matrix n n),
    exists l ut, SeqElmtryRowOpRel mat l ut /\ upper_triangular ut.
Proof.
  induction n; intros; unfold Matrix in *.
  - dep_list_decomp. exists nil, {||}. split; constructor.
  - dep_step_decomp mat. pose proof (dep_list_transpose_involutive mat1).
    remember (dep_list_transpose mat1) in *. dep_step_decomp d. rewrite e in H.
    clear e. rewrite dep_transpose_cons_row in H.
    remember (dep_list_transpose d1) as mat2. clear d1 Heqmat2.
    assert
      (forall (v: dep_list R (S n)) (mat: dep_list (dep_list R n) n),
          exists l ut, SeqElmtryRowOpRel
                         (dep_cons v (dep_list_binop
                                        (dep_cons (n := n)) vec_zero mat)) l ut /\
                       upper_triangular ut). {
      intros. specialize (IHn mat). destruct IHn as [l [ut [? ?]]].
      apply seror_cons_col, (seror_cons _ _ v) in H0. destruct H0 as [li ?].
      exists li, (dep_cons v (dep_list_binop (dep_cons (n:=n)) vec_zero ut)).
      split; auto. constructor. apply H1. } subst mat1.
    destruct (vec_eq_dec d0 vec_zero).
    + subst d0. specialize (H0 mat0 mat2). apply H0.
    + rename mat0 into v. rename d0 into vv.
      destruct (mat_seror_clear_col_not_vec_zero mat2 v vv n0) as [v1 [l1 [mat1 ?]]].
      specialize (H0 v1 mat1). destruct H0 as [l2 [ut [? ?]]]. exists (l1 ++ l2), ut.
      split; auto. now apply seror_trans with
                       (dep_cons v1 (dep_list_binop (dep_cons (n:=n)) vec_zero mat1)).
Qed.

Lemma seror_dual_rev: forall {m n} (m1 m2 m3 m4: Matrix m n) l,
    SeqElmtryRowOpRel m1 l m2 -> dual_rev_rel m1 m3 -> dual_rev_rel m2 m4 ->
    exists l', SeqElmtryRowOpRel m3 l' m4.
Proof.
  intros. revert l m1 m2 m3 m4 H H0 H1. induction l; intros.
  - inversion H. subst. exists nil.
    assert (m3 = m4) by (eapply dual_rev_rel_unique; eauto). subst. constructor.
  - inversion H; subst; clear H; destruct (dual_rev_rel_exists m5) as [m6 ?];
      specialize (IHl _ _ _ _ H7 H H1); destruct IHl as [l2 ?].
    + pose proof (row_op_mul_dual_rev _ _ _ _ _ _ H5 H0 H).
      exists (MultiplyRow a0 (m - 1 - i) :: l2). now apply seror_mul_cons with m6.
    + pose proof (row_op_swap_dual_rev _ _ _ _ _ _ H5 H0 H).
      exists (SwapRow (m-1-j) (m-1-i) :: l2). now apply seror_swap_cons with m6.
    + pose proof (row_op_add_dual_rev _ _ _ _ _ _ _ H5 H0 H).
      exists (AddRow a0 (m-1-i) (m-1-j) :: l2). now apply seror_add_cons with m6.
Qed.

Lemma mat_seror_lower_triangular: forall {n} (mat: Matrix n n),
    exists l lowt, SeqElmtryRowOpRel mat l lowt /\ lower_triangular lowt.
Proof.
  intros. destruct (dual_rev_rel_exists mat) as [mat' ?].
  destruct (mat_seror_upper_triangular mat') as [l [ut [? ?]]].
  destruct (dual_rev_rel_exists ut) as [lowt ?]. apply dual_rev_rel_sym in H.
  destruct (seror_dual_rev _ _ _ _ _ H0 H H2) as [l' ?].
  pose proof (upper_dual_rev_lower _ _ H1 H2). now exists l', lowt.
Qed.

Theorem det_mul: forall {n} (A B: Matrix n n), det (mat_mul A B) = (det A * det B)%R.
Proof.
  intros. destruct (mat_seror_upper_triangular A) as [lA [utA [? ?]]].
  pose proof (seror_comm_mul _ _ B _ H). pose proof (seror_det _ _ _ H1).
  rewrite <- (det_transpose (mat_mul utA B)), mat_transpose_mul in H2.
  destruct (mat_seror_lower_triangular (mat_transpose B)) as [lB [ltB [? ?]]].
  pose proof (seror_comm_mul _ _ (mat_transpose utA) _ H3). rewrite H2.
  rewrite (seror_det _ _ _ H5), lower_triangular_det_mul; auto.
  2: red; now autorewrite with matrix. autorewrite with matrix.
  rewrite (seror_det _ _ _ H). apply seror_det in H3. autorewrite with matrix in H3.
  rewrite H3. ring.
Qed.

Inductive diag_sigT: {n: nat & Matrix n n} -> Prop :=
| DIAG_O: diag_sigT (existT _ O (@dep_nil (dep_list R 0)))
| DIAG_Sn: forall
    (n: nat) (m: Matrix n n) (a: R),
    diag_sigT (existT (fun x => Matrix x x) n m) ->
    diag_sigT (existT _ (S n)
                      (dep_cons (dep_cons a vec_zero)
                                (dep_list_binop (dep_cons (n := n)) vec_zero m))).

Definition diagonal_mat {n: nat} (mat: Matrix n n): Prop :=
  diag_sigT (existT (fun x => Matrix x x) n mat).

Lemma upper_lower_is_diag: forall {n} (mat: Matrix n n),
    upper_triangular mat -> lower_triangular mat -> diagonal_mat mat.
Proof.
  induction n; intro; unfold Matrix in *; intros; dep_list_decomp. 1: constructor.
  destruct (dep_vertical_split mat1) as [v2 [mat4 ?]]. subst. rename mat4 into mat1.
  rename mat3 into v1. rename mat2 into a. inversion H0; subst. clear H0.
  apply inj_pair2_eq_dec in H3. 2: exact Nat.eq_dec.
  autorewrite with matrix dep_list in H3. apply dep_cons_eq_inv in H3. destruct H3.
  apply dep_list_binop_cons_eq in H1. destruct H1. subst.
  inversion H; subst. do 2 (apply inj_pair2_eq_dec in H5; [|exact Nat.eq_dec]).
  apply dep_list_binop_cons_eq in H5. destruct H5. subst. clear v0 H3 H4.
  constructor. now apply IHn.
Qed.

Lemma diag_iff_upper_lower: forall {n} (mat: Matrix n n),
    diagonal_mat mat <-> upper_triangular mat /\ lower_triangular mat.
Proof.
  intros. split; intros. 2: destruct H; now apply upper_lower_is_diag. revert mat H.
  induction n; intros; unfold Matrix in *; dep_list_decomp. 1: split; constructor.
  inversion H. apply inj_pair2_eq_dec in H5. 2: exact Nat.eq_dec. subst. clear H2 H3.
  destruct (dep_vertical_split mat1) as [v [mat3 ?]]. subst. rename mat3 into mat1.
  do 2 (apply inj_pair2_eq_dec in H6; [|exact Nat.eq_dec]).
  apply dep_list_binop_cons_eq in H6. destruct H6. subst. apply IHn in H1. destruct H1.
  split. 1: now constructor. red. autorewrite with matrix dep_list. now constructor.
Qed.

Lemma mat_seror_clear_col_single: forall
    {m n} (mat: Matrix m n) (a: R) (v: Vector m),
    a <> 0%R ->
    exists l,
      SeqElmtryRowOpRel
        (dep_cons (dep_cons a vec_zero) (dep_list_binop (dep_cons (n := n)) v mat)) l
        (dep_cons (dep_cons a vec_zero)
                  (dep_list_binop (dep_cons (n := n)) vec_zero mat)).
Proof.
  intros. remember (map (fun i => AddRow (-dep_nth (i-1) v 0%R * / a) O i) (seq 1 m)).
  exists l. assert (Forall (legal_ero (S m)) l). {
    subst l. clear. rewrite Forall_forall. intros. rewrite in_map_iff in H.
    destruct H as [i [? ?]]. subst x. simpl. apply in_seq in H0.
    rewrite (Nat.add_1_l m) in H0. destruct H0.
    split; [|split]; [|easy|now apply lt_0_neq]. unfold lt. apply le_n_S, Nat.le_0_l. }
  destruct (seror_exists
              (dep_cons (dep_cons a vec_zero) (dep_list_binop (dep_cons (n:=n)) v mat))
              _ H0) as [mat3 ?]. unfold Matrix in *. clear H0. dep_step_decomp mat3.
  destruct (dep_vertical_split mat1) as [v3 [mat' ?]]. subst mat1. subst l.
  assert (forall i : nat, In i (seq 1 m) -> 1 <= i <= m). {
    intros. rewrite in_seq in H0. destruct H0. split; auto. apply lt_n_Sm_le.
    now rewrite <- Nat.add_1_l. } pose proof H1.
  apply mat_seror_O_S_col_some in H1; auto. 2: apply seq_NoDup. destruct H1. subst.
  cut (dep_list_binop (dep_cons (n:=n)) v3 mat' =
       dep_list_binop (dep_cons (n:=n)) vec_zero mat). 1: intros; now rewrite <- H1.
  clear -H3 H. rewrite <- dep_nth_eq_iff. intros. specialize (H3 (S i)).
  destruct H3 as [? _]. rewrite (dep_nth_indep _ _ d1 vec_zero); auto.
  rewrite (dep_nth_indep _ _ d2 vec_zero); auto. simpl in H1.
  rewrite Nat.sub_0_r, Rmult_assoc, Rinv_l, Rmult_1_r in H1; auto.
  autorewrite with vector in H1. rewrite Rplus_opp_r in H1.
  rewrite !(dep_nth_list_binop _ _ _ _ 0%R vec_zero); auto.
  assert (In (S i) (seq 1 m)). {
    rewrite in_seq, (Nat.add_1_l m).
    split; [apply le_n_S, Nat.le_0_l | now apply lt_n_S]. } specialize (H1 H2).
  destruct H1. f_equal. 2: apply H3. unfold vec_zero. now rewrite dep_nth_repeat.
Qed.

Lemma mat_seror_lower_to_diag: forall {n} (mat: Matrix n n),
    det mat <> 0%R -> lower_triangular mat ->
    exists l m, SeqElmtryRowOpRel mat l m /\ diagonal_mat m.
Proof.
  induction n; intros; unfold Matrix in *; dep_list_decomp.
  - exists nil, {||}. split; constructor.
  - rename mat2 into a. rename mat3 into v1. pose proof (lower_triangular_det _ H0).
    rewrite diag_cons in H1. destruct (dep_vertical_split mat1) as [v2 [mat2 ?]].
    subst. rename mat2 into mat. autorewrite with dep_list in H1. simpl dep_hd in H1.
    autorewrite with vector in H1. rewrite H1 in H. clear H1. red in H0.
    autorewrite with matrix dep_list in H0. inversion H0. subst.
    do 2 (apply inj_pair2_eq_dec in H5; [|exact Nat.eq_dec]). clear H0 v0 H3 H4.
    apply dep_list_binop_cons_eq in H5. destruct H5. subst.
    rewrite <- (lower_triangular_det _ H2) in H. apply Rmult_neq_0_reg in H.
    assert
      (exists l diam,
          SeqElmtryRowOpRel
            (dep_cons (dep_cons a vec_zero)
                      (dep_list_binop (dep_cons (n := n)) vec_zero mat)) l diam /\
          diagonal_mat diam). {
      intros. destruct H. specialize (IHn _ H0 H2). destruct IHn as [l' [m' [? ?]]].
      apply seror_cons_col, (seror_cons _ _ (dep_cons a vec_zero)) in H1.
      destruct H1 as [li ?].
      exists li, (dep_cons (dep_cons a vec_zero)
                           (dep_list_binop (dep_cons (n:=n)) vec_zero m')).
      split; auto. constructor. apply H3. } destruct H.
    destruct (mat_seror_clear_col_single mat a v2 H) as [l1 ?].
    destruct H0 as [l2 [dm [? ?]]]. exists (l1 ++ l2), dm. split; auto.
    now apply seror_trans with
        (dep_cons (dep_cons a vec_zero)
                  (dep_list_binop (dep_cons (n:=n)) vec_zero mat)).
Qed.

Lemma mat_seror_diag: forall {n} (mat: Matrix n n),
    det mat <> 0%R -> exists l m, SeqElmtryRowOpRel mat l m /\ diagonal_mat m.
Proof.
  intros. destruct (mat_seror_lower_triangular mat) as [l1 [lowt [? ?]]].
  rewrite (seror_det _ _ _ H0) in H. apply Rmult_neq_0_reg in H. destruct H.
  destruct (mat_seror_lower_to_diag _ H2 H1) as [l2 [mat' [? ?]]].
  exists (l1 ++ l2), mat'. split; auto. now apply seror_trans with lowt.
Qed.

Fixpoint diag_mat {n} (v: Vector n): Matrix n n :=
  match n as x return (x = n -> Matrix x x) with
  | O => fun _ => dep_nil
  | S m =>
    fun h1 =>
      match v in (dep_list _ s) return (s = n -> Matrix (S m) (S m)) with
      | dep_nil =>
        fun h2 => False_rect _ (eq_ind (S m) _ (fun h3 => (O_S m h3)) _ h1 h2)
      | @dep_cons _ n0 h l =>
        fun h2 =>
          eq_rec (S m) _
                 (fun _ (h3 : S n0 = S m) =>
                    eq_rec_r _
                             (fun l0 =>
                                dep_cons (dep_cons h vec_zero)
                                         (dep_list_binop (dep_cons (n:=m))
                                                         vec_zero (diag_mat l0)))
                             (eq_add_S _ _ h3) l) n h1 v h2
      end eq_refl
  end eq_refl.

Lemma diag_mat_cons: forall {n} (a: R) (v: Vector n),
    diag_mat (dep_cons a v) =
    dep_cons (dep_cons a vec_zero)
             (dep_list_binop (dep_cons (n:=n)) vec_zero (diag_mat v)).
Proof. intros. easy. Qed.

Lemma diag_mat_is_diag: forall {n} (v: Vector n), diagonal_mat (diag_mat v).
Proof.
  apply dep_list_ind_1; intros; [simpl | rewrite diag_mat_cons]; constructor; easy.
Qed.

Lemma identity_is_diag_mat: forall {n}, identity_mat = diag_mat (dep_repeat 1%R n).
Proof.
  induction n; intros. 1: now simpl. simpl dep_repeat. rewrite diag_mat_cons.
  simpl. rewrite IHn. f_equal.
Qed.

Lemma diagonal_diag_mat: forall {n} (v: Vector n), diagonal (diag_mat v) = v.
Proof.
  induction n; intros; unfold Vector in *; dep_list_decomp. 1: now simpl.
  rewrite diag_mat_cons, diag_cons. autorewrite with dep_list. simpl. now rewrite IHn.
Qed.

Lemma diagonal_mat_is_diag: forall {n} (m: Matrix n n),
    diagonal_mat m -> exists v, m = diag_mat v.
Proof.
  induction n; intros; unfold Matrix in *; dep_list_decomp.
  - exists dep_nil. now simpl.
  - destruct (dep_vertical_split m1) as [v2 [m4 ?]]. subst. red in H. inversion H.
    subst. clear H2 H3. apply inj_pair2_eq_dec in H5; [|exact Nat.eq_dec]. subst.
    do 2 (apply inj_pair2_eq_dec in H6; [|exact Nat.eq_dec]).
    apply dep_list_binop_cons_eq in H6. destruct H6. subst. specialize (IHn _ H1).
    destruct IHn. subst. exists (dep_cons m2 x). now rewrite diag_mat_cons.
Qed.

Lemma dep_map_dot_prod_zero: forall {m n : nat} (mat: Matrix m n),
    dep_map (vec_dot_prod vec_zero) mat = vec_zero.
Proof.
  intros. rewrite <- (vec_scal_mul_zero_r 0%R), dep_map_dot_prod_scal_mul.
  now autorewrite with vector.
Qed.

Hint Rewrite @dep_map_dot_prod_zero: matrix.

Lemma diag_mat_mul: forall {n} (v1 v2: Vector n),
    mat_mul (diag_mat v1) (diag_mat v2) = diag_mat (dep_list_binop Rmult v1 v2).
Proof.
  apply dep_list_ind_2; intros. 1: now simpl. autorewrite with dep_list.
  rewrite !diag_mat_cons. autorewrite with matrix vector dep_list. f_equal.
  - f_equal. 1: ring. rewrite dep_map_dot_prod_cons.
    now autorewrite with matrix vector.
  - rewrite mat_mul_col_cons_2. rewrite H. now autorewrite with matrix.
Qed.

Lemma dep_list_unit: forall {n: nat},
    dep_list_binop Rmult (dep_repeat 1%R n) (dep_repeat 1%R n) = dep_repeat 1%R n.
Proof.
  induction n; simpl. 1: easy. rewrite dep_list_binop_cons, IHn. f_equal. ring.
Qed.

Lemma row_op_mul_mat: forall a i {m n} (mat1 mat2: Matrix m n),
    row_op_mul a i mat1 mat2 ->
    exists (m1 m2: Matrix m m), mat2 = mat_mul m1 mat1 /\ mat_mul m1 m2 = identity_mat.
Proof.
  intros. pose proof H. destruct H0 as [? _]. decomp_lt_subst. unfold Matrix in *.
  dep_add_decomp. dep_list_decomp. apply row_op_mul_spec in H.
  destruct H as [?N [? [? ?]]]. subst.
  exists (diag_mat (dep_app (dep_repeat 1%R i) (dep_cons a (dep_repeat 1%R k)))),
  (diag_mat (dep_app (dep_repeat 1%R i) (dep_cons (Rinv a) (dep_repeat 1%R k)))).
  split.
  - induction i; intros; dep_list_decomp.
    + simpl dep_app. simpl Init.Nat.add. rewrite diag_mat_cons.
      autorewrite with matrix. rewrite <- identity_is_diag_mat.
      autorewrite with matrix. f_equal. rewrite dep_map_dot_prod_cons.
      now autorewrite with matrix vector.
    + simpl dep_repeat. simpl dep_app. rewrite (@diag_mat_cons (i + S k)).
      rewrite (mat_mul_cons
                 (dep_cons 1%R vec_zero)
                 (dep_list_binop
                    (dep_cons (n:=i + S k)) vec_zero
                    (diag_mat (dep_app (dep_repeat 1%R i)
                                       (dep_cons a (dep_repeat 1%R k)))))).
      f_equal; autorewrite with matrix vector. 2: now apply IHi.
      rewrite dep_map_dot_prod_cons. now autorewrite with matrix vector.
  - rewrite diag_mat_mul, dep_list_binop_app, dep_list_binop_cons,
    identity_is_diag_mat, dep_repeat_app. simpl dep_repeat. rewrite !dep_list_unit.
    now rewrite Rmult_comm, Rinv_l.
Qed.

Lemma mat_mul_zero_l: forall {m n l} (mat: Matrix n l),
    mat_mul (@zero_mat m n) mat = zero_mat.
Proof.
  induction m; intros; autorewrite with matrix; [|rewrite IHm]; easy.
Qed.

Hint Rewrite @mat_mul_zero_l: matrix.

Lemma mat_transpose_zero: forall {m n}, mat_transpose (@zero_mat m n) = zero_mat.
Proof.
  induction m; intros; autorewrite with matrix. 1: easy.
  rewrite IHm. now autorewrite with matrix.
Qed.

Hint Rewrite @mat_transpose_zero: matrix.

Lemma mat_mul_zero_r: forall {m n l} (mat: Matrix m n),
    mat_mul mat (@zero_mat n l) = zero_mat.
Proof.
  induction m; intros; unfold Matrix in *; dep_list_decomp; autorewrite with matrix.
  1: easy. rewrite IHm. f_equal. clear. induction l; intros; autorewrite with matrix.
  1: easy. simpl. rewrite IHl. now autorewrite with vector.
Qed.

Hint Rewrite @mat_mul_zero_r: matrix.

Lemma dep_map_dot_prod_app:
  forall {m n l} (v1: Vector m) (v2: Vector n) (mat1: Matrix l m) (mat2: Matrix l n),
    dep_map (vec_dot_prod (dep_app v1 v2)) (dep_list_binop dep_app mat1 mat2) =
    vec_add (dep_map (vec_dot_prod v1) mat1) (dep_map (vec_dot_prod v2) mat2).
Proof.
  induction m; intros; unfold Matrix, Vector in *; dep_list_decomp.
  - autorewrite with matrix vector. simpl. f_equal. clear.
    revert l mat1 mat2. apply dep_list_ind_2; intros; autorewrite with dep_list.
    1: easy. rewrite H. dep_list_decomp. f_equal.
  - destruct (dep_vertical_split mat1) as [v1 [mat3 ?]]. subst. simpl dep_app.
    rewrite dep_map_dot_prod_cons, vec_add_assoc, <- IHm, <- dep_cons_app_col.
    now rewrite (dep_map_dot_prod_cons (dep_list_binop dep_app mat3 mat2)).
Qed.

Lemma vec_neg_scal_mul: forall {n} (v: Vector n),
    vec_scal_mul (-1) v = vec_neg v.
Proof.
  apply dep_list_ind_1; intros; autorewrite with vector. 1: easy. rewrite H. f_equal.
  ring.
Qed.

Hint Rewrite @vec_neg_scal_mul: vector.

Lemma vec_neg_double: forall {n} (v: Vector n), vec_neg (vec_neg v) = v.
Proof.
  intros. rewrite <- !vec_neg_scal_mul, vec_scal_mul_assoc.
  assert (-1 * -1 = 1)%R by ring. rewrite H. now autorewrite with vector.
Qed.

Hint Rewrite @vec_neg_double: vector.

Lemma vec_neg_add: forall {n} (v1 v2: Vector n),
    vec_neg (vec_add v1 v2) = vec_add (vec_neg v1) (vec_neg v2).
Proof. intros. now rewrite <- !vec_neg_scal_mul, vec_scal_mul_add_distr_l. Qed.

Lemma dep_map_dot_prod_add':
  forall {m n : nat} (mat1 mat2 : Matrix m n) (v: Vector n),
  dep_map (vec_dot_prod v) (mat_add mat1 mat2) =
  vec_add (dep_map (vec_dot_prod v) mat1) (dep_map (vec_dot_prod v) mat2).
Proof.
  intros. revert m mat1 mat2.
  apply dep_list_ind_2; intros; autorewrite with matrix vector. 1: now simpl.
  simpl dep_map. autorewrite with vector. now rewrite H, vec_dot_prod_add_l.
Qed.

Lemma vec_add_app: forall {m n} (v1 v2: Vector m) (v3 v4: Vector n),
    vec_add (dep_app v1 v3) (dep_app v2 v4) = dep_app (vec_add v1 v2) (vec_add v3 v4).
Proof.
  induction m; intros; unfold Vector in *; dep_list_decomp; autorewrite with vector;
    auto. simpl dep_app. now rewrite (vec_add_cons v2 v0 (dep_app v6 v3)), IHm.
Qed.

Lemma zero_mat_app: forall {m n l}, zero_mat = dep_app (@zero_mat m l) (@zero_mat n l).
Proof.
  induction m; intros; autorewrite with matrix; simpl dep_app; [|rewrite <- IHm]; easy.
Qed.

Lemma row_op_swap_mat: forall i j {m n} (mat1 mat2: Matrix m n),
    row_op_swap i j mat1 mat2 ->
    exists (m1 m2: Matrix m m), mat2 = mat_mul m1 mat1 /\ mat_mul m1 m2 = identity_mat.
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [o ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_spec in H.
  destruct H as [? [? [? [? ?]]]]. subst.
  remember (mat_add
              identity_mat
              (dep_app
                 zero_mat
                 (dep_cons
                    (dep_app (@vec_zero i)
                             (dep_cons (-1)%R
                                       (dep_app (@vec_zero k)
                                                (dep_cons 1%R (@vec_zero o)))))
                    (dep_app zero_mat
                             (dep_cons
                                (dep_app
                                   vec_zero
                                   (dep_cons 1%R (dep_app vec_zero
                                                          (dep_cons (-1)%R vec_zero))))
                                zero_mat))))). exists m, m. subst. split.
  - rewrite mat_mul_add_distr_r. autorewrite with matrix. do 2 f_equal.
    + unfold mat_transpose. rewrite dep_transpose_app, dep_map_dot_prod_app.
      autorewrite with matrix vector. unfold mat_transpose. rewrite dep_transpose_app.
      rewrite dep_map_dot_prod_cons, dep_map_dot_prod_app.
      autorewrite with matrix vector. rewrite dep_map_dot_prod_cons.
      rewrite <- vec_add_assoc. now autorewrite with matrix vector.
    + do 2 f_equal. unfold mat_transpose.
      rewrite dep_transpose_app, dep_map_dot_prod_app.
      autorewrite with matrix vector. unfold mat_transpose. rewrite dep_transpose_app.
      rewrite dep_map_dot_prod_cons, dep_map_dot_prod_app.
      autorewrite with matrix vector. rewrite dep_map_dot_prod_cons.
      rewrite <- vec_add_assoc, (vec_add_comm mat2 mat5), vec_add_assoc.
      now autorewrite with matrix vector.
  - rewrite mat_mul_add_distr_r, mat_mul_add_distr_l, mat_add_assoc.
    autorewrite with matrix. rewrite !mat_transpose_add.
    unfold mat_transpose. rewrite !dep_transpose_app.
    rewrite !dep_map_dot_prod_add', !dep_map_dot_prod_app.
    autorewrite with matrix vector dep_list. unfold mat_transpose.
    rewrite !dep_transpose_app, !dep_map_dot_prod_cons, !dep_map_dot_prod_app.
    autorewrite with matrix vector. rewrite <- vec_add_assoc.
    autorewrite with matrix vector.
    pose proof (@mat_vec_mul_identity (i + S (k + S o))). unfold mat_vec_mul in H.
    rewrite !H. autorewrite with vector. rewrite !dep_map_dot_prod_cons.
    autorewrite with matrix vector. rewrite vec_add_assoc.
    rewrite <- (vec_add_assoc
                  _ (vec_neg
                       (dep_app vec_zero
                                (dep_cons (-1)%R
                                          (dep_app vec_zero
                                                   (dep_cons 1%R vec_zero)))))).
    autorewrite with vector.
    rewrite (vec_add_comm
               _
               (vec_neg
                  (dep_app vec_zero
                           (dep_cons 1%R
                                     (dep_app vec_zero (dep_cons (-1)%R vec_zero)))))).
    rewrite
      <- (vec_add_assoc
            _
            (vec_neg
               (dep_app vec_zero
                        (dep_cons 1%R
                                  (dep_app vec_zero (dep_cons (-1)%R vec_zero)))))).
    autorewrite with vector. do 2 rewrite !vec_add_app, !vec_add_cons.
    autorewrite with vector. rewrite Rplus_opp_r. assert (-1 + 1 = 0)%R by ring.
    rewrite H0. rewrite <- (mat_add_zero_r (@identity_mat (i + S (k + S o)))) at 2.
    f_equal. do 2 rewrite zero_mat_app, zero_mat_cons.
    do 2 rewrite vec_zero_app, vec_zero_cons. easy.
Qed.

Lemma row_op_add_mat: forall a i j {m n} (mat1 mat2: Matrix m n),
    row_op_add a i j mat1 mat2 ->
    exists (m1 m2: Matrix m m), mat2 = mat_mul m1 mat1 /\ mat_mul m1 m2 = identity_mat.
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [l ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst.
    exists (mat_add
              identity_mat
              (dep_app
                 zero_mat
                 (dep_cons
                    (dep_app vec_zero
                             (dep_cons 0%R
                                       (dep_app vec_zero (dep_cons 0%R vec_zero))))
                    (dep_app zero_mat
                             (dep_cons
                                (dep_app
                                   vec_zero
                                   (dep_cons a (dep_app vec_zero
                                                        (dep_cons 0%R vec_zero))))
                                zero_mat))))),
    (mat_add identity_mat
             (dep_app
                zero_mat
                (dep_cons
                   (dep_app vec_zero
                            (dep_cons 0%R
                                      (dep_app vec_zero (dep_cons 0%R vec_zero))))
                   (dep_app zero_mat
                            (dep_cons
                               (dep_app
                                  vec_zero
                                  (dep_cons (Ropp a) (dep_app vec_zero
                                                       (dep_cons 0%R vec_zero))))
                               zero_mat))))). split.
    + rewrite mat_mul_add_distr_r. autorewrite with matrix. do 2 f_equal.
      * unfold mat_transpose. rewrite dep_transpose_app, dep_map_dot_prod_app.
        autorewrite with matrix vector. unfold mat_transpose.
        rewrite dep_transpose_app, dep_map_dot_prod_cons, dep_map_dot_prod_app.
        now autorewrite with matrix vector.
      * do 2 f_equal. unfold mat_transpose.
        rewrite dep_transpose_app, dep_map_dot_prod_app.
        autorewrite with matrix vector. unfold mat_transpose.
        rewrite dep_transpose_app, dep_map_dot_prod_cons, dep_map_dot_prod_app.
        now autorewrite with matrix vector.
    + rewrite mat_mul_add_distr_r, mat_mul_add_distr_l, mat_add_assoc.
      autorewrite with matrix. rewrite !mat_transpose_add.
      unfold mat_transpose. rewrite !dep_transpose_app.
      rewrite !dep_map_dot_prod_add', !dep_map_dot_prod_app.
      autorewrite with matrix vector dep_list. unfold mat_transpose.
      rewrite !dep_transpose_app, !dep_map_dot_prod_cons, !dep_map_dot_prod_app.
      autorewrite with matrix vector. rewrite <- vec_add_assoc.
      pose proof (@mat_vec_mul_identity (i + S (k + S l))). unfold mat_vec_mul in H.
      rewrite !H. do 2 rewrite !vec_add_app, !vec_add_cons. autorewrite with vector.
      rewrite Rplus_0_r, Rplus_opp_l. do 2 rewrite <- vec_zero_cons, <- vec_zero_app.
      autorewrite with vector. do 2 rewrite <- zero_mat_cons, <- zero_mat_app.
      now autorewrite with matrix.
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [l ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst.
    exists (mat_add
              identity_mat
              (dep_app
                 zero_mat
                 (dep_cons
                    (dep_app vec_zero
                             (dep_cons 0%R
                                       (dep_app vec_zero (dep_cons a vec_zero))))
                    (dep_app zero_mat
                             (dep_cons
                                (dep_app
                                   vec_zero
                                   (dep_cons 0%R (dep_app vec_zero
                                                        (dep_cons 0%R vec_zero))))
                                zero_mat))))),
    (mat_add
       identity_mat
       (dep_app
          zero_mat
          (dep_cons
             (dep_app vec_zero
                      (dep_cons 0%R
                                (dep_app vec_zero (dep_cons (Ropp a) vec_zero))))
             (dep_app zero_mat
                      (dep_cons
                         (dep_app
                            vec_zero
                            (dep_cons 0%R (dep_app vec_zero
                                                   (dep_cons 0%R vec_zero))))
                         zero_mat))))). split.
    + rewrite mat_mul_add_distr_r. autorewrite with matrix. do 2 f_equal.
      * unfold mat_transpose. rewrite dep_transpose_app, dep_map_dot_prod_app.
        autorewrite with matrix vector. unfold mat_transpose.
        rewrite dep_transpose_app, dep_map_dot_prod_cons, dep_map_dot_prod_app.
        autorewrite with matrix vector. rewrite dep_map_dot_prod_cons.
        now autorewrite with matrix vector.
      * do 2 f_equal. unfold mat_transpose.
        rewrite dep_transpose_app, dep_map_dot_prod_app.
        autorewrite with matrix vector. unfold mat_transpose.
        rewrite dep_transpose_app, dep_map_dot_prod_cons, dep_map_dot_prod_app.
        now autorewrite with matrix vector.
    + rewrite mat_mul_add_distr_r, mat_mul_add_distr_l, mat_add_assoc.
      autorewrite with matrix. rewrite !mat_transpose_add.
      unfold mat_transpose. rewrite !dep_transpose_app.
      rewrite !dep_map_dot_prod_add', !dep_map_dot_prod_app.
      autorewrite with matrix vector dep_list. unfold mat_transpose.
      rewrite !dep_transpose_app, !dep_map_dot_prod_cons, !dep_map_dot_prod_app.
      autorewrite with matrix vector. rewrite <- vec_add_assoc.
      pose proof (@mat_vec_mul_identity (j + S (k + S l))). unfold mat_vec_mul in H.
      rewrite !H. do 2 rewrite !vec_add_app, !vec_add_cons. autorewrite with vector.
      rewrite Rplus_0_r, Rplus_opp_l. do 2 rewrite <- vec_zero_cons, <- vec_zero_app.
      autorewrite with vector. rewrite dep_map_dot_prod_cons.
      autorewrite with matrix vector. do 2 rewrite <- zero_mat_cons, <- zero_mat_app.
      now autorewrite with matrix.
Qed.

Lemma seror_mat: forall {m n} (m1 m2: Matrix m n) l,
    SeqElmtryRowOpRel m1 l m2 ->
    exists (mat1 mat2: Matrix m m), m2 = mat_mul mat1 m1 /\
                                    mat_mul mat1 mat2 = identity_mat.
Proof.
  intros. induction H.
  - exists identity_mat, identity_mat. now autorewrite with matrix.
  - destruct (row_op_mul_mat _ _ _ _ H) as [mat1 [mat2 [? ?]]]. subst.
    destruct IHSeqElmtryRowOpRel as [mat3 [mat4 [? ?]]].
    rewrite <- mat_mul_assoc in H1. exists (mat_mul mat3 mat1), (mat_mul mat2 mat4).
    split; auto. rewrite mat_mul_assoc, <- (mat_mul_assoc mat1), H2.
    now autorewrite with matrix.
  - destruct (row_op_swap_mat _ _ _ _ H) as [mat1 [mat2 [? ?]]]. subst.
    destruct IHSeqElmtryRowOpRel as [mat3 [mat4 [? ?]]].
    rewrite <- mat_mul_assoc in H1. exists (mat_mul mat3 mat1), (mat_mul mat2 mat4).
    split; auto. rewrite mat_mul_assoc, <- (mat_mul_assoc mat1), H2.
    now autorewrite with matrix.
  - destruct (row_op_add_mat _ _ _ _ _ H) as [mat1 [mat2 [? ?]]]. subst.
    destruct IHSeqElmtryRowOpRel as [mat3 [mat4 [? ?]]].
    rewrite <- mat_mul_assoc in H1. exists (mat_mul mat3 mat1), (mat_mul mat2 mat4).
    split; auto. rewrite mat_mul_assoc, <- (mat_mul_assoc mat1), H2.
    now autorewrite with matrix.
Qed.

Lemma diag_mat_det: forall {n} (v: Vector n), det (diag_mat v) = vec_prod v.
Proof.
  intros. rewrite upper_triangular_det.
  - now rewrite diagonal_diag_mat.
  - pose proof (diag_mat_is_diag v). rewrite diag_iff_upper_lower in H.
    now destruct H.
Qed.

Lemma diag_mat_left_inv: forall {n} (v: Vector n),
    vec_prod v <> 0%R -> exists v', mat_mul (diag_mat v') (diag_mat v) = identity_mat.
Proof.
  induction n; intros; unfold Vector in *; dep_list_decomp.
  - exists dep_nil. simpl. easy.
  - autorewrite with vector in H. apply Rmult_neq_0_reg in H. destruct H.
    destruct (IHn _ H0) as [v2 ?]. exists (dep_cons (/ v0)%R v2).
    rewrite !diag_mat_cons. autorewrite with matrix.
    rewrite dep_map_dot_prod_cons. autorewrite with matrix vector.
    rewrite Rinv_l; auto. simpl identity_mat. f_equal. rewrite mat_mul_col_cons_2.
    autorewrite with matrix. now rewrite H1.
Qed.

Lemma diag_mat_mul_comm: forall {n} (v1 v2: Vector n),
    mat_mul (diag_mat v1) (diag_mat v2) = mat_mul (diag_mat v2) (diag_mat v1).
Proof.
  intros. rewrite !diag_mat_mul. f_equal. apply dep_list_binop_comm, Rmult_comm.
Qed.

Lemma mat_left_inv_and_dinv_exists: forall {n} (mat: Matrix n n),
    det mat <> 0%R ->
    exists mat1 mat2, mat_mul mat1 mat = identity_mat /\
                      mat_mul mat1 mat2 = identity_mat.
Proof.
  intros. destruct (mat_seror_diag _ H) as [l [mat3 [? ?]]].
  destruct (seror_mat _ _ _ H0) as [mat4 [mat5 [? ?]]].
  destruct (diagonal_mat_is_diag _ H1) as [v ?].
  pose proof (seror_det _ _ _ H0). rewrite H5 in H. apply Rmult_neq_0_reg in H.
  destruct H as [_ ?]. rewrite H4, diag_mat_det in H. apply diag_mat_left_inv in H.
  destruct H as [v' ?]. rewrite H4 in H2. pose proof H.
  rewrite H2, <- mat_mul_assoc in H.
  exists (mat_mul (diag_mat v') mat4), (mat_mul mat5 (diag_mat v)). split; auto.
  rewrite mat_mul_assoc, <- (mat_mul_assoc mat4), H3. now autorewrite with matrix.
Qed.

Lemma mat_left_inv_exists: forall {n} (mat: Matrix n n),
    det mat <> 0%R -> exists matl, mat_mul matl mat = identity_mat.
Proof.
  intros. destruct (mat_left_inv_and_dinv_exists _ H) as [mat1 [mat2 [? _]]].
  now exists mat1.
Qed.

Lemma mat_mul_right: forall {m n l} (m3: Matrix n l) (m1 m2: Matrix m n),
    m1 = m2 -> mat_mul m1 m3 = mat_mul m2 m3. Proof. intros. now subst. Qed.

Lemma mat_mul_left: forall {m n l} (m1: Matrix m n) (m2 m3: Matrix n l),
    m2 = m3 -> mat_mul m1 m2 = mat_mul m1 m3. Proof. intros. now subst. Qed.

Lemma mat_mul_identity_det: forall {n} (mat1 mat2: Matrix n n),
    mat_mul mat1 mat2 = identity_mat -> det mat1 <> 0%R /\ det mat2 <> 0%R.
Proof.
  intros. pose proof (@det_identity n). rewrite <- H, det_mul in H0. split.
  - intro. rewrite H1, Rmult_0_l in H0. symmetry in H0. now apply R1_neq_R0 in H0.
  - intro. rewrite H1, Rmult_0_r in H0. symmetry in H0. now apply R1_neq_R0 in H0.
Qed.

Lemma mat_right_inv_exists: forall {n} (mat: Matrix n n),
    det mat <> 0%R -> exists matr, mat_mul mat matr = identity_mat.
Proof.
  intros. destruct (mat_left_inv_and_dinv_exists _ H) as [mat1 [mat2 [? ?]]].
  destruct (mat_mul_identity_det _ _ H0) as [? _].
  destruct (mat_left_inv_and_dinv_exists _ H2) as [mat3 [mat4 [? ?]]].
  apply (mat_mul_left mat3) in H0. rewrite <- mat_mul_assoc, H3 in H0.
  autorewrite with matrix in H0. subst. now exists mat4.
Qed.

Lemma mat_left_inv_unique: forall {n} (mat mat1 mat2: Matrix n n),
    mat_mul mat1 mat = identity_mat -> mat_mul mat2 mat = identity_mat -> mat1 = mat2.
Proof.
  intros. destruct (mat_mul_identity_det _ _ H) as [_ ?].
  destruct (mat_right_inv_exists _ H1). apply (mat_mul_right x) in H.
  apply (mat_mul_right x) in H0. rewrite mat_mul_assoc, H2 in H, H0.
  autorewrite with matrix in H, H0. now  subst mat1 mat2.
Qed.

Lemma mat_right_inv_unique: forall {n} (mat mat1 mat2: Matrix n n),
    mat_mul mat mat1 = identity_mat -> mat_mul mat mat2 = identity_mat -> mat1 = mat2.
Proof.
  intros. destruct (mat_mul_identity_det _ _ H) as [? _].
  destruct (mat_left_inv_exists _ H1). apply (mat_mul_left x) in H.
  apply (mat_mul_left x) in H0. rewrite <- mat_mul_assoc, H2 in H, H0.
  autorewrite with matrix in H, H0. now  subst mat1 mat2.
Qed.

Lemma mat_inv_exists: forall {n} (mat: Matrix n n),
    det mat <> 0%R -> exists imat, mat_mul imat mat = identity_mat /\
                                   mat_mul mat imat = identity_mat.
Proof.
  intros. destruct (mat_left_inv_exists _ H) as [mat1 ?].
  destruct (mat_right_inv_exists _ H) as [mat2 ?].
  pose proof (mat_left_right_inverse_eq _ _ _ H0 H1). subst. now exists mat2.
Qed.

Lemma mat_mul_identity_comm: forall {n} (A B: Matrix n n),
    mat_mul A B = identity_mat -> mat_mul B A = identity_mat.
Proof.
  intros. destruct (mat_mul_identity_det _ _ H).
  destruct (mat_inv_exists _ H0) as [invA [? ?]].
  pose proof (mat_right_inv_unique _ _ _ H3 H). now subst.
Qed.

Definition orthogonal_mat {n: nat} (mat: Matrix n n): Prop :=
  mat_mul (mat_transpose mat) mat = identity_mat.

Lemma orthogonal_mat_spec_1: forall {n} (mat: Matrix n n),
    orthogonal_mat mat <-> mat_mul (mat_transpose mat) mat = identity_mat.
Proof. intros. now unfold orthogonal_mat. Qed.

Lemma orthogonal_mat_spec_2: forall {n} (mat: Matrix n n),
    orthogonal_mat mat <-> mat_mul mat (mat_transpose mat) = identity_mat.
Proof. intros. unfold orthogonal_mat. split; apply mat_mul_identity_comm. Qed.

Lemma orthogonal_mat_det: forall {n} (mat: Matrix n n),
    orthogonal_mat mat -> det mat = 1%R \/ det mat = (-1)%R.
Proof.
  intros. red in H. pose proof (det_mul (mat_transpose mat) mat). rewrite H in H0.
  autorewrite with matrix in H0. rewrite Rmult_sqr in H0. symmetry in H0.
  apply Rsqr_eq. now rewrite Rsqr_1.
Qed.

(** * Special and Concrete Matrix *)

Local Ltac decomp_mat_eq :=
  repeat match goal with
         | H: dep_cons _ _ = dep_cons _ _ |- _ =>
           apply dep_cons_eq_inv in H; destruct H
         | H: dep_nil = dep_nil |- _ => clear H
         end.

Lemma orthogonal_mat_dim2: forall mat: Matrix 2 2,
    orthogonal_mat mat ->
    exists x, (- PI <= x <= PI)%R /\
              (mat = {|{|cos x; (- sin x)%R|}; {|sin x; cos x|}|} \/
               mat = {|{|cos x; sin x|}; {|sin x; (- cos x)%R|}|}).
Proof.
  intros. pose proof H. rewrite orthogonal_mat_spec_1 in H.
  rewrite orthogonal_mat_spec_2 in H0. unfold Matrix in mat. dep_list_decomp.
  rename mat3 into p. rename mat1 into q. rename mat0 into t. rename mat2 into u.
  vm_compute in H, H0. replace R0 with 0%R in H, H0 by now vm_compute.
  replace R1 with 1%R in H, H0 by now vm_compute. rewrite !Rplus_0_l in H, H0.
  decomp_mat_eq. clear H11 H5. rewrite !Rmult_sqr in *.
  destruct (Rsqr_sum_1_cos_sin _ _ H) as [x [? [? ?]]]. subst. exists x. split; auto.
  apply cos2_sum_1_sin in H0. apply sin2_sum_1_cos in H9. clear H3 H1.
  destruct H0, H9; subst; [| now right | now left |].
  - rewrite Rmult_comm, <- double in H7. apply Rmult_integral in H7.
    destruct H7. 1: exfalso; pose proof R2_neq_0; now apply H1.
    apply Rmult_integral in H0.
    destruct H0; rewrite H0, Ropp_0; [right | left]; easy.
  - rewrite Rmult_opp_opp, Rmult_comm, <- double in H7. apply Rmult_integral in H7.
    destruct H7. 1: exfalso; pose proof R2_neq_0; now apply H1.
    apply Rmult_integral in H0.
    destruct H0; rewrite H0, Ropp_0; [left | right]; easy.
Qed.
