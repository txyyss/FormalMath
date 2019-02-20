Require Export Coq.Reals.Reals.
Require Export FormalMath.lib.dep_list.

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

Lemma vec_add_id: forall {n} (v: Vector n), vec_add v vec_zero = v.
Proof.
  apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rplus_0_r.
Qed.

Definition vec_neg {n} (v: Vector n): Vector n := dep_map Ropp v.

Lemma vec_neg_cons: forall a {n} (v: Vector n),
    vec_neg (dep_cons a v) = dep_cons (- a)%R (vec_neg v).
Proof. intros. unfold vec_neg. now simpl. Qed.

Hint Rewrite @vec_neg_cons: vector.

Lemma vec_add_inv: forall {n} (v: Vector n), vec_add v (vec_neg v) = vec_zero.
Proof.
  apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rplus_opp_r.
Qed.

Definition vec_scal_mul (a: R) {n} (v: Vector n): Vector n := dep_map (Rmult a) v.

Lemma vec_scal_mul_nil: forall a, vec_scal_mul a dep_nil = dep_nil.
Proof. intros. unfold vec_scal_mul. now simpl. Qed.

Hint Rewrite vec_scal_mul_nil: vector.

Lemma vec_scal_mul_cons: forall f a {n} (v: Vector n),
    vec_scal_mul f (dep_cons a v) = dep_cons (f * a)%R (vec_scal_mul f v).
Proof. intros. unfold vec_scal_mul. now simpl. Qed.

Hint Rewrite @vec_scal_mul_cons : vector.

Lemma vec_scal_mul_one: forall {n} (v: Vector n), vec_scal_mul 1 v = v.
Proof.
  apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rmult_1_l.
Qed.

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

Definition vec_dot_prod {n} (v1 v2: Vector n) :=
  dep_fold_left Rplus (dep_list_binop Rmult v1 v2) 0%R.

Lemma vec_dot_prod_nil: vec_dot_prod dep_nil dep_nil = 0%R.
Proof. unfold vec_dot_prod. autorewrite with dep_list. simpl. easy. Qed.

Hint Rewrite vec_dot_prod_nil: vector.

Lemma vec_dot_prod_cons: forall a b {n} (v1 v2: Vector n),
    vec_dot_prod (dep_cons a v1) (dep_cons b v2) = (a * b + vec_dot_prod v1 v2)%R.
Proof.
  intros. unfold vec_dot_prod. autorewrite with dep_list. simpl.
  generalize (dep_list_binop Rmult v1 v2) as v. clear v1 v2.
  generalize (a * b)%R as r. clear a b. intros. rewrite Rplus_0_l. revert r.
  apply dep_list_ind_1 with (v := v); simpl; intros. 1: now rewrite Rplus_0_r.
  rewrite H, (H (0 + a)%R), Rplus_0_l. apply Rplus_assoc.
Qed.

Hint Rewrite @vec_dot_prod_cons: vector.

Lemma vec_dot_prod_comm: forall {n} (v1 v2: Vector n),
    vec_dot_prod v1 v2 = vec_dot_prod v2 v1.
Proof.
  apply dep_list_ind_2. 1: easy. intros. autorewrite with vector.
  now rewrite Rmult_comm, H.
Qed.

Lemma vec_dot_prod_add: forall {n} (a b c: Vector n),
    vec_dot_prod a (vec_add b c) = (vec_dot_prod a b + vec_dot_prod a c)%R.
Proof.
  apply dep_list_ind_3; intros; autorewrite with vector.
  - now rewrite Rplus_0_r.
  - rewrite H. rewrite Rmult_plus_distr_l, !Rplus_assoc. f_equal.
    rewrite <- !Rplus_assoc. f_equal. apply Rplus_comm.
Qed.

Lemma vec_dot_prod_scal_mul: forall a {n} (b c: Vector n),
    vec_dot_prod (vec_scal_mul a b) c = (a * (vec_dot_prod b c))%R.
Proof.
  intros a. apply dep_list_ind_2; intros; autorewrite with vector.
  - now rewrite Rmult_0_r.
  - now rewrite H, Rmult_assoc, Rmult_plus_distr_l.
Qed.

Definition preserve_vec_add {m n} (f: Vector m -> Vector n): Prop :=
  forall u v, f (vec_add u v) = vec_add (f u) (f v).

Definition preserve_vec_scal_mul {m n} (f: Vector m -> Vector n): Prop :=
  forall a v, f (vec_scal_mul a v) = vec_scal_mul a (f v).

Definition linear_map {m n} (f: Vector m -> Vector n): Prop :=
  preserve_vec_add f /\ preserve_vec_scal_mul f.

Definition Matrix (m n: nat) := dep_list (dep_list R n) m.

Definition mat_transpose {m n}: Matrix m n -> Matrix n m := dep_list_transpose.

Definition mat_neg {m n}: Matrix m n -> Matrix m n := dep_map vec_neg.

Definition mat_add {m n} (m1 m2: Matrix m n): Matrix m n :=
  dep_list_binop vec_add m1 m2.

Definition mat_scal_mul {m n} (a: R): Matrix m n -> Matrix m n :=
  dep_map (vec_scal_mul a).

Definition mat_mul {m l n} (m1: Matrix m l) (m2: Matrix l n): Matrix m n :=
  dep_map (fun row => dep_map (vec_dot_prod row) (mat_transpose m2)) m1.

Definition mat_vec_mul {m n} (mat: Matrix m n) (v: Vector n): Vector m :=
  dep_map (vec_dot_prod v) mat.

Lemma mat_transpose_involution: forall {m n} (mat: Matrix m n),
    mat_transpose (mat_transpose mat) = mat.
Proof. intros. apply dep_list_transpose_involution. Qed.

Hint Rewrite @mat_transpose_involution: matrix.

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

Lemma mat_transpose_cons: forall {m n} (v: Vector n) (mat: Matrix m n),
    mat_transpose (dep_cons v mat) =
    dep_list_binop (dep_cons (n:=m)) v (mat_transpose mat).
Proof. intros. unfold mat_transpose. now simpl. Qed.

Hint Rewrite @mat_transpose_cons: matrix.

Lemma mat_transpose_add: forall {m n} (m1 m2: Matrix m n),
    mat_transpose (mat_add m1 m2) = mat_add (mat_transpose m1) (mat_transpose m2).
Proof.
  intros. revert m m1 m2. apply dep_list_ind_2; intros; autorewrite with matrix.
  - unfold mat_transpose. simpl. induction n; simpl; autorewrite with matrix.
    1: easy. autorewrite with vector. now rewrite <- IHn.
  - rewrite H. clear H. generalize (mat_transpose v1) as m1.
    generalize (mat_transpose v2) as m2. intros. clear v1 v2. revert a b.
    apply dep_list_ind_2 with (v1 := m1) (v2 := m2); intros; autorewrite with matrix.
    + rewrite (dep_list_O_unique a), (dep_list_O_unique b).
      now autorewrite with dep_list.
    + destruct (dep_list_S_decompose a0) as [a1 [a2 ?]].
      destruct (dep_list_S_decompose b0) as [b1 [b2 ?]]. subst a0 b0.
      autorewrite with vector dep_list matrix. now rewrite H.
Qed.

Lemma mat_mul_add_distr_l: forall {m l n} (m1: Matrix m l) (m2 m3: Matrix l n),
    mat_mul m1 (mat_add m2 m3) = mat_add (mat_mul m1 m2) (mat_mul m1 m3).
Proof.
  intros. revert m m1. apply dep_list_ind_1; simpl; intros. 1: easy.
  unfold mat_mul in *. simpl. rewrite H. autorewrite with matrix. f_equal. clear H.
  rewrite mat_transpose_add. clear v n0. generalize (mat_transpose m2) as m1.
  clear m2. generalize (mat_transpose m3) as m2. clear m3. intros. revert n m1 m2.
  apply dep_list_ind_2; intros; autorewrite with matrix. 1: easy. simpl. rewrite H.
  autorewrite with vector. f_equal. apply vec_dot_prod_add.
Qed.

Lemma linear_map_mat_vec_mul_ext_eq: forall {n m} (f: Vector n -> Vector m),
    exists ! (mat: Matrix m n), forall (v: Vector n), f v = mat_vec_mul mat v.
Proof.
  
Abort.
