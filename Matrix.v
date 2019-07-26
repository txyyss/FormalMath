(** Lɪʙʀᴀʀʏ ᴏғ Mᴀᴛʀɪx Tʜᴇᴏʀʏ Bᴀsᴇᴅ ᴏɴ Dᴇᴘᴇɴᴅᴇɴᴛ Tʏᴘᴇs *)
(** Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

Require Export Coq.Reals.Reals.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Lists.List.
Require Export FormalMath.lib.Coqlib.
Require Export FormalMath.lib.dep_list.


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

Lemma vec_add_inv: forall {n} (v: Vector n), vec_add v (vec_neg v) = vec_zero.
Proof.
  apply dep_list_ind_1. 1: easy. intros. autorewrite with vector.
  now rewrite H, Rplus_opp_r.
Qed.

Lemma vec_add_neg_zero_iff: forall {n} (u v: Vector n),
    vec_add u (vec_neg v) = vec_zero <-> u = v.
Proof.
  apply dep_list_ind_2; intros; autorewrite with vector. 1: easy.
  split; intros; apply dep_cons_eq_inv in H0; destruct H0.
  - f_equal. 2: now rewrite <- H. apply Rplus_opp_r_uniq, Ropp_eq_compat in H0.
    rewrite !Ropp_involutive in H0. now subst.
  - rewrite <- H in H1. rewrite H1. f_equal. subst. apply Rplus_opp_r.
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

Definition preserve_vec_add {m n} (f: Vector m -> Vector n): Prop :=
  forall u v, f (vec_add u v) = vec_add (f u) (f v).

Definition preserve_vec_scal_mul {m n} (f: Vector m -> Vector n): Prop :=
  forall a v, f (vec_scal_mul a v) = vec_scal_mul a (f v).

Definition linear_map {m n} (f: Vector m -> Vector n): Prop :=
  preserve_vec_add f /\ preserve_vec_scal_mul f.

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
    apply dep_list_ind_1; intros; simpl. 1: easy. rewrite H. autorewrite with matrix.
    now simpl.
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

Definition zero_mat {m n}: Matrix m n := dep_repeat vec_zero m.

Lemma zero_mat_cons: forall {m n}, @zero_mat (S m) n = dep_cons vec_zero zero_mat.
Proof. intros; unfold zero_mat. now simpl. Qed.

Hint Rewrite @zero_mat_cons: matrix.

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
  1: easy. rewrite H. autorewrite with vector. clear.
  induction m; autorewrite with matrix vector dep_list. 1: easy. unfold Vector.
  now rewrite IHm.
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

Lemma linear_map_mat_iff: forall {n m} (f: Vector n -> Vector m),
    linear_map f <->
    exists ! mat: Matrix m n, forall v, f v = mat_vec_mul mat v.
Proof.
  intros. split; intros.
  - exists (mat_transpose (dep_map f identity_mat)).
    assert (forall v, f v = mat_vec_mul (mat_transpose (dep_map f identity_mat)) v) by
        (intro; rewrite <- linear_map_mat; auto; now autorewrite with matrix).
    split; auto. intros m2 ?. apply mat_vec_mul_unique. intros.
    now rewrite <- H0, <- H1.
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

Lemma preserve_dot_prod_mat: forall {m n} (f: Vector n -> Vector m),
    preserve_dot_prod f <->
    exists ! mat: Matrix m n,
      mat_mul (mat_transpose mat) mat = identity_mat /\
      forall v, f v = mat_vec_mul mat v.
Proof.
  intros. split; intros.
  - pose proof H. apply preserve_dot_prod_linear in H0.
    rewrite linear_map_mat_iff in H0. destruct H0 as [mat [? ?]]. exists mat.
    split; [split|]; auto.
    + red in H.
      assert (forall u v,
                 vec_dot_prod (mat_vec_mul (mat_mul (mat_transpose mat) mat) u) v =
                 vec_dot_prod u v) by
          (intros; now rewrite <- vec_dot_prod_mul, <- !H0).
      apply mat_vec_mul_unique. intros u. autorewrite with matrix.
      now apply vec_dot_prod_unique.
    + intros. destruct H2. now apply H1.
  - destruct H as [mat [[? ?] ?]]. pose proof (mat_vec_mul_preserve_dot_prod _ H).
    red in H2 |-* . intros. now rewrite !H0.
Qed.

Lemma sq_mat_left_right_inverse_eq: forall {n} (A B C: Matrix n n),
    mat_mul B A = identity_mat -> mat_mul A C = identity_mat -> B = C.
Proof.
  intros. pose proof (mat_mul_assoc B A C). rewrite H, H0 in H1.
  now autorewrite with matrix in H1.
Qed.

(** * Square Matrix Theory *)

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

(** * Elementary Row Operations *)

Definition row_op_mul_row (a: R) (i: nat) {m n: nat} (mat1 mat2: Matrix m n): Prop :=
  i < m /\ a <> 0%R /\
  (forall j, j <> i -> dep_nth j mat1 vec_zero = dep_nth j mat2 vec_zero) /\
  dep_nth i mat2 vec_zero = vec_scal_mul a (dep_nth i mat1 vec_zero).

Lemma row_op_mul_row_spec:
  forall (a: R) {m n l: nat} (mat1 mat2: Matrix m l) (mat3 mat4: Matrix n l)
         (v1 v2: Vector l),
    row_op_mul_row a m (dep_app mat1 (dep_cons v1 mat3))
                   (dep_app mat2 (dep_cons v2 mat4)) <->
    a <> 0%R /\ mat1 = mat2 /\ v2 = vec_scal_mul a v1 /\ mat3 = mat4.
Proof.
  intros. split; intros; destruct H as [? [? [? ?]]].
  - split; [|split; [|split]]; unfold Matrix in *; auto.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
      rewrite (dep_nth_app_1 _ mat1 (dep_cons v1 mat3)); auto.
      rewrite (dep_nth_app_1 _ mat2 (dep_cons v2 mat4)); auto.
      now apply H1, Nat.lt_neq.
    + now rewrite !dep_nth_app_cons in H2.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
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

Lemma row_op_mul_row_det: forall a i {n: nat} (mat1 mat2: Matrix n n),
    row_op_mul_row a i mat1 mat2 -> det mat1 = (/ a * det mat2)%R.
Proof.
  intros. pose proof H. destruct H as [? _]. decomp_lt_subst.
  unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  apply row_op_mul_row_spec in H0. destruct H0 as [? [? [? ?]]]. subst.
  rewrite det_row_mul, <- Rmult_assoc, <- Rinv_l_sym, Rmult_1_l; auto.
Qed.

Lemma row_op_mul_row_comm_mul:
  forall a i {m n l: nat} (A A': Matrix m n) (B: Matrix n l),
    row_op_mul_row a i A A' -> row_op_mul_row a i (mat_mul A B) (mat_mul A' B).
Proof.
  intros. pose proof H. destruct H as [? _]. decomp_lt_subst.
  unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  apply row_op_mul_row_spec in H0. destruct H0 as [? [? [? ?]]]. subst.
  autorewrite with matrix. rewrite row_op_mul_row_spec. split;[|split;[|split]]; auto.
  unfold vec_scal_mul at 2. rewrite dep_map_nest. apply dep_map_ext. intros.
  apply vec_dot_prod_scal_l.
Qed.

Lemma row_op_mul_row_unique: forall a i {m n: nat} (mat mat1 mat2: Matrix m n),
    row_op_mul_row a i mat mat1 -> row_op_mul_row a i mat mat2 -> mat1 = mat2.
Proof.
  intros. pose proof H. destruct H1 as [? _]. decomp_lt_subst.
  unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  rewrite row_op_mul_row_spec in H, H0. destruct H0 as [? [? [? ?]]].
  destruct H as [? [? [? ?]]]. now subst.
Qed.

Lemma row_op_mul_row_exists: forall a i {m n: nat} (mat: Matrix m n),
    i < m -> a <> 0%R -> exists mat', row_op_mul_row a i mat mat'.
Proof.
  intros. decomp_lt_subst. unfold Matrix in *. dep_add_decomp. dep_list_decomp.
  exists (dep_app mat0 (dep_cons (vec_scal_mul a mat2) mat3)).
  rewrite row_op_mul_row_spec. easy.
Qed.

Lemma row_op_mul_row_cons: forall a i {m n: nat} (mat1 mat2: Matrix m n) v,
    row_op_mul_row a i mat1 mat2 ->
    row_op_mul_row a (S i) (dep_cons v mat1) (dep_cons v mat2).
Proof.
  intros. pose proof H. destruct H0 as [? _]. decomp_lt_subst. unfold Matrix in *.
  dep_add_decomp. dep_list_decomp. rewrite row_op_mul_row_spec in H.
  destruct H as [? [? [? ?]]]. subst. rewrite !dep_cons_app.
  now rewrite (row_op_mul_row_spec a (dep_cons v mat1) (dep_cons v mat1) mat5 mat5).
Qed.

Lemma row_op_mul_row_cons_col: forall a i {m n: nat} (mat1 mat2: Matrix m n),
    row_op_mul_row a i mat1 mat2 ->
    row_op_mul_row a i (dep_list_binop (dep_cons (n := n)) vec_zero mat1)
                   (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. pose proof H. destruct H0 as [? _]. decomp_lt_subst. unfold Matrix in *.
  rewrite vec_zero_app, vec_zero_cons. dep_add_decomp. dep_list_decomp.
  rewrite !dep_list_binop_app, !dep_list_binop_cons. rewrite row_op_mul_row_spec in *.
  destruct H as [? [? [? ?]]]. subst. autorewrite with vector. now rewrite Rmult_0_r.
Qed.

Definition row_op_swap_row (i j: nat) {m n: nat} (mat1 mat2: Matrix m n): Prop :=
  i < j < m /\
  (forall k, k <> i -> k <> j -> dep_nth k mat1 vec_zero = dep_nth k mat2 vec_zero) /\
  dep_nth i mat1 vec_zero = dep_nth j mat2 vec_zero /\
  dep_nth j mat1 vec_zero = dep_nth i mat2 vec_zero.

Lemma row_op_swap_row_spec:
  forall {n m l k: nat} (m1 m2: Matrix n k) (m3 m4: Matrix m k)
         (m5 m6: Matrix l k) (v1 v2 v3 v4: Vector k),
    row_op_swap_row n (n + S m)
                    (dep_app m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5))))
                    (dep_app m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))) <->
    m1 = m2 /\ m3 = m4 /\ m5 = m6 /\ v1 = v4 /\ v3 = v2.
Proof.
  intros. split; intros.
  - destruct H as [? [? [? ?]]]. split; [|split;[|split;[|split]]]; unfold Matrix in *.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
      rewrite (dep_nth_app_1 _ m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5)))),
      (dep_nth_app_1 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H0; apply Nat.lt_neq; [|apply Nat.lt_lt_add_r]; easy.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
      rewrite (dep_nth_app_1 _ m3 (dep_cons v3 m5)),
      (dep_nth_app_1 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _  (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H0. 1: apply S_plus_neq. now apply neq_nSl_nSm, Nat.lt_neq.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
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

Lemma row_op_swap_row_det: forall i j {n: nat} (mat1 mat2: Matrix n n),
    row_op_swap_row i j mat1 mat2 -> det mat1 = (- det mat2)%R.
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [l ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst n.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_row_spec in H.
  destruct H as [? [? [? [? ?]]]]. subst. apply det_swap_row.
Qed.

Lemma row_op_swap_row_comm_mul:
  forall i j {m n l: nat} (A A': Matrix m n) (B: Matrix n l),
    row_op_swap_row i j A A' -> row_op_swap_row i j (mat_mul A B) (mat_mul A' B).
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [o ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_row_spec in H.
  destruct H as [? [? [? [? ?]]]]. subst. autorewrite with matrix.
  rewrite row_op_swap_row_spec. easy.
Qed.

Lemma row_op_swap_row_unique: forall i j {m n: nat} (mat mat1 mat2: Matrix m n),
    row_op_swap_row i j mat mat1 -> row_op_swap_row i j mat mat2 -> mat1 = mat2.
Proof.
  intros. pose proof H. destruct H1 as [[? ?] _]. decomp_lt_subst' H1.
  apply lt_exists_S_diff in H2. destruct H2 as [o ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H1. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_row_spec in H, H0.
  destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? [? [? ?]]]]. now subst.
Qed.

Lemma row_op_swap_row_exists: forall i j {m n: nat} (mat: Matrix m n),
    i < j < m -> exists mat', row_op_swap_row i j mat mat'.
Proof.
  intros. destruct H. decomp_lt_subst' H. apply lt_exists_S_diff in H0.
  destruct H0 as [o ?]. rewrite plus_assoc_reverse, plus_Sn_m in H. subst m.
  unfold Matrix in *. do 2 (dep_add_decomp; dep_list_decomp).
  exists (dep_app mat0 (dep_cons mat3 (dep_app mat1 (dep_cons mat2 mat5)))).
  rewrite row_op_swap_row_spec. easy.
Qed.

Lemma row_op_swap_row_cons: forall i j {m n: nat} (mat1 mat2: Matrix m n) v,
    row_op_swap_row i j mat1 mat2 ->
    row_op_swap_row (S i) (S j) (dep_cons v mat1) (dep_cons v mat2).
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [l ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite <- plus_Sn_m.
  rewrite dep_cons_app, (dep_cons_app v). rewrite row_op_swap_row_spec in H.
  destruct H as [? [? [? [? ?]]]]. subst.
  now rewrite (row_op_swap_row_spec (dep_cons v mat1) (dep_cons v mat1) mat6 mat6
                                    mat9 mat9 mat5 mat2 mat2 mat5).
Qed.

Lemma row_op_swap_row_cons_col: forall i j {m n: nat} (mat1 mat2: Matrix m n),
    row_op_swap_row i j mat1 mat2 ->
    row_op_swap_row i j (dep_list_binop (dep_cons (n := n)) vec_zero mat1)
                    (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. pose proof H. destruct H0 as [[? ?] _]. decomp_lt_subst' H0.
  apply lt_exists_S_diff in H1. destruct H1 as [l ?]. unfold Matrix in *.
  rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
  do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_swap_row_spec in H.
  rewrite vec_zero_app, vec_zero_cons, vec_zero_app, vec_zero_cons,
  !dep_list_binop_app, !dep_list_binop_cons, !dep_list_binop_app, !dep_list_binop_cons.
  destruct H as [? [? [? [? ?]]]]. subst. now rewrite row_op_swap_row_spec.
Qed.

Definition row_op_add_row (a: R) (i j: nat) {m n: nat} (mat1 mat2: Matrix m n): Prop :=
  i < m /\ j < m /\ i <> j /\
  (forall k, k <> j -> dep_nth k mat1 vec_zero = dep_nth k mat2 vec_zero) /\
  dep_nth j mat2 vec_zero = vec_add (dep_nth j mat1 vec_zero)
                                    (vec_scal_mul a (dep_nth i mat1 vec_zero)).

Lemma row_op_add_row_spec_1:
  forall {n m l k: nat} (a: R) (m1 m2: Matrix n k) (m3 m4: Matrix m k)
         (m5 m6: Matrix l k) (v1 v2 v3 v4: Vector k),
    row_op_add_row a n (n + S m)
                   (dep_app m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5))))
                   (dep_app m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))) <->
    m1 = m2 /\ v1 = v2 /\ m3 = m4 /\ m5 = m6 /\ v4 = vec_add v3 (vec_scal_mul a v1).
Proof.
  intros; split; intros; destruct H as [? [? [? [? ?]]]].
  - unfold Matrix in *. split; [|split; [|split; [|split]]].
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
      rewrite (dep_nth_app_1 _ m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5)))),
      (dep_nth_app_1 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2. now apply Nat.lt_neq, Nat.lt_lt_add_r.
    + specialize (H2 _ H1). now rewrite !dep_nth_app_cons in H2.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
      rewrite (dep_nth_app_1 _ m3 (dep_cons v3 m5)),
      (dep_nth_app_1 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _  (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2. now apply neq_nSl_nSm, Nat.lt_neq.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
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

Lemma row_op_add_row_spec_2:
  forall {n m l k: nat} (a: R) (m1 m2: Matrix n k) (m3 m4: Matrix m k)
         (m5 m6: Matrix l k) (v1 v2 v3 v4: Vector k),
    row_op_add_row a (n + S m) n
                   (dep_app m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5))))
                   (dep_app m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))) <->
    m1 = m2 /\ v3 = v4 /\ m3 = m4 /\ m5 = m6 /\ v2 = vec_add v1 (vec_scal_mul a v3).
Proof.
  intros; split; intros; destruct H as [? [? [? [? ?]]]].
  - unfold Matrix in *. split; [|split; [|split; [|split]]].
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
      rewrite (dep_nth_app_1 _ m1 (dep_cons v1 (dep_app m3 (dep_cons v3 m5)))),
      (dep_nth_app_1 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2. now apply Nat.lt_neq.
    + specialize (H2 _ H1).
      now rewrite <- !dep_nth_app_2, <- !dep_nth_cons, !dep_nth_app_cons in H2.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
      rewrite (dep_nth_app_1 _ m3 (dep_cons v3 m5)),
      (dep_nth_app_1 _ m4 (dep_cons v4 m6)),
      (dep_nth_cons _ _ v1), (dep_nth_cons _  (dep_app m4 (dep_cons v4 m6)) v2),
      (dep_nth_app_2 _ m1),
      (dep_nth_app_2 _ m2 (dep_cons v2 (dep_app m4 (dep_cons v4 m6)))); auto.
      apply H2, not_eq_sym, Nat.lt_neq, lt_plus_S_l.
    + rewrite <- dep_nth_eq_iff with (d1 := vec_zero) (d2 := vec_zero). intros.
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

Lemma row_op_add_row_det: forall a i j {n: nat} (mat1 mat2: Matrix n n),
    row_op_add_row a i j mat1 mat2 -> det mat1 = det mat2.
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [l ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst n.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_row_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst. rewrite H0. now rewrite det_row_add_row_1.
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [l ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst n.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_row_spec_2 in H.
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

Lemma row_op_add_row_comm_mul:
  forall a i j {m n l: nat} (A A': Matrix m n) (B: Matrix n l),
    row_op_add_row a i j A A' -> row_op_add_row a i j (mat_mul A B) (mat_mul A' B).
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_row_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst. autorewrite with matrix.
    now rewrite row_op_add_row_spec_1, dep_map_dot_prod_add, dep_map_dot_prod_scal_mul.
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_row_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst. autorewrite with matrix.
    now rewrite row_op_add_row_spec_2, dep_map_dot_prod_add, dep_map_dot_prod_scal_mul.
Qed.

Lemma row_op_add_row_unique: forall a i j {m n: nat} (mat mat1 mat2: Matrix m n),
    row_op_add_row a i j mat mat1 -> row_op_add_row a i j mat mat2 -> mat1 = mat2.
Proof.
  intros. pose proof H. destruct H1 as [? [? [? _]]]. apply not_eq in H3. destruct H3.
  - clear H1. decomp_lt_subst' H3. apply lt_exists_S_diff in H2. unfold Matrix in *.
    destruct H2 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H1. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_row_spec_1 in H, H0.
    destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? [? [? ?]]]]. now subst.
  - clear H2. decomp_lt_subst' H3. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H1. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite row_op_add_row_spec_2 in H, H0.
    destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? [? [? ?]]]]. now subst.
Qed.

Lemma row_op_add_row_exists: forall a i j {m n: nat} (mat: Matrix m n),
    i < m -> j < m -> i <> j -> exists mat', row_op_add_row a i j mat mat'.
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
    now rewrite row_op_add_row_spec_1.
  - clear H0. decomp_lt_subst' H1. apply lt_exists_S_diff in H. unfold Matrix in *.
    destruct H as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H. subst m.
    do 2 (dep_add_decomp; dep_list_decomp).
    exists (dep_app mat0 (dep_cons (vec_add mat2 (vec_scal_mul a mat3))
                                   (dep_app mat1 (dep_cons mat3 mat5)))).
    now rewrite row_op_add_row_spec_2.
Qed.

Lemma row_op_add_row_cons: forall a i j {m n: nat} (mat1 mat2: Matrix m n) v,
    row_op_add_row a i j mat1 mat2 ->
    row_op_add_row a (S i) (S j) (dep_cons v mat1) (dep_cons v mat2).
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite <- plus_Sn_m.
    rewrite dep_cons_app, (dep_cons_app v). rewrite row_op_add_row_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst.
    now rewrite (row_op_add_row_spec_1
                   a (dep_cons v mat1) (dep_cons v mat1) mat6 mat6 mat9 mat9
                   mat2 mat2 mat8 (vec_add mat8 (vec_scal_mul a mat2))).
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp). rewrite <- plus_Sn_m.
    rewrite dep_cons_app, (dep_cons_app v). rewrite row_op_add_row_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst.
    now rewrite (row_op_add_row_spec_2
                   a (dep_cons v mat1) (dep_cons v mat1) mat6 mat6 mat9 mat9
                   mat4 (vec_add mat4 (vec_scal_mul a mat5)) mat5 mat5).
Qed.

Lemma row_op_add_row_cons_col: forall a i j {m n: nat} (mat1 mat2: Matrix m n),
    row_op_add_row a i j mat1 mat2 ->
    row_op_add_row a i j (dep_list_binop (dep_cons (n := n)) vec_zero mat1)
                   (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. pose proof H. destruct H0 as [? [? [? _]]]. apply not_eq in H2. destruct H2.
  - clear H0. decomp_lt_subst' H2. apply lt_exists_S_diff in H1. unfold Matrix in *.
    destruct H1 as [j ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp).
    rewrite vec_zero_app, vec_zero_cons, vec_zero_app, vec_zero_cons,
    !dep_list_binop_app, !dep_list_binop_cons, !dep_list_binop_app,
    !dep_list_binop_cons. rewrite row_op_add_row_spec_1 in H.
    destruct H as [? [? [? [? ?]]]]. subst. rewrite row_op_add_row_spec_1.
    autorewrite with vector. now rewrite Rplus_0_l, Rmult_0_r.
  - clear H1. decomp_lt_subst' H2. apply lt_exists_S_diff in H0. unfold Matrix in *.
    destruct H0 as [i ?]. rewrite plus_assoc_reverse, plus_Sn_m in H0. subst m.
    do 2 (dep_add_decomp; dep_list_decomp).
    rewrite vec_zero_app, vec_zero_cons, vec_zero_app, vec_zero_cons,
    !dep_list_binop_app, !dep_list_binop_cons, !dep_list_binop_app,
    !dep_list_binop_cons. rewrite row_op_add_row_spec_2 in H.
    destruct H as [? [? [? [? ?]]]]. subst. rewrite row_op_add_row_spec_2.
    autorewrite with vector. now rewrite Rplus_0_l, Rmult_0_r.
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

Inductive SeqElmtryRowOpRel {m n: nat}:
    Matrix m n -> list ElmtryRowOp -> Matrix m n -> Prop :=
| seror_nil: forall (mat: Matrix m n), SeqElmtryRowOpRel mat List.nil mat
| seror_mul_cons: forall (m1 m2 m3: Matrix m n) a i l,
    row_op_mul_row a i m1 m2 -> SeqElmtryRowOpRel m2 l m3 ->
    SeqElmtryRowOpRel m1 (MultiplyRow a i :: l) m3
| seror_swap_cons: forall (m1 m2 m3: Matrix m n) i j l,
    row_op_swap_row i j m1 m2 -> SeqElmtryRowOpRel m2 l m3 ->
    SeqElmtryRowOpRel m1 (SwapRow i j :: l) m3
| seror_add_cons: forall (m1 m2 m3: Matrix m n) a i j l,
    row_op_add_row a i j m1 m2 -> SeqElmtryRowOpRel m2 l m3 ->
    SeqElmtryRowOpRel m1 (AddRow a i j :: l) m3.

Lemma seror_det: forall {n: nat} (mat1 mat2: Matrix n n) (l: list ElmtryRowOp),
    SeqElmtryRowOpRel mat1 l mat2 -> det mat1 = (coeff_of_eros l * det mat2)%R.
Proof.
  intros. induction H; simpl.
  - ring.
  - apply row_op_mul_row_det in H. rewrite IHSeqElmtryRowOpRel in H. rewrite H. ring.
  - apply row_op_swap_row_det in H. rewrite IHSeqElmtryRowOpRel in H. rewrite H. ring.
  - apply row_op_add_row_det in H. rewrite IHSeqElmtryRowOpRel in H. rewrite H. ring.
Qed.

Lemma seror_comm_mul: forall {m n l: nat} (A A': Matrix m n) (B: Matrix n l) li,
    SeqElmtryRowOpRel A li A' -> SeqElmtryRowOpRel (mat_mul A B) li (mat_mul A' B).
Proof.
  intros. induction H.
  - constructor.
  - apply seror_mul_cons with (mat_mul m2 B); [apply row_op_mul_row_comm_mul|]; easy.
  - apply seror_swap_cons with (mat_mul m2 B); [apply row_op_swap_row_comm_mul|]; easy.
  - apply seror_add_cons with (mat_mul m2 B); [apply row_op_add_row_comm_mul|]; easy.
Qed.

Lemma seror_cons: forall {m n: nat} (mat1 mat2: Matrix m n) (v: Vector n) li,
    SeqElmtryRowOpRel mat1 li mat2 ->
    exists li', SeqElmtryRowOpRel (dep_cons v mat1) li' (dep_cons v mat2).
Proof.
  intros. induction H; [|destruct IHSeqElmtryRowOpRel..].
  - exists nil. constructor.
  - apply (row_op_mul_row_cons _ _ _ _ v) in H. exists (MultiplyRow a (S i) :: x).
    now apply seror_mul_cons with (dep_cons v m2).
  - apply (row_op_swap_row_cons _ _ _ _ v) in H. exists (SwapRow (S i) (S j) :: x).
    now apply seror_swap_cons with (dep_cons v m2).
  - apply (row_op_add_row_cons _ _ _ _ _ v) in H. exists (AddRow a (S i) (S j) :: x).
    now apply seror_add_cons with (dep_cons v m2).
Qed.

Lemma seror_cons_col: forall {m n: nat} (mat1 mat2: Matrix m n) li,
    SeqElmtryRowOpRel mat1 li mat2 ->
    SeqElmtryRowOpRel (dep_list_binop (dep_cons (n := n)) vec_zero mat1) li
                      (dep_list_binop (dep_cons (n := n)) vec_zero mat2).
Proof.
  intros. induction H.
  - constructor.
  - apply row_op_mul_row_cons_col in H.
    now apply seror_mul_cons with (dep_list_binop (dep_cons (n:=n)) vec_zero m2).
  - apply row_op_swap_row_cons_col in H.
    now apply seror_swap_cons with (dep_list_binop (dep_cons (n:=n)) vec_zero m2).
  - apply row_op_add_row_cons_col in H.
    now apply seror_add_cons with (dep_list_binop (dep_cons (n:=n)) vec_zero m2).
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
      split; auto. constructor. apply H1. }
Abort.

Definition multilinear_map (f: forall n, Matrix n n -> R): Prop :=
  forall (n m: nat) (a1 a2: R) (m1: Matrix n (n + S m))
         (m2: Matrix m (n + S m)) (r1 r2: Vector (n + S m)),
    f (n + S m)
      (dep_app m1 (dep_cons (vec_add (vec_scal_mul a1 r1) (vec_scal_mul a2 r2)) m2)) =
    (a1 * f (n + S m)%nat (dep_app m1 (dep_cons r1 m2)) +
     a2 * f (n + S m)%nat (dep_app m1 (dep_cons r2 m2)))%R.

Lemma det_is_multilinear_map: multilinear_map (@det).
Proof. red. intros. now rewrite det_row_add, !det_row_mul. Qed.

Definition alternating_form (f: forall x, Matrix x x -> R): Prop :=
  forall {n m l: nat} (m1: Matrix n (n + S (m + S l))) (m2: Matrix m (n + S (m + S l)))
         (m3: Matrix l (n + S (m + S l))) (r: Vector (n + S (m + S l))),
    f (n + S (m + S l)) (dep_app m1 (dep_cons r (dep_app m2 (dep_cons r m3)))) = 0%R.

Lemma det_is_alternating_form: alternating_form (@det).
Proof. red. intros. now rewrite det_row_dup. Qed.

Lemma multilinear_alternating_unique: forall (f: forall n, Matrix n n -> R),
    multilinear_map f -> alternating_form f ->
    forall n (m: Matrix n n), f n m = (det m * f n identity_mat)%R.
Proof.
  do 3 intro. induction n; intros; unfold Matrix in *.
  - dep_list_decomp. simpl. ring.
  -
Abort.

Goal forall (a b c d e f g h i j k l: R),
    let A := {| {| a; b; c |}; {| d; e; f |} |} in
    let B := {| {| g; h |}; {| i; j |}; {| k; l |} |} in
    det (mat_mul A B) =
    vec_sum (dep_map det (dep_list_binop mat_mul (dep_colist (mat_transpose A))
                                         (dep_colist B))).
Proof. intros. subst A. subst B. vm_compute. ring. Qed.

Goal forall (a b c d e f g h i j k l m n o p q r s t u v w x: R),
    let A := {| {| a; b; c; d |}; {| e; f; g; h |}; {| i; j; k; l |} |} in
    let B := {| {| m; n; o |}; {| p; q; r |}; {| s; t; u |}; {| v; w; x |} |} in
    det (mat_mul A B) =
    vec_sum (dep_map det (dep_list_binop mat_mul (dep_colist (mat_transpose A))
                                         (dep_colist B))).
Proof. intros. subst A. subst B. vm_compute. ring. Qed.

Definition adj {n: nat}: Matrix n n -> Matrix n n :=
  match n as m return (Matrix m m -> Matrix m m) with
  | O => fun _ => dep_nil
  | S l =>
    fun mat =>
      (dep_map (dep_list_binop Rmult (alter_sign (dep_repeat 1%R (S l))))
               (mat_transpose
                  (dep_map
                     (dep_list_binop Rmult (alter_sign (dep_repeat 1%R (S l))))
                     (dep_map (dep_map det)
                              (dep_map (fun x => dep_colist (dep_list_transpose x))
                                       (dep_colist mat))))))
  end.

Goal forall (a b c d e f g h i: R),
    let A := {| {| a; b; c |}; {| d; e; f |}; {| g; h; i |} |} in
    mat_mul (adj A) A = mat_scal_mul (det A) identity_mat.
Proof.
  intros. subst A. vm_compute. do 2 f_equal.
  - ring.
  - do 2 (f_equal; try ring).
  - do 3 (f_equal; try ring).
  - do 4 (f_equal; try ring).
Qed.

Lemma mat_mul_adj_l: forall {n} (mat: Matrix n n),
    mat_mul (adj mat) mat = mat_scal_mul (det mat) identity_mat.
Proof.
  induction n; intros; unfold Matrix in *.
  - dep_list_decomp. easy.
  - dep_step_decomp mat. unfold adj. simpl dep_repeat.
    autorewrite with matrix vector. destruct n.
    + dep_list_decomp. autorewrite with matrix. vm_compute. do 2 f_equal. ring.
    + simpl dep_repeat. autorewrite with dep_list matrix vector.

Abort.

Lemma cauchy_binet_nxSn: forall {n} (A: Matrix n (S n)) (B: Matrix (S n) n),
    det (mat_mul A B) =
    vec_sum (dep_map det (dep_list_binop mat_mul (dep_colist (mat_transpose A))
                                         (dep_colist B))).
Proof.
  induction n; intros; unfold Matrix in *.
  - dep_list_decomp. autorewrite with matrix dep_list. simpl. vm_compute. ring.
  - rewrite <- (mat_transpose_involutive A) at 1. generalize (mat_transpose A).
    clear A. intros A. unfold Matrix in *. dep_step_decomp A. dep_step_decomp B.
    autorewrite with matrix dep_list.
    dep_step_decomp A1. dep_step_decomp B1. autorewrite with matrix dep_list.
Abort.

Lemma det_mul: forall {n} (A B: Matrix n n), det (mat_mul A B) = (det A * det B)%R.
Proof.
  induction n; intros; unfold Matrix in *.
  - dep_list_decomp. simpl. now rewrite Rmult_1_r.
  - dep_step_decomp A. dep_step_decomp B. autorewrite with matrix.
    rewrite mat_transpose_mul. autorewrite with matrix.
    rewrite dep_colist_mat_mul, dep_colist_cons_col.
    rewrite dep_map_nest, !dep_map_list_binop.
    generalize (mat_transpose A1) (mat_transpose B1). clear A1 B1. intros A1 B1.
    unfold Matrix in *. dep_step_decomp A1.
    rewrite (dep_list_binop_ext
               (fun x y => det (mat_add (mat_span x A2) (mat_mul y A3)))) by
        (intros; now autorewrite with matrix).
Abort.
