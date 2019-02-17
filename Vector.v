Require Import Coq.Reals.Reals.
Require Import FormalMath.lib.dep_list.

Definition Vector (n: nat) := dep_list R n.

Fixpoint vec_zero {n: nat}: Vector n :=
  match n with | O => dep_nil | S m => dep_cons 0%R vec_zero end.

Section N_DIMENSION.

  Context {n : nat}.

  Definition vec_add (v1 v2: Vector n): Vector n := dep_list_binop Rplus v1 v2.

  Lemma vec_add_assoc: forall v1 v2 v3,
      vec_add (vec_add v1 v2) v3 = vec_add v1 (vec_add v2 v3).
  Proof. intros. unfold vec_add. apply dep_list_binop_assoc, Rplus_assoc. Qed.

  Lemma vec_add_comm: forall v1 v2, vec_add v1 v2 = vec_add v2 v1.
  Proof. intros. unfold vec_add. apply dep_list_binop_comm, Rplus_comm. Qed.

  Lemma vec_add_id: forall v, vec_add v vec_zero = v.
  Proof.
    intros. unfold vec_add.
    apply dep_list_ind_1 with (v := v); intros; simpl;
      autorewrite with dep_list; [easy | now rewrite H, Rplus_0_r].
  Qed.

  Definition vec_neg (v: Vector n): Vector n := dep_map Ropp v.

  Lemma vec_add_inv: forall v, vec_add v (vec_neg v) = vec_zero.
  Proof.
    intros. unfold vec_add, vec_neg.
    apply dep_list_ind_1 with (v := v); intros; simpl;
      autorewrite with dep_list; [easy | now rewrite H, Rplus_opp_r].
  Qed.

  Definition scalar_mul (a: R) (v: Vector n): Vector n := dep_map (Rmult a) v.

  Lemma scalar_mul_one: forall v, scalar_mul 1 v = v.
  Proof.
    intros. unfold scalar_mul. apply dep_list_ind_1 with (v := v); simpl. 1: easy.
    intros. now rewrite H, Rmult_1_l.
  Qed.

  Lemma scalar_mul_assoc: forall a b v,
      scalar_mul a (scalar_mul b v) = scalar_mul (a * b) v.
  Proof.
    intros. unfold scalar_mul. apply dep_list_ind_1 with (v := v); intros; simpl.
    - easy.
    - rewrite H. f_equal. now rewrite Rmult_assoc.
  Qed.

  Lemma scalar_mul_add_distr_r: forall a u v,
      scalar_mul a (vec_add u v) = vec_add (scalar_mul a u) (scalar_mul a v).
  Proof.
    intros. unfold vec_add, scalar_mul.
    apply dep_list_ind_2 with (v1 := u) (v2 := v); intros;
      simpl dep_map at 2 3; autorewrite with dep_list; simpl; [easy |].
    rewrite H. f_equal. apply Rmult_plus_distr_l.
  Qed.

  Lemma scalar_mul_add_distr_l: forall a b v,
      scalar_mul (a + b) v = vec_add (scalar_mul a v) (scalar_mul b v).
  Proof.
    intros. unfold vec_add, scalar_mul.
    apply dep_list_ind_1 with (v := v); intros; simpl; autorewrite with dep_list.
    - easy.
    - rewrite H. f_equal. apply Rmult_plus_distr_r.
  Qed.

  Definition vec_dot_prod (v1 v2: Vector n) :=
    dep_fold_left Rplus (dep_list_binop Rmult v1 v2) 0%R.

End N_DIMENSION.
