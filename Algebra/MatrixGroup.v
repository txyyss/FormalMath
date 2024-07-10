(** * Lɪʙʀᴀʀʏ ᴏғ Mᴀᴛʀɪx Gʀᴏᴜᴘ *)
(** * Aᴜᴛʜᴏʀ: Sʜᴇɴɢʏɪ Wᴀɴɢ *)

Require Import FormalMath.Algebra.Matrix.
Require Import FormalMath.Algebra.Group.
Require Import Coq.micromega.Lra.

Section ORTHOGONAL_GROUP.

  Context {n: nat}.

  Definition OrthogonalMatrix := {mat: Matrix n n | orthogonal_mat mat}.

  #[global] Instance ortho_mat_rep: Cast OrthogonalMatrix (Matrix n n) :=
    fun x => proj1_sig x.

  #[global] Instance ortho_mat_equiv: Equiv OrthogonalMatrix :=
    fun x y => proj1_sig x == proj1_sig y.

  #[global] Instance ortho_mat_binop: BinOp OrthogonalMatrix.
  Proof.
    intros [x] [y]. exists (mat_mul x y). unfold orthogonal_mat in *.
    rewrite mat_transpose_mul, mat_mul_assoc, <- (mat_mul_assoc _ x y), o.
    now autorewrite with matrix.
  Defined.

  #[global] Instance ortho_mat_gunit: GrUnit OrthogonalMatrix.
  Proof. exists identity_mat. red. now autorewrite with matrix. Defined.

  #[global] Instance ortho_mat_neg: Negate OrthogonalMatrix.
  Proof.
    intros [mat]. exists (mat_transpose mat).
    rewrite orthogonal_mat_spec_2. autorewrite with matrix. apply o.
  Defined.

  Instance: Setoid OrthogonalMatrix.
  Proof.
    constructor; unfold equiv, ortho_mat_equiv.
    - intros [x]. now simpl.
    - intros [x] [y]. simpl. now intros.
    - intros [x] [y] [z]. simpl. intros. now transitivity y.
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) ortho_mat_binop.
  Proof. intros [x] [y] ? [x0] [y0] ?. hnf in H, H0 |- *. simpl in *. now subst. Qed.

  Instance: Proper ((=) ==> (=)) ortho_mat_neg.
  Proof. intros [x] [y] ?. hnf in H |- *. simpl in *. now subst. Qed.

  #[global] Instance ortho_mat_group: Group OrthogonalMatrix.
  Proof.
    repeat (constructor; try apply _); repeat intros [?];
      unfold bi_op, neg, ortho_mat_binop, one, equiv,
      ortho_mat_equiv, ortho_mat_gunit, ortho_mat_neg; simpl.
    - apply mat_mul_assoc.
    - now autorewrite with matrix.
    - apply o.
  Qed.

End ORTHOGONAL_GROUP.

Section GENERAL_LINEAR_GROUP.

  Context {n: nat}.

  Definition InvertibleMatrix := {mat: Matrix n n | det mat <> 0%R}.

  #[global] Instance gl_mat_rep: Cast InvertibleMatrix (Matrix n n) :=
    fun x => proj1_sig x.

  #[global] Instance gl_mat_equiv: Equiv InvertibleMatrix :=
    fun x y => ' x == ' y.

  Lemma gl_mat_binop_ok:
    forall x y : InvertibleMatrix, det (mat_mul (' x) (' y)) =/= 0%R.
  Proof.
    intros [x] [y]. simpl. rewrite det_mul. apply Rmult_integral_contrapositive. now split.
  Qed.

  #[global] Instance gl_mat_binop: BinOp InvertibleMatrix.
  Proof.
    intros x y. exists (mat_mul (' x) (' y)). now apply gl_mat_binop_ok.
  Defined.

  Lemma gl_mat_gunit_ok: @det n identity_mat =/= 0%R.
  Proof. rewrite det_identity. lra. Qed.

  #[global] Instance gl_mat_gunit: GrUnit InvertibleMatrix.
  Proof. exists identity_mat. apply gl_mat_gunit_ok. Defined.

  Lemma gl_mat_neg_ok:
    forall mat : InvertibleMatrix,
      det (proj1_sig (mat_inv_exists (' mat) (proj2_sig mat))) =/= 0%R.
  Proof.
    intros [mat ?H]. simpl. destruct (mat_inv_exists mat H) as [imat [[?H ?H] ?H]].
    simpl. pose proof (det_mul imat mat). rewrite H0, det_identity in H3.
    assert ((det imat * det mat)%R =/= 0%R) by lra. apply Rmult_neq_0_reg in H4.
    now destruct H4.
  Qed.

  #[global] Instance gl_mat_neg: Negate InvertibleMatrix.
  Proof.
    intros mat. exists (proj1_sig (mat_inv_exists (' mat) (proj2_sig mat))).
    apply gl_mat_neg_ok.
  Defined.

  Instance: Setoid InvertibleMatrix.
  Proof.
    constructor; unfold equiv, ortho_mat_equiv.
    - intros [x]. now simpl.
    - intros [x] [y]. simpl. now intros.
    - intros [x] [y] [z]. simpl. intros. now transitivity y.
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) gl_mat_binop.
  Proof. intros [x] [y] ? [x0] [y0] ?. hnf in H, H0 |- *. simpl in *. now subst. Qed.

  Instance: Proper ((=) ==> (=)) gl_mat_neg.
  Proof.
    intros [x] [y] ?. hnf in H |- *. simpl in *. subst.
    destruct (mat_inv_exists y n0) as [x1 [[? ?] ?H]].
    destruct (mat_inv_exists y n1) as [x2 [[? ?] ?]].
    simpl. apply H. now split.
  Qed.

  #[global] Instance gl_mat_group: Group InvertibleMatrix.
  Proof.
    repeat (constructor; try apply _); repeat intros [?];
      unfold bi_op, neg, gl_mat_binop, one, equiv,
      gl_mat_equiv, gl_mat_gunit, gl_mat_neg; simpl.
    - apply mat_mul_assoc.
    - now autorewrite with matrix.
    - destruct (mat_inv_exists x n0) as [x1 [[? ?] ?]]. now simpl.
  Qed.

End GENERAL_LINEAR_GROUP.
