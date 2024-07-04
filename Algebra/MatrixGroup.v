(** * Lɪʙʀᴀʀʏ ᴏғ Mᴀᴛʀɪx Gʀᴏᴜᴘ *)
(** * Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

Require Import FormalMath.Algebra.Matrix.
Require Import FormalMath.Algebra.Group.

Section ORTHOGONAL_GROUP.

  Context {n: nat}.

  Definition OrthogonalMatrix := {mat: Matrix n n | orthogonal_mat mat}.

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
