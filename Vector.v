Require Import Coq.Reals.Reals.
Require Import FormalMath.lib.dep_list.

Definition Vector (n: nat) := dep_list R n.

Section N_DIMENSION.

  Context {n : nat}.

  Definition vec_add (v1 v2: Vector n): Vector n := dep_list_binop Rplus v1 v2.

  Lemma vec_add_comm: forall v1 v2, vec_add v1 v2 = vec_add v2 v1.
  Proof.
    
  Abort.

  Definition vec_mul (a: R) (v: Vector n): Vector n := dep_map (Rmult a) v.

  Definition vec_dot_prod (v1 v2: Vector n) :=
    dep_fold_left Rplus (dep_list_binop Rmult v1 v2) 0%R.

End N_DIMENSION.
