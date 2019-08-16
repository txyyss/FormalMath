(** Lɪʙʀᴀʀʏ ᴀʙᴏᴜᴛ Isᴏᴍᴇᴛʀɪᴇs ᴏғ Eᴜᴄʟɪᴅᴇᴀɴ Sᴘᴀᴄᴇ *)
(** Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

Require Import FormalMath.Matrix.

Open Scope R_scope.

Definition norm {n} (v: Vector n) := sqrt (vec_dot_prod v v).

Definition distance {n} (x y: Vector n) := norm (vec_add x (vec_neg y)).

Lemma polarization_identity: forall {n} (u v: Vector n),
    vec_dot_prod u v = ((norm u)² + (norm v)² - (norm (vec_add u (vec_neg v)))²) * / 2.
Proof.
  intros. cut (2 * vec_dot_prod u v =
               (norm u)² + (norm v)² - (norm (vec_add u (vec_neg v)))²).
  - intros. rewrite <- H, Rmult_comm, <- Rmult_assoc, Rinv_l, Rmult_1_l. 1: easy.
    apply not_0_IZR. discriminate.
  - unfold norm. rewrite !Rsqr_sqrt; [|apply vec_dot_prod_nonneg..].
    rewrite vec_dot_prod_add_r, !vec_dot_prod_add_l. autorewrite with vector.
    ring_simplify. rewrite (vec_dot_prod_comm v). apply double.
Qed.

Lemma vec_dot_prod_distance: forall {n} (u v: Vector n),
    vec_dot_prod u v =
    ((distance u vec_zero)² + (distance v vec_zero)² - (distance u v)²) * / 2.
Proof.
  intros. unfold distance. autorewrite with vector. apply polarization_identity.
Qed.
