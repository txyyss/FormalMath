Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo_facts.
Require Import Coq.micromega.Lra.

Local Open Scope R_scope.

Lemma Rdiv_simpl_l: forall (r1 r2: R), r1 <> 0 -> r2 / r1 * r1 = r2.
Proof.
  intros. unfold Rdiv. rewrite Rmult_assoc, (Rmult_comm (/ r1)).
  rewrite <- Rinv_r_sym; auto. apply Rmult_1_r.
Qed.

Lemma Rsqr_sum_1_bound: forall x y: R, x² + y² = 1 -> -1 <= x <= 1 /\ -1 <= y <= 1.
Proof.
  intros. assert (x² + y² <= 1²) by (rewrite Rsqr_1; now apply Req_le_sym).
  apply triangle_rectangle in H0. 2: apply Rle_0_1. easy.
Qed.

Lemma Rsqr_sum_solve: forall a x b: R, a + x² = b ->
                                       x = sqrt (b - a) \/ x = - sqrt (b - a).
Proof.
  intros. assert (x² = b - a) by (rewrite <- H; ring). apply Rsqr_eq.
  rewrite Rsqr_sqrt; auto. rewrite <- H0. apply Rle_0_sqr.
Qed.

Lemma Rsqr_sum_1_cos_sin_or: forall x y: R,
    x² + y² = 1 -> exists t, 0 <= t <= PI /\
                             (x = cos t /\ y = sin t \/ x = cos t /\ y = - sin t).
Proof.
  intros. destruct (Rsqr_sum_1_bound _ _ H). exists (acos x). split.
  1: apply acos_bound. rewrite cos_acos; auto. rewrite sin_acos; auto.
  apply Rsqr_sum_solve in H. destruct H; [left | right]; now split.
Qed.

Lemma Rsqr_sum_1_cos_sin: forall x y: R,
    x² + y² = 1 -> exists t, - PI <= t <= PI /\ x = cos t /\ y = sin t.
Proof.
  intros. destruct (Rsqr_sum_1_cos_sin_or _ _ H) as [m [? [[? ?] | [? ?]]]].
  - exists m. split; [|split]; auto. lra.
  - exists (- m). rewrite cos_neg, sin_neg. split; [|split]; auto. lra.
Qed.

Lemma Rmult_sqr: forall x: R, x * x = x². Proof. now unfold Rsqr. Qed.

Lemma sin_le_0': forall x: R, - PI <= x <= 0 -> sin x <= 0.
Proof.
  intros. rewrite <- (sin_period _ 1). ring_simplify. change (INR 1) with 1%R.
  rewrite Rmult_1_r. apply sin_le_0; lra.
Qed.

Lemma cos2_sum_1_sin: forall x y, (cos x)² + y² = 1 -> y = sin x \/ y = - sin x.
Proof.
  intros. apply Rsqr_sum_solve in H. destruct (Rle_dec (sin x) 0).
  - apply sin_cos_opp in r. destruct H.
    + apply Ropp_eq_compat in r. rewrite Ropp_involutive, <- H in r. now right.
    + rewrite <- H in r. now left.
  - assert (sin x >= 0) by lra. apply sin_cos in H0. destruct H.
    + rewrite <- H in H0. now left.
    + apply Ropp_eq_compat in H0. rewrite <- H in H0. now right.
Qed.

Lemma sin2_sum_1_cos: forall x y, (sin x)² + y² = 1 -> y = cos x \/ y = - cos x.
Proof.
  intros. apply Rsqr_sum_solve in H. destruct (Rle_dec (cos x) 0).
  - apply cos_sin_opp in r. destruct H.
    + apply Ropp_eq_compat in r. rewrite Ropp_involutive, <- H in r. now right.
    + rewrite <- H in r. now left.
  - assert (cos x >= 0) by lra. apply cos_sin in H0. destruct H.
    + rewrite <- H in H0. now left.
    + apply Ropp_eq_compat in H0. rewrite <- H in H0. now right.
Qed.

Lemma R2_neq_0: 2 <> 0. Proof. pose proof Rlt_0_2. now apply Rlt_not_eq in H. Qed.
