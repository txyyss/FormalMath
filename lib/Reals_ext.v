(** * Part of the following code comes from https://github.com/coq/coq/pull/9803 *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Local Open Scope R_scope.

Lemma Rdiv_simpl_l: forall (r1 r2: R), r1 <> 0 -> r2 / r1 * r1 = r2.
Proof.
  intros. unfold Rdiv. rewrite Rmult_assoc, (Rmult_comm (/ r1)).
  rewrite <- Rinv_r_sym; auto. apply Rmult_1_r.
Qed.

Lemma sqrt_neg_0 x: x <= 0 -> sqrt(x) = 0.
Proof.
  intros Hx.
  pose proof sqrt_0 as H1.
  pose proof sqrt_le_1_alt x 0 Hx as H2.
  pose proof sqrt_pos x as H3.
  lra.
Qed.

Lemma inv_sqrt x: 0 < x -> / sqrt x = sqrt (/ x).
Proof.
  intros x0.
  assert (sqrt x <> 0).
  apply Rgt_not_eq.
  now apply sqrt_lt_R0.
  apply Rmult_eq_reg_r with (sqrt x); auto.
  rewrite Rinv_l; auto.
  rewrite <- sqrt_mult_alt.
  now rewrite -> Rinv_l, sqrt_1; auto with real.
  apply Rlt_le.
  now apply Rinv_0_lt_compat.
Qed.

Lemma neg_pos_Rsqr_lt:  forall x y: R, - y < x -> x < y -> x² < y².
Proof.
  intros x y Hneg Hpos.
  apply Rsqr_lt_abs_1.
  unfold Rabs.
  repeat case Rcase_abs.
  all: lra.
Qed.

Lemma sqr_bound_le: forall a b:R, -a <= b <= a -> 0 <= b² <= a².
Proof.
  intros a b H.
  split.
  - apply Rle_0_sqr.
  - apply neg_pos_Rsqr_le; lra.
Qed.

Lemma sqr_bound_lt: forall a b:R, -a < b < a -> 0 <= b² < a².
Proof.
  intros a b H.
  split.
  - apply Rle_0_sqr.
  - apply neg_pos_Rsqr_lt; lra.
Qed.

Lemma atan_inv: forall x, 0 < x ->  atan (/ x) = PI / 2 - atan x.
Proof.
  intros x Hx.
  apply tan_is_inj.
  - apply atan_bound.
  - split.
    + apply Rlt_trans with R0.
      * unfold Rdiv.
        rewrite Ropp_mult_distr_l_reverse.
        apply Ropp_lt_gt_0_contravar.
        apply PI2_RGT_0.
      * apply Rgt_minus.
        apply atan_bound.
    + apply Rplus_lt_reg_r with (atan x - PI / 2).
      ring_simplify.
      rewrite <- atan_0.
      now apply atan_increasing.
  - rewrite atan_right_inv.
    unfold tan.
    rewrite sin_shift.
    rewrite cos_shift.
    rewrite <- Rinv_Rdiv.
    + apply f_equal, sym_eq, atan_right_inv.
    + apply Rgt_not_eq, sin_gt_0.
      * rewrite <- atan_0.
        now apply atan_increasing.
      * apply Rlt_trans with (2 := PI2_Rlt_PI).
        apply atan_bound.
    + apply Rgt_not_eq, cos_gt_0.
      unfold Rdiv.
      rewrite <- Ropp_mult_distr_l_reverse.
      apply atan_bound.
      apply atan_bound.
Qed.

Lemma sin_inj x y: -(PI/2) <= x <= PI/2 ->
                    -(PI/2) <= y <= PI/2 -> sin x = sin y -> x = y.
Proof.
  intros xP yP Hsin.
  destruct (total_order_T x y) as [[H|H]|H]; auto.
  - assert (sin x < sin y).
    now apply sin_increasing_1; lra.
    now lra.
  - assert (sin y < sin x).
    now apply sin_increasing_1; lra.
    now lra.
Qed.

Lemma cos_inj x y: 0 <= x <= PI -> 0 <= y <= PI -> cos x = cos y -> x = y.
Proof.
  intros xP yP Hcos.
  destruct (total_order_T x y) as [[H|H]|H]; auto.
  - assert (cos y < cos x).
    now apply cos_decreasing_1; lra.
    now lra.
  - assert (cos x < cos y).
    now apply cos_decreasing_1; lra.
    now lra.
Qed.

Lemma sin2_bound: forall α:R, 0 <= (sin α)² <= 1.
Proof.
  intros α.
  rewrite <- Rsqr_1.
  apply sqr_bound_le.
  apply SIN_bound.
Qed.

Lemma cos2_bound: forall α:R, 0 <= (cos α)² <= 1.
Proof.
  intros α.
  rewrite <- Rsqr_1.
  apply sqr_bound_le.
  apply COS_bound.
Qed.

Lemma sin_cos: forall α:R, sin α >=0 -> sin α = sqrt(1 - (cos α)²).
Proof.
  intros α H.
  apply Rsqr_inj.
  - lra.
  - apply sqrt_pos.
  - rewrite Rsqr_sqrt.
    apply sin2.
    pose proof cos2_bound α.
    lra.
Qed.

Lemma sin_cos_opp: forall α:R, sin α <= 0 -> sin α = - sqrt(1 - (cos α)²).
Proof.
  intros α H.
  rewrite <- (Ropp_involutive (sin α)).
  apply Ropp_eq_compat.
  apply Rsqr_inj.
  - lra.
  - apply sqrt_pos.
  - rewrite Rsqr_sqrt.
    rewrite <- Rsqr_neg.
    apply sin2.
    pose proof cos2_bound α.
    lra.
Qed.

Lemma tan_cos_opp: forall α:R, 0 >= sin α -> tan α = - sqrt (1-(cos α)²) / cos α.
Proof.
  intros α H.
  unfold tan.
  rewrite sin_cos_opp by lra.
  reflexivity.
Qed.

Lemma tan_sin: forall α:R, 0 <= cos α -> tan α = sin α / sqrt (1-(sin α)²).
Proof.
  intros α H.
  unfold tan.
  rewrite <- (sqrt_Rsqr (cos α)) by assumption.
  rewrite <- (cos2 α).
  reflexivity.
Qed.

Lemma tan_cos: forall α:R, 0 <= sin α -> tan α = sqrt (1-(cos α)²) / cos α.
Proof.
  intros α H.
  unfold tan.
  rewrite <- (sqrt_Rsqr (sin α)) by assumption.
  rewrite <- (sin2 α).
  reflexivity.
Qed.

Lemma sin_tan: forall α:R, 0 < cos α -> sin α = tan α / sqrt (1+(tan α)²).
Proof.
  intros.
  assert(Hcosle:0<=cos α) by lra.
  pose proof tan_sin α Hcosle as Htan.
  rewrite Htan.
  repeat rewrite <- Rsqr_pow2 in *.
  assert (forall a b c:R, b<>0 -> c<> 0 -> a/b/c = a/(b*c)) as R_divdiv_divmul
      by (intros; field; lra).
  rewrite R_divdiv_divmul.
  rewrite <- sqrt_mult_alt.
  rewrite Rsqr_div, Rsqr_sqrt.
  field_simplify ((1 - (sin α)²) * (1 + (sin α)² / (1 - (sin α)²))).
  rewrite sqrt_1.
  field.
  all: pose proof (sin2 α); pose proof Rsqr_pos_lt (cos α); try lra.
  all: assert( forall a, 0 < a -> a <> 0) as Hne by (intros; lra).
  all: apply Hne, sqrt_lt_R0; try lra.
  rewrite <- Htan.
  pose proof Rle_0_sqr (tan α); lra.
Qed.

Lemma cos_tan: forall α:R, 0 < cos α -> cos α = 1 / sqrt (1+(tan α)²).
Proof.
  intros.
  destruct (Rcase_abs (sin α)) as [Hsignsin|Hsignsin].
  - assert(Hsinle:0>=sin α) by lra.
    pose proof tan_cos_opp α Hsinle as Htan.
    rewrite Htan.
    rewrite Rsqr_div.
    rewrite <- Rsqr_neg.
    rewrite Rsqr_sqrt.
    field_simplify( 1 + (1 - (cos α)²) / (cos α)² ).
    rewrite sqrt_div_alt.
    rewrite sqrt_1.
    field_simplify_eq.
    rewrite sqrt_Rsqr.
    reflexivity.
    all: pose proof cos2_bound α.
    all: pose proof Rsqr_pos_lt (cos α) ltac:(lra).
    all: pose proof sqrt_lt_R0 (cos α)² ltac:(assumption).
    all: lra.
  - assert(Hsinge:0<=sin α) by lra.
    pose proof tan_cos α Hsinge as Htan.
    rewrite Htan.
    rewrite Rsqr_div.
    rewrite Rsqr_sqrt.
    field_simplify( 1 + (1 - (cos α)²) / (cos α)² ).
    rewrite sqrt_div_alt.
    rewrite sqrt_1.
    field_simplify_eq.
    rewrite sqrt_Rsqr.
    reflexivity.
    all: pose proof cos2_bound α.
    all: pose proof Rsqr_pos_lt (cos α) ltac:(lra).
    all: pose proof sqrt_lt_R0 (cos α)² ltac:(assumption).
    all: lra.
Qed.

Lemma sin_atan: forall x:R, sin(atan(x))=x/sqrt(1+x²).
Proof.
  intros x.
  pose proof (atan_right_inv x) as Hatan.
  remember (atan(x)) as α.
  rewrite <- Hatan.
  apply sin_tan.
  apply cos_gt_0.
  all: pose proof atan_bound x; lra.
Qed.

Lemma cos_atan: forall x:R, cos(atan(x))=1/sqrt(1+x²).
Proof.
  intros x.
  pose proof (atan_right_inv x) as Hatan.
  remember (atan(x)) as α.
  rewrite <- Hatan.
  apply cos_tan.
  apply cos_gt_0.
  all: pose proof atan_bound x; lra.
Qed.

Lemma cos_sin: forall α:R, cos α >=0 -> cos α = sqrt(1 - (sin α)²).
Proof.
  intros α H.
  apply Rsqr_inj.
  - lra.
  - apply sqrt_pos.
  - rewrite Rsqr_sqrt.
    apply cos2.
    pose proof sin2_bound α.
    lra.
Qed.

Definition asin x :=
  if Rle_dec x (-1) then - (PI / 2) else
    if Rle_dec 1 x then PI / 2 else
      atan (x / sqrt(1 - x²)).

Lemma asin_atan x: -1 < x < 1 -> asin x = atan (x / sqrt (1 - x²)).
Proof. unfold asin; repeat case Rle_dec; intros; lra. Qed.

Lemma asin_0: asin 0 = 0.
Proof.
  unfold asin; repeat case Rle_dec; intros; try lra.
  replace (0/_) with 0.
  - apply atan_0.
  - field.
    rewrite Rsqr_pow2; field_simplify (1 - 0^2).
    rewrite sqrt_1; lra.
Qed.

Lemma asin_1: asin 1 = PI / 2.
Proof.
  unfold asin; repeat case Rle_dec; lra.
Qed.

Lemma asin_inv_sqrt2: asin (/sqrt 2) = PI/4.
Proof.
  rewrite asin_atan.
  pose proof sqrt2_neq_0 as SH.
  rewrite Rsqr_pow2, <-Rinv_pow, <- Rsqr_pow2, Rsqr_sqrt; try lra.
  replace (1 - /2) with (/2) by lra.
  rewrite <- inv_sqrt; try lra.
  now rewrite <- atan_1; apply f_equal; field.
  split.
  apply (Rlt_trans _ 0); try lra.
  now apply Rinv_0_lt_compat; apply sqrt_lt_R0; lra.
  replace 1 with (/ sqrt 1).
  apply Rinv_1_lt_contravar.
  now rewrite sqrt_1; lra.
  now apply sqrt_lt_1; lra.
  now rewrite sqrt_1; lra.
Qed.

Lemma asin_opp x: asin (- x) = - asin x.
Proof.
  unfold asin; repeat case Rle_dec; intros; try lra.
  rewrite <- Rsqr_neg.
  rewrite Ropp_div.
  rewrite atan_opp.
  reflexivity.
Qed.

Lemma asin_bound x: - (PI/2) <= asin x <= PI/2.
Proof.
  pose proof PI_RGT_0.
  unfold asin; repeat case Rle_dec; try lra.
  intros Hx1 Hx2.
  pose proof atan_bound (x / sqrt (1 - x²)); lra.
Qed.

Lemma asin_bound_lt x: -1 < x < 1 -> - (PI/2) < asin x < PI/2.
Proof.
  intro HxB.
  pose proof PI_RGT_0.
  unfold asin; repeat case Rle_dec; try lra.
  intros Hx1 Hx2.
  pose proof atan_bound (x / sqrt (1 - x²)); lra.
Qed.

(** ** arcsine is the left and right inverse of sine *)

Lemma sin_asin x: -1 <= x <= 1 -> sin (asin x) = x.
Proof.
  unfold asin; repeat case Rle_dec.
  rewrite sin_antisym, sin_PI2; lra.
  rewrite sin_PI2; lra.
  intros Hx1 Hx2 Hx3.
  rewrite sin_atan.
  assert (forall a b c:R, b<>0 -> c<> 0 -> a/b/c = a/(b*c)) as R_divdiv_divmul by (intros; field; lra).
  rewrite R_divdiv_divmul.
  rewrite <- sqrt_mult_alt.
  rewrite Rsqr_div, Rsqr_sqrt.
  field_simplify((1 - x²) * (1 + x² / (1 - x²))).
  rewrite sqrt_1.
  field.
  (* Pose a few things useful for several subgoals *)
  all: pose proof sqr_bound_lt 1 x ltac:(lra) as Hxsqr;
    rewrite Rsqr_1 in Hxsqr.
  all: pose proof sqrt_lt_R0 (1 - x²) ltac:(lra).
  (* Do 6 first, because it produces more subgoals *)
  all: swap 1 6.
  rewrite Rsqr_div, Rsqr_sqrt.
  field_simplify(1 + x² / (1 - x²)).
  rewrite sqrt_div.
  rewrite sqrt_1.
  pose proof Rdiv_lt_0_compat 1 (sqrt (- x² + 1)) ltac:(lra) as Hrange.
  pose proof sqrt_lt_R0 (- x² + 1) ltac:(lra) as Hrangep.
  specialize (Hrange Hrangep).
  lra.
  (* The rest can all be done with lra *)
  all: try lra.
Qed.

Lemma asin_sin x: -(PI/2) <= x <= PI/2 -> asin (sin x) = x.
Proof.
  intros HB.
  apply sin_inj; auto.
  apply asin_bound.
  apply sin_asin.
  apply SIN_bound.
Qed.

(** ** Relation between arcsin, cosine and tangent *)

Lemma cos_asin: forall x: R, -1 <= x <= 1 -> cos (asin x) = sqrt (1 - x²).
Proof.
  intros x Hxrange.
  pose proof (sin_asin x) ltac:(lra) as Hasin.
  remember (asin(x)) as α.
  rewrite <- Hasin.
  apply cos_sin.
  pose proof cos_ge_0 α.
  pose proof asin_bound x.
  lra.
Qed.

Lemma tan_asin: forall x: R, -1 <= x <= 1 -> tan (asin x) = x / sqrt (1-x²).
Proof.
  intros x Hxrange.
  pose proof (sin_asin x) Hxrange as Hasin.
  remember (asin(x)) as α.
  rewrite <- Hasin.
  apply tan_sin.
  pose proof cos_ge_0 α.
  pose proof asin_bound x.
  lra.
Qed.

Lemma derivable_pt_asin: forall x, -1 < x < 1 -> derivable_pt asin x.
Proof.
  intros x H.

  eapply (Coq.Reals.Ranalysis5.derivable_pt_recip_interv sin asin (-PI/2) (PI/2)).
  { rewrite <- (pr_nu sin (asin x) (derivable_pt_sin (asin x))).
    rewrite derive_pt_sin.
    pose proof asin_bound_lt x ltac:(lra) as HxB3.
    unfold asin in *.
    destruct (Rle_dec x (-1)); destruct (Rle_dec 1 x).
    intros HxB1; contradict HxB1; lra.
    intros HxB1; contradict HxB1; lra.
    intros HxB1; contradict HxB1; lra.
    apply Rgt_not_eq.
    apply cos_gt_0; lra.
  }

  Unshelve.
  - pose proof PI_RGT_0 as HPi; lra.
  - rewrite Ropp_div,sin_antisym,sin_PI2; lra.
  - intros x0 Ha Hb.
    unfold comp,id.
    rewrite sin_asin.
    + reflexivity.
    + rewrite Ropp_div,sin_antisym,sin_PI2 in *; lra.
  - clear x H; intros x Ha Hb.
    rewrite Ropp_div; apply asin_bound.
  - intros x1 x2 Ha Hb Hc.
    apply sin_increasing_1; lra.
  - intros a Ha.
    reg.
Qed.

Lemma derive_pt_asin: forall (x: R) (Hxrange: -1 < x < 1),
    derive_pt asin x (derivable_pt_asin x Hxrange) = 1/sqrt(1-x²).
Proof.
  intros x Hxrange.

  epose proof (Ranalysis5.derive_pt_recip_interv sin asin (-PI/2) (PI/2) x
                                                 ?[H1] ?[H2] ?[H3] ?[H4] ?[H5] ?[H6] ?[H7]) as Hd.

  rewrite <- (pr_nu sin (asin x) (derivable_pt_sin (asin x))) in Hd.
  rewrite <- (pr_nu asin x (derivable_pt_asin x Hxrange)) in Hd.
  rewrite derive_pt_sin in Hd.
  rewrite cos_asin in Hd.
  assumption; lra.

  Unshelve.
  - lra.
  - pose proof PI_RGT_0. lra.
  - rewrite Ropp_div,sin_antisym,sin_PI2; lra.
  - intros x1 x2 Ha Hb Hc.
    apply sin_increasing_1; lra.
  - intros x0 Ha Hb.
    pose proof asin_bound x0; lra.
  - intros a Ha.
    reg.
  - intros x0 Ha Hb.
    unfold comp,id.
    rewrite sin_asin.
    + reflexivity.
    + rewrite Ropp_div,sin_antisym,sin_PI2 in *; lra.
  - rewrite <- (pr_nu sin (asin x) (derivable_pt_sin (asin x))).
    rewrite derive_pt_sin.
    rewrite cos_asin.
    apply Rgt_not_eq.
    apply sqrt_lt_R0.
    pose proof sqr_bound_lt 1 x ltac:(lra) as Hxsqrrange.
    rewrite Rsqr_1 in Hxsqrrange; lra.
    lra.
Qed.

Definition acos x :=
  if Rle_dec x (-1) then PI else
    if Rle_dec 1 x then 0 else
      PI/2 - atan (x/sqrt(1-x²)).

(** ** Relation between arccosine, arcsine and arctangent *)

Lemma acos_atan x: 0 < x -> acos x = atan (sqrt (1 - x²) / x).
Proof.
  unfold acos; repeat case Rle_dec; [lra | |].
  - intros Hx1 Hx2 Hx3.
    pose proof sqr_bound_le x 1 ltac:(lra)as Hxsqr.
    rewrite Rsqr_1 in Hxsqr.
    rewrite sqrt_neg_0 by lra.
    replace (0/x) with 0 by (field;lra).
    rewrite atan_0; reflexivity.
  - intros Hx1 Hx2 Hx3.
    pose proof atan_inv (sqrt (1 - x²) / x) as Hatan.
    pose proof sqr_bound_lt 1 x ltac:(lra)as Hxsqr.
    rewrite Rsqr_1 in Hxsqr.
    replace (/ (sqrt (1 - x²) / x)) with (x/sqrt (1 - x²)) in Hatan.
    + rewrite Hatan; [field|].
      apply Rdiv_lt_0_compat; [|assumption].
      apply sqrt_lt_R0; lra.
    + field; split.
      lra.
      assert(sqrt (1 - x²) >0) by (apply sqrt_lt_R0; lra); lra.
Qed.

Lemma acos_asin x: -1 <= x <= 1 -> acos x = PI/2 - asin x.
Proof. unfold acos, asin; repeat case Rle_dec; lra. Qed.

Lemma asin_acos x: -1 <= x <= 1 -> asin x = PI/2 - acos x.
Proof. unfold acos, asin; repeat case Rle_dec; lra. Qed.

Lemma acos_0: acos 0 = PI/2.
Proof.
  unfold acos; repeat case Rle_dec; try lra.
  intros Hx1 Hx2.
  replace (0/_) with 0.
  rewrite atan_0; field.
  field.
  rewrite Rsqr_pow2; field_simplify (1 - 0^2).
  rewrite sqrt_1; lra.
Qed.

Lemma acos_1: acos 1 = 0.
Proof.
  unfold acos; repeat case Rle_dec; lra.
Qed.

Lemma acos_opp x: acos (- x) = PI - acos x.
Proof.
  unfold acos; repeat case Rle_dec; try lra.
  intros Hx1 Hx2 Hx3 Hx4.
  rewrite <- Rsqr_neg, Ropp_div, atan_opp.
  lra.
Qed.

Lemma acos_inv_sqrt2: acos (/sqrt 2) = PI/4.
Proof.
  rewrite acos_asin.
  rewrite asin_inv_sqrt2.
  lra.
  split.
  apply Rlt_le.
  apply (Rlt_trans (-1) 0 (/ sqrt 2)); try lra.
  apply Rinv_0_lt_compat.
  apply Rlt_sqrt2_0.
  replace 1 with (/ sqrt 1).
  apply Rlt_le.
  apply Rinv_1_lt_contravar.
  rewrite sqrt_1; lra.
  apply sqrt_lt_1; lra.
  rewrite sqrt_1; lra.
Qed.

(** ** Bounds of arccosine *)

Lemma acos_bound x: 0 <= acos x <= PI.
Proof.
  pose proof PI_RGT_0.
  unfold acos; repeat case Rle_dec; try lra.
  intros Hx1 Hx2.
  pose proof atan_bound (x / sqrt (1 - x²)); lra.
Qed.

Lemma acos_bound_lt x: -1 < x < 1 -> 0 < acos x < PI.
Proof.
  intro xB.
  pose proof PI_RGT_0.
  unfold acos; repeat case Rle_dec; try lra.
  intros Hx1 Hx2.
  pose proof atan_bound (x / sqrt (1 - x²)); lra.
Qed.

(** ** arccosine is the left and right inverse of cosine *)

Lemma cos_acos x: -1 <= x <= 1 -> cos (acos x) = x.
Proof.
  intros xB.
  assert (H: x = -1 \/ -1 < x) by lra.
  destruct H as [He|Hl].
  rewrite He.
  change (IZR (-1)) with (-(IZR 1)).
  now rewrite acos_opp, acos_1, Rminus_0_r, cos_PI.
  assert (H: x = 1 \/ x < 1) by lra.
  destruct H as [He1|Hl1].
  now rewrite He1, acos_1, cos_0.
  rewrite acos_asin, cos_shift; try lra.
  rewrite sin_asin; lra.
Qed.

Lemma acos_cos x: 0 <= x <= PI -> acos (cos x) = x.
Proof.
  intro HB.
  apply cos_inj; try lra.
  apply acos_bound.
  apply cos_acos.
  apply COS_bound.
Qed.

(** ** Relation between arccosine, sine and tangent *)

Lemma sin_acos: forall x: R, -1 <= x <= 1 -> sin (acos x) = sqrt (1 - x²).
Proof.
  intros x Hxrange.
  pose proof (cos_acos x) ltac:(lra) as Hacos.
  remember (acos(x)) as α.
  rewrite <- Hacos.
  apply sin_cos.
  pose proof sin_ge_0 α.
  pose proof acos_bound x.
  lra.
Qed.

Lemma tan_acos: forall x: R, -1 <= x <= 1 -> tan (acos x) = sqrt (1-x²) / x.
Proof.
  intros x Hxrange.
  pose proof (cos_acos x) Hxrange as Hacos.
  remember (acos(x)) as α.
  rewrite <- Hacos.
  apply tan_cos.
  pose proof sin_ge_0 α.
  pose proof acos_bound x.
  lra.
Qed.

(** *The following code is written by 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

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

Lemma cos_sin_opp: forall α: R, cos α <= 0 -> cos α = - sqrt(1 - (sin α)²).
Proof.
  intros. rewrite <- (Ropp_involutive (cos α)).
  apply Ropp_eq_compat. apply Rsqr_inj.
  - lra.
  - apply sqrt_pos.
  - rewrite Rsqr_sqrt.
    + rewrite <- Rsqr_neg. apply cos2.
    + pose proof sin2_bound α. lra.
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
