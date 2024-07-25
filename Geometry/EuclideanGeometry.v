(** * Lɪʙʀᴀʀʏ ᴀʙᴏᴜᴛ Tʀᴀɴsꜰᴏʀᴍᴀᴛɪᴏɴs ᴏꜰ Eᴜᴄʟɪᴅᴇᴀɴ Sᴘᴀᴄᴇ *)
(** * Aᴜᴛʜᴏʀ: Sʜᴇɴɢʏɪ Wᴀɴɢ *)

Require Import FormalMath.Algebra.Matrix.
Require Import FormalMath.Algebra.Group.
Require Import FormalMath.Algebra.FiniteGroup.
Require Import FormalMath.Algebra.GroupAction.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.SetoidPermutation.
Require Import Coq.micromega.Lra.

Open Scope R_scope.
Local Open Scope program_scope.

Class InvertibleAffine {n} (f: Vector n -> Vector n) :=
  {
    aff_inv :: Inverse f;
    aff_inj :: Inj (==) (==) f;
    aff_surj :: Cancel (==) f (f ⁻¹);
    aff_is_affine: affine_map f
  }.

#[global] Arguments aff_inv {_} _ {_}.
#[global] Arguments aff_inj {_} _ {_}.
#[global] Arguments aff_surj {_} _ {_}.

Lemma invertible_affine_inv_affine:
  forall {n} (f: Vector n -> Vector n) {X: InvertibleAffine f}, affine_map (f ⁻¹).
Proof.
  intros. pose proof aff_is_affine. rewrite affine_map_linear_iff in H |- *. destruct H.
  assert (forall u v, f (vec_add u v) == vec_sub (vec_add (f u) (f v)) (f vec_zero)). {
    intros. pose proof (f_equal (fun x => vec_add x (f vec_zero)) (H u v)). simpl in H1.
    rewrite vec_add_sub_assoc in H1. autorewrite with vector in H1.
    rewrite vec_add_assoc, (vec_add_sub_assoc (f v)) in H1. autorewrite with vector in H1.
    now rewrite H1, vec_add_sub_assoc, vec_sub_add_assoc2. }
  assert (forall (a : R) (v : Vector n),
             f (vec_scal_mul a v)  ==
               vec_add (vec_scal_mul a (f v)) (vec_scal_mul (1 - a) (f vec_zero))). {
    intros. pose proof (f_equal (fun x => vec_add x (f vec_zero)) (H0 a v)). simpl in H2.
    rewrite vec_add_sub_assoc in H2. autorewrite with vector in H2.
    rewrite H2, vec_scal_mul_sub_distr_l, vec_add_sub_assoc. unfold vec_sub. f_equal.
    rewrite <- (vec_neg_scal_mul (f _)), <- vec_scal_mul_add_distr_r, vec_scal_mul_neg_opp.
    f_equal. lra. }
  assert (forall v, f (vec_neg v) == vec_sub (vec_scal_mul 2 (f vec_zero)) (f v)). {
    intros. specialize (H2 (-1) v). rewrite !vec_neg_scal_mul in H2.
    rewrite H2, vec_add_comm. unfold vec_sub. do 2 f_equal. lra. }
  assert (vec_sub (vec_scal_mul 2 (f vec_zero)) (f vec_zero) == f vec_zero). {
    rewrite <- (vec_scal_mul_one (f vec_zero)) at 2.
    rewrite <- vec_scal_mul_sub_distr_r. replace (2 - 1) with 1 by lra.
    now rewrite vec_scal_mul_one. } split; repeat intro.
  - apply (aff_inj f). unfold vec_sub. rewrite !H1, H3, !aff_surj.
    autorewrite with vector. rewrite !vec_sub_add_assoc1, H4.
    autorewrite with vector. rewrite !vec_add_assoc. f_equal. now rewrite vec_add_comm.
  - apply (aff_inj f). unfold vec_sub. rewrite H1, H2, H3, H1, H3, !aff_surj.
    autorewrite with vector. rewrite !vec_sub_add_assoc1, H4, vec_scal_mul_add_distr_l.
    rewrite vec_add_assoc, <- vec_scal_mul_add_distr_r. f_equal.
    rewrite <- (vec_scal_mul_one (f vec_zero)) at 1. f_equal. lra.
Qed.

Lemma invertible_affine_invertible_mat: forall {n} (f: Vector n -> Vector n),
    InvertibleAffine f ->
    {mat_v: (Matrix n n * Vector n) |
      unique (fun mv => forall x, f x == vec_add (mat_vec_mul (fst mv) x) (snd mv)) mat_v /\
        invertible_mat (fst mat_v)}.
Proof.
  intros. destruct (affine_map_mat_sig _ aff_is_affine) as [[mat v] [? ?]].
  exists (mat, v). split; [split|]; simpl in *; intros; auto. clear H0.
  destruct (affine_map_mat_sig _ (invertible_affine_inv_affine f)) as [[mat' v'] [? _]].
  simpl fst in H0. simpl snd in H0. rewrite invertible_mat_spec2. exists mat'.
  apply mat_vec_mul_unique. intros x. autorewrite with matrix. pose proof (aff_surj f x).
  rewrite H0, H, mat_vec_mul_add_r, mat_vec_mul_assoc, vec_add_assoc in H1.
  cut (vec_add (mat_vec_mul mat v') v == vec_zero).
  - intros. rewrite H2 in H1. now autorewrite with vector in H1.
  - assert (mat_vec_mul mat v' == vec_sub (f v') v). {
      rewrite H, vec_sub_add_assoc1. now autorewrite with vector. }
    rewrite H2, vec_add_sub_assoc. autorewrite with vector. specialize (H0 vec_zero).
    autorewrite with matrix vector in H0. rewrite <- H0. apply aff_surj.
Qed.

Class DistanceFunc (A: Type) := distance: A -> A -> R.
#[global] Typeclasses Transparent DistanceFunc.

Class Metric (A: Type) {DF: DistanceFunc A}: Prop :=
  {
    metric_nonneg: forall x y, 0 <= distance x y;
    metric_zero_iff: forall x y, distance x y == 0 <-> x == y;
    metric_sym: forall x y, distance x y == distance y x;
    metric_trig_ineq: forall x y z, distance x z <= distance x y + distance y z
  }.

Section EUCLIDEAN_DISTANCE.

  Context {n: nat}.

  Definition norm (v: Vector n) := sqrt (vec_dot_prod v v).

  Lemma Rabs_norm: forall (v: Vector n), Rabs (norm v) == norm v.
  Proof. intros. unfold norm. rewrite Rabs_pos_eq; auto. apply sqrt_pos. Qed.

  Theorem Cauchy_Schwarz_ineq: forall (u v: Vector n),
      Rabs (vec_dot_prod u v) <= norm u * norm v.
  Proof.
    intros. cut ((vec_dot_prod u v)² <= (norm u)² * (norm v)²).
    - intros. rewrite <- Rsqr_mult in H. apply Rsqr_le_abs_0 in H.
      now rewrite Rabs_mult, !Rabs_norm in H.
    - unfold norm. rewrite !Rsqr_sqrt; [|apply vec_dot_prod_nonneg..].
      destruct (vec_eq_dec v vec_zero).
      + subst. autorewrite with vector. rewrite Rsqr_0, Rmult_0_r. apply Rle_refl.
      + assert (vec_dot_prod v v =/= 0). {
          intro. apply vec_dot_prod_zero in H. now apply n0. }
        remember ((vec_dot_prod u v) / (vec_dot_prod v v)) as l.
        pose proof (vec_dot_prod_nonneg (vec_sub u (vec_scal_mul l v))).
        rewrite !vec_dot_prod_sub_r, !vec_dot_prod_sub_l,
          !vec_dot_prod_scal_l, !vec_dot_prod_scal_r in H0. rewrite Heql in H0 at 4.
        rewrite Rdiv_simpl_l in H0; auto.
        rewrite (vec_dot_prod_comm v u), Rminus_diag, Rminus_0_r in H0.
        apply (Rplus_le_compat_r (l * vec_dot_prod u v)) in H0.
        rewrite <- Rplus_minus_swap, <- Rplus_minus_assoc, Rminus_diag,
          Rplus_0_l, Rplus_0_r in H0.
        assert (l * vec_dot_prod u v == (vec_dot_prod u v)² / vec_dot_prod v v). {
          rewrite Rmult_comm. subst l. unfold Rsqr, Rdiv. now rewrite Rmult_assoc. }
        rewrite H1 in H0. clear Heql H1.
        apply (Rmult_le_compat_r (vec_dot_prod v v)) in H0.
        * rewrite Rdiv_simpl_l in H0; auto.
        * apply vec_dot_prod_nonneg.
  Qed.

  Lemma norm_tri_ineq: forall (x y: Vector n), norm (vec_add x y) <= norm x + norm y.
  Proof.
    intros. cut (vec_dot_prod (vec_add x y) (vec_add x y) <= (norm x + norm y)²).
    - intros. rewrite <- (Rsqr_sqrt (vec_dot_prod (vec_add x y) (vec_add x y))) in H.
      + apply Rsqr_le_abs_0 in H. rewrite !Rabs_pos_eq in H; auto.
        * apply Rplus_le_le_0_compat; apply sqrt_pos.
        * apply sqrt_pos.
      + apply vec_dot_prod_nonneg.
    - rewrite !vec_dot_prod_add_r, !vec_dot_prod_add_l.
      assert (0 <= 2) by apply Rlt_le, Rlt_0_2.
      apply Rle_trans with
          (r2 := ((norm x)² + (norm y)² + 2 * Rabs (vec_dot_prod x y))).
      + unfold norm. rewrite !Rsqr_sqrt; [|apply vec_dot_prod_nonneg..].
        rewrite !Rplus_assoc. apply Rplus_le_compat_l. rewrite <- Rplus_assoc.
        rewrite (Rplus_comm (vec_dot_prod y y)). apply Rplus_le_compat_r.
        rewrite (vec_dot_prod_comm y), Rplus_diag. apply Rmult_le_compat_l; auto.
        apply RRle_abs.
      + rewrite Rsqr_plus. apply Rplus_le_compat_l. rewrite Rmult_assoc.
        apply Rmult_le_compat_l; auto. apply Cauchy_Schwarz_ineq.
  Qed.

  #[global] Instance eucDis: DistanceFunc (Vector n) := fun x y => norm (vec_sub x y).

  #[global] Instance distanceMetric: Metric (Vector n).
  Proof.
    constructor; intros; unfold distance, eucDis, norm.
    - apply sqrt_pos.
    - split; intro.
      + apply sqrt_eq_0 in H. 2: apply vec_dot_prod_nonneg.
        apply vec_dot_prod_zero in H. now rewrite vec_sub_eq_zero_iff in H.
      + subst. autorewrite with vector. apply sqrt_0.
    - rewrite (vec_sub_swap x y). autorewrite with vector. now rewrite Ropp_involutive.
    - remember (vec_sub x y) as vx. remember (vec_sub y z) as vy.
      assert (vec_sub x z == vec_add vx vy). {
        subst. rewrite vec_add_sub_assoc. f_equal.
        rewrite <- vec_sub_add_assoc2, vec_add_comm, vec_sub_add_assoc1.
        now autorewrite with vector. } rewrite H. clear. apply norm_tri_ineq.
  Qed.

  Lemma polarization_identity: forall (u v: Vector n),
      vec_dot_prod u v == ((norm u)² + (norm v)² - (norm (vec_sub u v))²) * / 2.
  Proof.
    intros. cut (2 * vec_dot_prod u v == (norm u)² + (norm v)² - (norm (vec_sub u v))²).
    - intros. rewrite <- H, Rmult_comm, <- Rmult_assoc, Rinv_l, Rmult_1_l. 1: easy.
      apply not_0_IZR. discriminate.
    - unfold norm. rewrite !Rsqr_sqrt; [|apply vec_dot_prod_nonneg..].
      rewrite vec_dot_prod_sub_r, !vec_dot_prod_sub_l. ring_simplify.
      rewrite (vec_dot_prod_comm v). now rewrite <- Rplus_diag.
  Qed.

  Lemma vec_dot_prod_distance: forall (u v: Vector n),
      vec_dot_prod u v ==
        ((distance u vec_zero)² + (distance v vec_zero)² - (distance u v)²) * / 2.
  Proof.
    intros. unfold distance, eucDis. autorewrite with vector. apply polarization_identity.
  Qed.

End EUCLIDEAN_DISTANCE.

Class Isometric {n} (f: Vector n -> Vector n) :=
  {
    iso_inv :: Inverse f;
    iso_inj :: Inj (==) (==) f;
    iso_surj :: Cancel (==) f (f ⁻¹);
    distance_preserve: forall x y, distance x y == distance (f x) (f y)
  }.

#[global] Arguments iso_inv {_} _ {_}.
#[global] Arguments iso_inj {_} _ {_}.
#[global] Arguments iso_surj {_} _ {_}.

Lemma preserve_dot_prod_isometric: forall {n} (f: Vector n -> Vector n),
    preserve_dot_prod f -> Isometric f.
Proof.
  intros. pose proof H as S. apply preserve_dot_prod_mat_sig in H.
  destruct H as [mat [[? ?] ?]]. exists (mat_vec_mul (mat_transpose mat)); repeat intro.
  - rewrite !H in H2. rewrite <- mat_vec_mul_identity, <- (mat_vec_mul_identity x).
    now rewrite <- !H1, <- !mat_vec_mul_assoc, H2.
  - simpl. rewrite H, mat_vec_mul_assoc.
    rewrite <- orthogonal_mat_spec1, orthogonal_mat_spec2 in H1.
    now rewrite H1, mat_vec_mul_identity.
  - pose proof (preserve_dot_prod_linear _ S). destruct H2.
    red in S. unfold distance, eucDis, vec_sub.
    rewrite <- !vec_neg_scal_mul, <- H3, <- H2, !vec_neg_scal_mul. unfold norm.
    now rewrite S.
Qed.

Lemma isometric_fix_preserve_dot_prod: forall {n} (f: Vector n -> Vector n),
    Isometric f -> f vec_zero == vec_zero -> preserve_dot_prod f.
Proof.
  intros. red. intros.
  now rewrite !vec_dot_prod_distance, <- H, <- !distance_preserve, H.
Qed.

Lemma translation_isometric: forall {n} (v: Vector n), Isometric (vec_add v).
Proof.
  intros. exists (vec_add (vec_neg v)); repeat intro.
  - now rewrite <- vec_add_id_l, <- (vec_add_id_l x), <- (vec_add_inv1 (vec_neg v)),
    vec_neg_nest, !vec_add_assoc, H.
  - simpl. rewrite <- vec_add_assoc. now autorewrite with vector.
  - unfold distance, eucDis, vec_sub.
    rewrite vec_neg_add, (vec_add_comm v x), vec_add_assoc, <- (vec_add_assoc v (vec_neg v)).
    now autorewrite with vector.
Qed.

Lemma ext_isometric: forall {n} (f g: Vector n -> Vector n),
    (forall x, f x == g x) -> Isometric f -> Isometric g.
Proof.
  intros. exists (iso_inv f); repeat intro.
  - rewrite <- !H in H0. now apply iso_inj in H0.
  - simpl. rewrite <- H. now apply iso_surj.
  - rewrite <- !H. now apply distance_preserve.
Qed.

Definition Isometry (n: nat) := sigT (fun func => @Isometric n func).

Section ISOMETRY.

  Context {n: nat}.

  #[global] Instance iso_rep: Cast (Isometry n) (Vector n -> Vector n) := fun x => projT1 x.

  #[global] Instance iso_equiv: Equiv (Isometry n) :=
    fun f1 f2 => forall x, (' f1) x == (' f2) x.

  #[global] Instance iso_binop: BinOp (Isometry n).
  Proof.
    intros [f1] [f2].
    refine (existT _ (fun x => f1 (f2 x))
                   (Build_Isometric _ _ (fun x => (iso_inv f2) (iso_inv f1 x)) _ _ _));
      repeat intro.
    - apply (iso_inj f2), (iso_inj f1); auto.
    - pose proof (iso_surj f1). pose proof (iso_surj f2). simpl in *. now rewrite H0, H.
    - transitivity (distance (f2 x) (f2 y)); apply distance_preserve.
  Defined.

  #[global] Instance iso_gunit: GrUnit (Isometry n).
  Proof.
    refine (existT _ (fun x => x) (Build_Isometric _ _ (fun x => x) _ _ _));
      repeat intro; auto.
  Defined.

  #[global] Instance iso_neg: Negate (Isometry n).
  Proof.
    intros [f].
    refine (existT _ (iso_inv f) (Build_Isometric _ _ f _ _ _));
      assert (forall x, iso_inv f (f x) == x) by
        (intros; apply (iso_inj f), iso_surj); repeat intro; auto.
    - pose proof (iso_surj f x). pose proof (iso_surj f y). simpl in *.
      rewrite <- H0, H1 in H2; assumption.
    - rewrite <- (iso_surj f x), <- (iso_surj f y), !H. symmetry.
      apply distance_preserve.
  Defined.

  Instance: Setoid (Isometry n).
  Proof. constructor; repeat intro; [| rewrite H | rewrite H, H0]; reflexivity. Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) iso_binop.
  Proof.
    repeat intro. simpl. unfold iso_rep, iso_binop. destruct x, y, x0, y0.
    unfold equiv, iso_equiv in H, H0. simpl in *. rewrite H0, H. reflexivity.
  Qed.

  Instance: Proper ((=) ==> (=)) iso_neg.
  Proof.
    repeat intro. simpl. unfold iso_rep, iso_neg. destruct x, y.
    unfold equiv, iso_equiv in H. simpl in *. apply (iso_inj x).
    change (iso_inv x) with (x ⁻¹). change (iso_inv x1) with (x1 ⁻¹).
    rewrite iso_surj, H, iso_surj. reflexivity.
  Qed.

  #[global] Instance isometryGroup: Group (Isometry n).
  Proof.
    constructor; try apply _; intros; unfold bi_op, iso_binop, one, iso_gunit,
                                      neg, iso_neg, equiv, iso_equiv.
    - destruct x, y, z; intros; simpl. reflexivity.
    - destruct x; intros; simpl; reflexivity.
    - destruct x. intros. simpl. apply (iso_inj x). change (iso_inv x) with (x ⁻¹).
      rewrite iso_surj; reflexivity.
  Qed.

End ISOMETRY.

Lemma isometric_orthogonal_mat: forall {n} (f: Vector n -> Vector n),
    Isometric f ->
    {mat_v: (Matrix n n * Vector n) |
      unique (fun mv => forall x, f x == vec_add (mat_vec_mul (fst mv) x) (snd mv)) mat_v /\
        orthogonal_mat (fst mat_v)}.
Proof.
  intros. remember (existT _ _ (translation_isometric (vec_neg (f vec_zero)))) as T.
  remember (existT _ _ X) as A. remember (T & A). destruct s as [B ?H].
  assert (B == (fun x : Vector n => vec_add (vec_neg (f vec_zero)) (f x))). {
    destruct T, A. unfold bi_op, iso_binop in Heqs.
    apply EqdepFacts.eq_sigT_fst in Heqs. apply EqdepFacts.eq_sigT_fst in HeqT.
    apply EqdepFacts.eq_sigT_fst in HeqA. now subst x x0. }
  assert (B vec_zero == vec_zero) by
      (subst B; rewrite vec_add_comm; now autorewrite with vector).
  pose proof (isometric_fix_preserve_dot_prod _ H H1).
  apply preserve_dot_prod_mat_sig in H2. destruct H2 as [mat [[? ?] ?]].
  exists (mat, (f vec_zero)). split; [split|]; simpl; intros; auto.
  - rewrite <- H2, H0, vec_add_comm, <- vec_add_assoc. now autorewrite with vector.
  - destruct x' as [mat2 v]. simpl in *. f_equal.
    + apply H3. intros. subst B. rewrite !H5.
      autorewrite with matrix vector. rewrite vec_add_comm, vec_add_assoc.
      now autorewrite with vector.
    + rewrite H5. now autorewrite with matrix vector.
Qed.

Lemma orthogonal_mat_isometric: forall {n} (mat: Matrix n n) (v: Vector n),
    orthogonal_mat mat -> Isometric (fun x => vec_add (mat_vec_mul mat x) v).
Proof.
  intros. rewrite orthogonal_mat_spec1 in H. apply mat_vec_mul_preserve_dot_prod in H.
  apply preserve_dot_prod_isometric in H. remember (existT _ _ H) as R.
  remember (existT _ _ (translation_isometric v)) as T. remember (T & R).
  destruct s as [B ?H]. destruct R, T. unfold bi_op, iso_binop in Heqs.
  apply EqdepFacts.eq_sigT_fst in Heqs. apply EqdepFacts.eq_sigT_fst in HeqT.
  apply EqdepFacts.eq_sigT_fst in HeqR. subst x x0. apply (ext_isometric B); auto.
  intros. subst. now rewrite vec_add_comm.
Qed.

Lemma isometric_is_affine: forall {n} (f: Vector n -> Vector n),
    Isometric f -> affine_map f.
Proof.
  intros. apply isometric_orthogonal_mat in X. destruct X as [[mat v] [[? _] ?]].
  simpl in *. apply (affine_map_ext (fun x => vec_add v (mat_vec_mul mat x))).
  - intros. now rewrite H, vec_add_comm.
  - apply affine_map_compose.
    + apply linear_map_is_affine, mat_vec_mul_linear_map.
    + apply vec_add_is_affine.
Qed.

Section ISOMETRY_ACTION.

  Context {n: nat}.

  #[global] Instance isometry_act: GrAct (Isometry n) (Vector n) := fun g x => ('g) x.

  Instance: Proper ((=) ==> (==) ==> (==)) isometry_act.
  Proof.
    intros [x] [y] ? a b ?. unfold isometry_act. subst. red in H.
    unfold iso_equiv in H. simpl in *. apply H.
  Qed.

  #[global] Instance isometryGroupAction: GroupAction (Isometry n) (Vector n).
  Proof.
    constructor; auto.
    - apply _.
    - intros [g] [h] ?. vm_compute. easy.
  Qed.

End ISOMETRY_ACTION.

Lemma isometry_subgroup_fix_one_point:
  forall `{!SubGroupCondition (Isometry n) P},
    SetoidFinite (Subpart (Isometry n) P) ->
    exists c, forall (g: Subpart (Isometry n) P), g ⊙ c == c.
Proof.
  intros n P SGC ?. destruct H as [m [l [? [? ?]]]].
  unfold gr_act, subgroup_act, gr_act, isometry_act.
  remember (vec_scal_mul
              (/ INR m)
              (@fold_right (Vector n) _ vec_add
                           vec_zero (map (fun x => (''x) vec_zero) l))) as c. exists c.
  intros [[g]]. simpl. rewrite Heqc at 1.
  rewrite (fold_right_distr (fun x y => (@vec_scal_mul x n y))).
  2: intros; apply vec_scal_mul_add_distr_l. autorewrite with vector.
  rewrite (map_binary_func (fun x y => (@vec_scal_mul x n y))).
  rewrite <- fold_right_map, (isometric_is_affine _ i).
  - rewrite fold_right_map, map_binary_snd_combine with
        (f := fun x y => (@vec_scal_mul x n y)), map_map, map_length.
    replace (length l) with
        (length (map (fun x : Subpart (Isometry n) P => g ((' (' x)) vec_zero)) l)) by
        now rewrite map_length.
    rewrite <- (map_binary_func (fun x y => (@vec_scal_mul x n y))).
    replace vec_zero with (@vec_scal_mul (/ INR m) n vec_zero) by
        now rewrite vec_scal_mul_zero_r.
    rewrite <- (fold_right_distr (fun x y => (@vec_scal_mul x n y))).
    2: intros; apply vec_scal_mul_add_distr_l. autorewrite with vector. subst c.
    f_equal. apply fold_right_perm.
    + apply vec_add_comm.
    + apply vec_add_assoc.
    + remember (exist _ (existT _ g i) p) as gg.
      replace (map (fun x => g ((' (' x)) vec_zero)) l)
        with (map (fun x : Subpart (Isometry n) P => (''x) vec_zero) (map (gg &) l)).
      * remember (fun x : Subpart (Isometry n) P => (' (' x)) vec_zero) as f.
        assert (forall (l1 l2: list (Subpart (Isometry n) P)),
                   PermutationA (=) l1 l2 -> Permutation (map f l1) (map f l2)). {
          subst f. clear. intros. induction H; simpl; try constructor.
          - change (iso_rep (subgroup_rep x₁)) with (' (' x₁)).
            change (iso_rep (subgroup_rep x₂)) with (' (' x₂)).
            rewrite H. now constructor.
          - apply perm_trans with
                (map (fun x : Subpart (Isometry n) P => (' (' x)) vec_zero) l₂); auto.
          } apply H2. symmetry. now apply finite_group_left_perm.
      * rewrite map_map. apply map_ext. intros [[a]]. subst gg. now simpl.
  - rewrite fold_right_map, map_fst_combine. 2: now rewrite repeat_length, map_length.
    assert (forall r k, fold_right Rplus 0 (repeat r k) == Rmult (INR k) r). {
      intros. induction k. 1: simpl; ring. rewrite S_INR. simpl. rewrite IHk. ring. }
    rewrite map_length, H0, H2. apply Rinv_r, not_0_INR. destruct SGC, non_empty.
    specialize (H1 (exist _ x H3)). intro. subst m. now destruct l.
Qed.
