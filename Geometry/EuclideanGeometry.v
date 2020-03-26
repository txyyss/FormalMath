(** * Lɪʙʀᴀʀʏ ᴀʙᴏᴜᴛ Isᴏᴍᴇᴛʀɪᴇs ᴏғ Eᴜᴄʟɪᴅᴇᴀɴ Sᴘᴀᴄᴇ *)
(** * Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

Require Import FormalMath.Algebra.Matrix.
Require Import FormalMath.Algebra.Group.
Require Import FormalMath.Algebra.FiniteGroup.
Require Import FormalMath.Algebra.GroupAction.
Require Import FormalMath.Topology.Topology.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.SetoidPermutation.

Open Scope R_scope.

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
        pose proof (vec_dot_prod_nonneg (vec_add u (vec_neg (vec_scal_mul l v)))).
        rewrite !vec_dot_prod_add_r, !vec_dot_prod_add_l, !vec_dot_prod_neg_r,
        !vec_dot_prod_neg_l, !vec_dot_prod_scal_l, !vec_dot_prod_scal_r in H0.
        rewrite Ropp_involutive in H0. rewrite Heql in H0 at 4.
        rewrite Rdiv_simpl_l in H0; auto. rewrite (vec_dot_prod_comm u v) in H0 at 2.
        rewrite Rplus_opp_l, Rplus_0_r in H0.
        apply (Rplus_le_compat_r (l * vec_dot_prod u v)) in H0.
        rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_l, Rplus_0_r in H0.
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
        rewrite (vec_dot_prod_comm y), <- double. apply Rmult_le_compat_l; auto.
        apply RRle_abs.
      + rewrite Rsqr_plus. apply Rplus_le_compat_l. rewrite Rmult_assoc.
        apply Rmult_le_compat_l; auto. apply Cauchy_Schwarz_ineq.
  Qed.

  Global Instance eucDis: DistanceFunc (Vector n) :=
    fun x y => norm (vec_add x (vec_neg y)).

  Global Instance distanceMetric: Metric (Vector n).
  Proof.
    constructor; intros; unfold d, eucDis, norm.
    - apply sqrt_pos.
    - split; intro.
      + apply sqrt_eq_0 in H. 2: apply vec_dot_prod_nonneg.
        apply vec_dot_prod_zero in H. now rewrite vec_add_neg_zero_iff in H.
      + subst. autorewrite with vector. apply sqrt_0.
    - rewrite <- (vec_neg_double x) at 1 2. rewrite <- vec_neg_add.
      autorewrite with vector. rewrite Ropp_involutive. now rewrite vec_add_comm.
    - remember (vec_add x (vec_neg y)) as vx.
      remember (vec_add y (vec_neg z)) as vy.
      assert (vec_add x (vec_neg z) == vec_add vx vy). {
        subst. rewrite <- vec_add_assoc. rewrite (vec_add_assoc x).
        now autorewrite with vector. } rewrite H. clear. apply norm_tri_ineq.
  Qed.

  Lemma polarization_identity: forall (u v: Vector n),
      vec_dot_prod u v ==
      ((norm u)² + (norm v)² - (norm (vec_add u (vec_neg v)))²) * / 2.
  Proof.
    intros. cut (2 * vec_dot_prod u v ==
                 (norm u)² + (norm v)² - (norm (vec_add u (vec_neg v)))²).
    - intros. rewrite <- H, Rmult_comm, <- Rmult_assoc, Rinv_l, Rmult_1_l. 1: easy.
      apply not_0_IZR. discriminate.
    - unfold norm. rewrite !Rsqr_sqrt; [|apply vec_dot_prod_nonneg..].
      rewrite vec_dot_prod_add_r, !vec_dot_prod_add_l. autorewrite with vector.
      ring_simplify. rewrite (vec_dot_prod_comm v). apply double.
  Qed.

  Lemma vec_dot_prod_distance: forall (u v: Vector n),
      vec_dot_prod u v == ((d u vec_zero)² + (d v vec_zero)² - (d u v)²) * / 2.
  Proof.
    intros. unfold d, eucDis. autorewrite with vector. apply polarization_identity.
  Qed.

End EUCLIDEAN_DISTANCE.

Class Isometric {n} (f: Vector n -> Vector n) :=
  {
    iso_inv: Vector n -> Vector n;
    iso_inj: forall x y, f x == f y -> x == y;
    iso_surj: forall x, f (iso_inv x) == x;
    distance_preserve: forall x y, d x y == d (f x) (f y)
  }.

Arguments iso_inv {_} _ {_}.
Arguments iso_inj {_} _ {_}.
Arguments iso_surj {_} _ {_}.

Lemma preserve_dot_prod_isometric: forall {n} (f: Vector n -> Vector n),
    preserve_dot_prod f -> Isometric f.
Proof.
  intros. pose proof H as S. apply preserve_dot_prod_mat_sig in H.
  destruct H as [mat [[? ?] ?]]. exists (mat_vec_mul (mat_transpose mat)); intros.
  - rewrite !H0 in H2. rewrite <- mat_vec_mul_identity, <- (mat_vec_mul_identity x).
    now rewrite <- !H, <- !mat_vec_mul_assoc, H2.
  - rewrite H0, mat_vec_mul_assoc.
    rewrite <- orthogonal_mat_spec_1, orthogonal_mat_spec_2 in H.
    now rewrite H, mat_vec_mul_identity.
  - pose proof (preserve_dot_prod_linear _ S). destruct H2.
    red in S. unfold d, eucDis.
    rewrite <- !vec_neg_scal_mul, <- H3, <- H2, !vec_neg_scal_mul. unfold norm.
    now rewrite S.
Qed.

Lemma isometric_fix_preserve_dot_prod: forall {n} (f: Vector n -> Vector n),
    Isometric f -> f vec_zero == vec_zero -> preserve_dot_prod f.
Proof.
  intros. red. intros.
  now rewrite !vec_dot_prod_distance, <- H0, <- !distance_preserve, H0.
Qed.

Lemma translation_isometric: forall {n} (v: Vector n), Isometric (vec_add v).
Proof.
  intros. exists (vec_add (vec_neg v)); intros.
  - now rewrite <- vec_add_id_l, <- (vec_add_id_l x), <- (vec_add_inv1 (vec_neg v)),
    vec_neg_double, !vec_add_assoc, H.
  - rewrite <- vec_add_assoc. now autorewrite with vector.
  - unfold d, eucDis. rewrite vec_neg_add, (vec_add_comm v x), vec_add_assoc,
                     <- (vec_add_assoc v (vec_neg v)). now autorewrite with vector.
Qed.

Lemma ext_isometric: forall {n} (f g: Vector n -> Vector n),
    (forall x, f x == g x) -> Isometric f -> Isometric g.
Proof.
  intros. exists (iso_inv f); intros.
  - rewrite <- !H in H1. now apply iso_inj in H1.
  - rewrite <- H. now apply iso_surj.
  - rewrite <- !H. now apply distance_preserve.
Qed.

Definition Isometry (n: nat) := sigT (fun func => @Isometric n func).

Section ISOMETRY.

  Context {n: nat}.

  Global Instance iso_rep: Cast (Isometry n) (Vector n -> Vector n) :=
    fun x => projT1 x.

  Global Instance iso_equiv: Equiv (Isometry n) :=
    fun f1 f2 => forall x, (' f1) x == (' f2) x.

  Global Instance iso_binop: BinOp (Isometry n).
  Proof.
    intros [f1] [f2].
    refine (existT _ (fun x => f1 (f2 x))
                   (Build_Isometric _ _ (fun x => (iso_inv f2) (iso_inv f1 x)) _ _ _));
      intros.
    - apply (iso_inj f2), (iso_inj f1); auto.
    - do 2 rewrite iso_surj; easy.
    - transitivity (d (f2 x) (f2 y)); apply distance_preserve.
  Defined.

  Global Instance iso_gunit: GrUnit (Isometry n).
  Proof.
    refine (existT _ (fun x => x) (Build_Isometric _ _ (fun x => x) _ _ _));
      intros; auto.
  Defined.

  Global Instance iso_neg: Negate (Isometry n).
  Proof.
    intros [f].
    refine (existT _ (iso_inv f) (Build_Isometric _ _ f _ _ _));
      assert (forall x, iso_inv f (f x) == x) by
        (intros; apply (iso_inj f), iso_surj); intros; auto.
    - pose proof (iso_surj f x). pose proof (iso_surj f y).
      rewrite <- H0, H1 in H2; assumption.
    - rewrite <- (iso_surj f x), <- (iso_surj f y), !H. symmetry.
      apply distance_preserve.
  Defined.

  Instance: Setoid (Isometry n).
  Proof. constructor; repeat intro; [| rewrite H | rewrite H, H0]; reflexivity. Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) iso_binop.
  Proof.
    repeat intro. unfold cast, iso_rep, iso_binop. destruct x, y, x0, y0.
    unfold equiv, iso_equiv in H, H0. simpl in *. rewrite H0, H. reflexivity.
  Qed.

  Instance: Proper ((=) ==> (=)) iso_neg.
  Proof.
    repeat intro. unfold cast, iso_rep, iso_neg. destruct x, y.
    unfold equiv, iso_equiv in H. simpl in *. apply (iso_inj x).
    rewrite iso_surj, H, iso_surj. reflexivity.
  Qed.

  Global Instance isometryGroup: Group (Isometry n).
  Proof.
    constructor; try apply _; intros; unfold bi_op, iso_binop, one, iso_gunit,
                                      neg, iso_neg, equiv, iso_equiv.
    - destruct x, y, z; intros; simpl. reflexivity.
    - destruct x; intros; simpl; reflexivity.
    - destruct x. intros; unfold cast, iso_rep. simpl.
      apply (iso_inj x). rewrite iso_surj; reflexivity.
  Qed.

End ISOMETRY.

Lemma isometric_orthogonal_mat: forall {n} (f: Vector n -> Vector n),
    Isometric f ->
    {mat_v: (Matrix n n * Vector n) |
     unique (fun mv => orthogonal_mat (fst mv) /\
                       forall x, f x == vec_add (mat_vec_mul (fst mv) x) (snd mv))
            mat_v}.
Proof.
  intros. remember (existT _ _ (translation_isometric (vec_neg (f vec_zero)))) as T.
  remember (existT _ _ H) as A. remember (T & A). destruct s as [B ?H].
  assert (B == (fun x : Vector n => vec_add (vec_neg (f vec_zero)) (f x))). {
    destruct T, A. unfold bi_op, iso_binop in Heqs.
    apply EqdepFacts.eq_sigT_fst in Heqs. apply EqdepFacts.eq_sigT_fst in HeqT.
    apply EqdepFacts.eq_sigT_fst in HeqA. now subst x x0. }
  assert (B vec_zero == vec_zero) by
      (subst B; rewrite vec_add_comm; now autorewrite with vector).
  pose proof (isometric_fix_preserve_dot_prod _ H0 H2).
  apply preserve_dot_prod_mat_sig in H3. destruct H3 as [mat [[? ?] ?]].
  exists (mat, (f vec_zero)). red. split; intros.
  - rewrite orthogonal_mat_spec_1. split; auto. intros.
    rewrite <- H4, H1, vec_add_comm, <- vec_add_assoc. now autorewrite with vector.
  - destruct x' as [mat2 v]. simpl in *. destruct H6. f_equal.
    + apply H5. split. 1: apply H6. intros. subst B. rewrite !H7.
      autorewrite with matrix vector. rewrite vec_add_comm, vec_add_assoc.
      now autorewrite with vector.
    + rewrite H7. now autorewrite with matrix vector.
Qed.

Lemma orthogonal_mat_isometric: forall {n} (mat: Matrix n n) (v: Vector n),
    orthogonal_mat mat -> Isometric (fun x => vec_add (mat_vec_mul mat x) v).
Proof.
  intros. rewrite orthogonal_mat_spec_1 in H. apply mat_vec_mul_preserve_dot_prod in H.
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
  intros. apply isometric_orthogonal_mat in H. destruct H as [[mat v] [[? ?] _]].
  simpl in *. apply (affine_map_ext (fun x => vec_add v (mat_vec_mul mat x))).
  - intros. now rewrite H0, vec_add_comm.
  - apply affine_map_compose.
    + apply linear_map_is_affine, mat_vec_mul_linear_map.
    + apply vec_add_is_affine.
Qed.

Section ISOMETRY_ACTION.

  Context {n: nat}.

  Global Instance isometry_act: GrAct (Isometry n) (Vector n) := fun g x => ('g) x.

  Instance: Proper ((=) ==> (==) ==> (==)) isometry_act.
  Proof.
    intros [x] [y] ? a b ?. unfold isometry_act. subst. red in H.
    unfold iso_equiv in H. unfold cast, iso_rep in *. simpl in *. apply H.
  Qed.

  Global Instance isometryGroupAction: GroupAction (Isometry n) (Vector n).
  Proof.
    constructor; auto.
    - apply _.
    - intros [g] [h] ?. vm_compute. easy.
  Qed.

End ISOMETRY_ACTION.

Lemma isometry_subgroup_fix_one_point:
  forall {n} P `{!SubGroupCondition (Isometry n) P},
    SetoidFinite (Subpart (Isometry n) P) ->
    exists c, forall (g: Subpart (Isometry n) P), g ⊙ c == c.
Proof.
  intros n P SGC ?. destruct H as [m [l [? [? ?]]]].
  unfold gr_act, subgroup_act, gr_act, isometry_act.
  remember (vec_scal_mul
              (/ INR m)
              (@fold_right (Vector n) _ vec_add
                           vec_zero (map (fun x => (''x) vec_zero) l))) as c. exists c.
  intros [[g]]. unfold cast, iso_rep, subgroup_rep. simpl. rewrite Heqc at 1.
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
          - rewrite H. now constructor.
          - apply perm_trans with
                (map (fun x : Subpart (Isometry n) P => (' (' x)) vec_zero) l₂); auto.
          } apply H2. symmetry. now apply finite_group_left_perm.
      * rewrite map_map. apply map_ext. intros [[a]]. subst gg.
        unfold cast, iso_rep, subgroup_rep. now simpl.
  - rewrite fold_right_map, map_fst_combine. 2: now rewrite repeat_length, map_length.
    assert (forall r k, fold_right Rplus 0 (repeat r k) == Rmult (INR k) r). {
      intros. induction k. 1: simpl; ring. rewrite S_INR. simpl. rewrite IHk. ring. }
    rewrite map_length, H0, H2. apply Rinv_r, not_0_INR. destruct SGC, non_empty.
    specialize (H1 (exist _ x H3)). intro. subst m. now destruct l.
Qed.

Class TilingAxioms {n: nat} (pat: Ensemble (Vector n)) (P: Isometry n -> Prop)
      {SGC: SubGroupCondition (Isometry n) P}: Prop := {
  pattern_int_nonempty: interior pat =/= Empty_set;
  pattern_connected: connected_subspace pat;
  pattern_compact: compact_subspace pat;
  cover_all: IndexedUnion (fun g: Subpart (Isometry n) P => Im pat (g ⊙)) == Full_set;
  edge_overlap: forall g h: Subpart (Isometry n) P,
      Intersection (Im (interior pat) (g ⊙))
                   (Im (interior pat) (h ⊙)) =/= Empty_set ->
      Im pat (g ⊙) == Im pat (h ⊙);
  }.

Section TILING_PROP.

  Context {n: nat}.
  Variable pat : Ensemble (Vector n).
  Variable P : Isometry n -> Prop.
  Context {SGC: SubGroupCondition (Isometry n) P}.
  Hypothesis TiA: TilingAxioms pat P.

  (* 1.7.5.1 in Geometry I *)

  Lemma tiling_group_acts_discretely:
    forall (x: Vector n), discrete (orbit (Subpart (Isometry n) P) _ x).
  Proof.
    intros x. red. intros y ?. unfold orbit in H. destruct H as [g ?].
    rewrite (orbit_the_same _ _ g). rewrite <- H0. clear x g H H0. rename y into x.
  Abort.

End TILING_PROP.
