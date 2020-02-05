(** * Lɪʙʀᴀʀʏ ᴀʙᴏᴜᴛ Isᴏᴍᴇᴛʀɪᴇs ᴏғ Eᴜᴄʟɪᴅᴇᴀɴ Sᴘᴀᴄᴇ *)
(** * Aᴜᴛʜᴏʀ: 𝕾𝖍𝖊𝖓𝖌𝖞𝖎 𝖂𝖆𝖓𝖌 *)

Require Import FormalMath.Matrix.
Require Import FormalMath.Group.
Require Import FormalMath.FiniteGroup.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.SetoidPermutation.

Open Scope R_scope.

Definition norm {n} (v: Vector n) := sqrt (vec_dot_prod v v).

Definition distance {n} (x y: Vector n) := norm (vec_add x (vec_neg y)).

Lemma polarization_identity: forall {n} (u v: Vector n),
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

Lemma vec_dot_prod_distance: forall {n} (u v: Vector n),
    vec_dot_prod u v ==
    ((distance u vec_zero)² + (distance v vec_zero)² - (distance u v)²) * / 2.
Proof.
  intros. unfold distance. autorewrite with vector. apply polarization_identity.
Qed.

Class Isometric {n} (f: Vector n -> Vector n) :=
  {
    iso_inv: Vector n -> Vector n;
    iso_inj: forall x y, f x == f y -> x == y;
    iso_surj: forall x, f (iso_inv x) == x;
    distance_preserve: forall x y, distance x y == distance (f x) (f y)
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
    red in S. unfold distance.
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
  - rewrite <- vec_add_id_l, <- (vec_add_id_l x), <- (vec_add_inv (vec_neg v)).
    autorewrite with vector. now rewrite !vec_add_assoc, H.
  - rewrite <- vec_add_assoc. now autorewrite with vector.
  - unfold distance. rewrite vec_neg_add, (vec_add_comm v x), vec_add_assoc,
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
    - transitivity (distance (f2 x) (f2 y)); apply distance_preserve.
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

Lemma isometry_subgroup_fix_one_point:
  forall {n} P `{!SubGroupCondition (Isometry n) P},
    SetoidFinite (Subpart (Isometry n) P) ->
    exists c, forall (g: Subpart (Isometry n) P), (''g) c == c.
Proof.
  intros n P SGC ?. destruct H as [m [l [? [? ?]]]].
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
