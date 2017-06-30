Require Import FormalMath.Infra.

(***************************************** Group *****************************************)

Class BinOp A := bi_op : A -> A -> A.
Infix "&" := bi_op (at level 50, left associativity) : math_scope.
Notation "(&)" := bi_op (only parsing) : math_scope.
Notation "( x &)" := (bi_op x) (only parsing) : math_scope.
Notation "(& x )" := (fun y => y & x) (only parsing) : math_scope.

Class GrUnit A := one : A.

Class Negate A := neg : A -> A.

Class Group (A : Type) {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A} : Prop :=
  {
    gr_as_setoid :> Setoid A;
    gr_op_proper :> Proper ((=) ==> (=) ==> (=)) (&);
    negate_proper :> Proper ((=) ==> (=)) neg;
    op_assoc : forall x y z, (x & y) & z = x & (y & z);
    one_left : forall x, one & x = x;
    neg_left : forall x, neg x & x = one
  }.

Coercion gr_as_setoid : Group >-> Setoid.

Class AbelianGroup (A : Type) {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A} : Prop :=
  {
    abgroup_as_group :> Group A;
    bi_op_comm : forall x y, x & y = y & x
  }.

(* Coercion abgroup_as_group : AbelianGroup >-> Group. *)

Section GROUP_PROP.

  Context `{G : Group A}.

  Lemma one_unique : forall x,  x & x = x -> x = one. Proof. intros; rewrite <- (one_left x), <- (neg_left x), op_assoc, H; auto. Qed.

  Lemma neg_right : forall x, x & neg x = one. Proof. intros; apply one_unique. rewrite <- op_assoc, (op_assoc x (neg x) x), neg_left, op_assoc, one_left; auto. Qed.

  Lemma one_right : forall x, x & one = x. Proof. intros; rewrite <- (neg_left x), <- op_assoc, neg_right, one_left; auto. Qed.

  Lemma eq_left : forall x y z, y = z <-> x & y = x & z.
  Proof.
    intros; split; intros.
    + rewrite H; auto.
    + rewrite <- one_left, <- (one_left z), <- (neg_left x), !op_assoc, H. auto.
  Qed.

  Lemma eq_right : forall x y z, y = z <-> y & x = z & x.
  Proof.
    intros; split; intros.
    + rewrite H; auto.
    + rewrite <- one_right, <- (one_right z), <- (neg_right x), <- !op_assoc, H; auto.
  Qed.

  Lemma neg_unique : forall x y, x & y = one -> y = neg x. Proof. intros; apply (eq_left x); rewrite H, neg_right; auto. Qed.

  Lemma double_neg : forall x, neg (neg x) = x. Proof. intro. generalize (neg_left x); intro. apply neg_unique in H. rewrite <- H; auto. Qed.

  Lemma neg_op : forall x y, neg (x & y) = neg y & neg x.
  Proof. intros. symmetry. apply neg_unique. rewrite <- op_assoc, (op_assoc x y (neg y)), neg_right, one_right, neg_right. auto. Qed.

  Lemma neg_one : neg one = one. Proof. apply one_unique. rewrite <- neg_op, one_right. auto. Qed.

  Lemma neg_iff : forall x y, x = y <-> neg x = neg y.
  Proof. intros; split; intros; [rewrite H | rewrite (eq_left (neg x)), neg_left; rewrite (eq_right y) in H; rewrite H, neg_left]; auto. Qed.

End GROUP_PROP.

(***************************************** SubGroup *****************************************)

Class SubGroup (A : Type) {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A} (PA : Pred A) : Prop :=
  {
    super_group :> Group A;
    sub_setoid :> SubSetoid A PA;
    not_empty : exists x, pred x;
    sub_criteria : forall x y : A, pred x -> pred y -> pred (x & (neg y))
  }.

Section SUB_GROUP_PROP.

  Context `(SA : SubGroup A).

  Lemma one_pred : pred one. Proof. destruct (not_empty) as [x ?H]. generalize (sub_criteria _ _ H H); intro. rewrite (neg_right x) in H0. auto. Qed.

  Lemma op_pred : forall x y : A, pred x -> pred y -> pred (x & y).
  Proof.
    intros. generalize one_pred; intro. generalize (sub_criteria _ _ H1 H0); intro. rewrite one_left in H2.
    generalize (sub_criteria _ _ H H2); intro. rewrite double_neg in H3. auto.
  Qed.

  Lemma neg_pred : forall x : A, pred x -> pred (neg x). Proof. intros. generalize one_pred; intro. generalize (sub_criteria _ _ H0 H); intro. rewrite one_left in H1. auto. Qed.

  Instance sg_op : BinOp (Sub PA). Proof. intros x y. destruct x as [x ?H]. destruct y as [y ?H]. exists (x & y). apply op_pred; auto. Defined.

  Instance sg_unit : GrUnit (Sub PA) := exist _ _ one_pred.

  Instance sg_negate : Negate (Sub PA). Proof. intro x. destruct x as [x ?H]. exists (neg x). apply neg_pred; auto. Defined.

  Lemma sg_neg_proj : forall (x : Sub PA), neg (proj1_sig x) = proj1_sig (sg_negate x). Proof. intros. destruct x. unfold proj1_sig, sg_negate. auto. Qed.

  Lemma sg_op_proj : forall (x y : Sub PA), proj1_sig x & proj1_sig y = proj1_sig (sg_op x y). Proof. intros; destruct x, y; unfold proj1_sig, sg_op; auto. Qed.

  Instance subgroup_as_group : Group (Sub PA).
  Proof.
    constructor.
    - exact (subsetoid_as_setoid sub_setoid).
    - repeat intro. destruct x as [x ?H]; destruct y as [y ?H]; destruct x0 as [x0 ?H]; destruct y0 as [y0 ?H].
      hnf in H, H0 |- *. unfold proj1_sig in H, H0 |- *. simpl. apply gr_op_proper; auto.
    - repeat intro. destruct x as [x ?H]; destruct y as [y ?H]. hnf in H |- *. unfold proj1_sig in H |- *. simpl. apply negate_proper; auto.
    - repeat intro. destruct x as [x ?H]; destruct y as [y ?H]; destruct z as [z ?H]. hnf. unfold proj1_sig. simpl. apply op_assoc.
    - intro. destruct x as [x ?H]. hnf. unfold proj1_sig. simpl. apply one_left.
    - intro. destruct x as [x ?H]. hnf. unfold proj1_sig. simpl. apply neg_left.
  Qed.

  Lemma normal_condition_equivalence : (forall x y : A, pred (x & y) -> pred (y & x)) <-> (forall a h, pred h -> exists h', pred h' /\ a & h = h' & a).
  Proof.
    split; intros.
    - specialize (H (h & (neg a)) a). exists (a & h & (neg a)). rewrite op_assoc, neg_left, one_right, <- op_assoc in H.
      specialize (H H0). split; auto. rewrite op_assoc, neg_left, one_right. auto.
    - specialize (H (neg x) (x & y) H0). destruct H as [h' [? ?]]. rewrite <- op_assoc, neg_left, one_left in H1. rewrite H1, op_assoc, neg_left, one_right. auto.
  Qed.

  Definition right_coset_rel : relation A := fun x y => pred (x & (neg y)).

  Instance equiv_right_coset : Equivalence right_coset_rel.
  Proof.
    constructor; hnf; unfold right_coset_rel; intros.
    - rewrite neg_right. apply one_pred.
    - apply neg_pred in H. rewrite neg_op in H. rewrite double_neg in H. auto.
    - pose proof (op_pred _ _ H H0). rewrite <- op_assoc, (op_assoc x (neg y) y), neg_left, one_right in H1. auto.
  Qed.

  Instance subrelation_right_coset : subrelation (=) right_coset_rel. Proof. repeat intro. unfold right_coset_rel. rewrite H. rewrite neg_right. apply one_pred. Qed.

  Instance right_coset_quotient_setoid : QuotientSetoid A (=) right_coset_rel.
  Proof. constructor; [exact gr_as_setoid | exact equiv_right_coset | exact subrelation_right_coset]. Qed.

End SUB_GROUP_PROP.

Existing Instance right_coset_quotient_setoid.

Arguments right_coset_rel [_ _ _] _.

(* Existing Instance subgroup_as_group. *)

(* Coercion subgroup_as_group : SubGroup >-> Group. *)

(***************************************** Group Homomorphism *****************************************)

Section GROUP_HOMOMORPHISM.

  Context `{Group A} `{Group B}.

  Class Group_Homomorphism (f : A -> B) :=
  {
    grmor_a : Group A;
    grmor_b : Group B;
    grmor_setmore :> Setoid_Morphism f;
    preserve_gr_op : forall x y, f (x & y) = f x & f y
  }.

End GROUP_HOMOMORPHISM.

Section GROUP_HOMOMORPHISMS_PROP.

  Context `{GA : Group A} `{GB : Group B} {f : A -> B} `{GH : !Group_Homomorphism f}.

  Lemma preserve_gr_unit : f one = one. Proof. intros. pose proof (preserve_gr_op (one : A) one). rewrite (one_left one) in H. symmetry in H. apply one_unique in H. auto. Qed.

  Lemma preserve_negate : forall x, f (neg x) = neg (f x). Proof. intros. rewrite (eq_left (f x)). rewrite <- preserve_gr_op. rewrite 2!neg_right. apply preserve_gr_unit. Qed.

  Instance kernel_pred : Pred A := fun x => f x = one.

  Instance image_pred : Pred B := fun x => exists o, f o = x.

  Instance homm_kernel_subgroup : SubGroup A kernel_pred.
  Proof.
    constructor.
    + exact GA.
    + constructor. 1 : exact GA. repeat intro. unfold pred, kernel_pred. rewrite H. tauto.
    + exists one. unfold pred. apply preserve_gr_unit.
    + unfold pred, kernel_pred. intros. rewrite preserve_gr_op, preserve_negate, H, H0. apply neg_right.
  Qed.

  Definition homm_image_subgroup : SubGroup B image_pred.
  Proof.
    constructor.
    + exact GB.
    + constructor. 1 : exact GB. repeat intro. unfold pred, image_pred. split; intros; destruct H0 as [o ?]; exists o; rewrite H0; [|symmetry]; auto.
    + exists one. exists one. apply preserve_gr_unit.
    + unfold pred, image_pred. intros. destruct H as [xo ?]. destruct H0 as [yo ?]. exists (xo & neg yo). rewrite <- H, <- H0.
      rewrite <- preserve_negate. apply preserve_gr_op.
  Qed.

  Definition image_f : A -> Sub (image_pred). Proof. unfold Sub, image_pred. intro m. exists (f m). unfold pred. exists m. auto. Defined.

End GROUP_HOMOMORPHISMS_PROP.

Arguments kernel_pred [_ _ _ _] _.

Arguments image_pred [_ _ _] _.

Section GROUP_ISOMORPHISM.

  Context `{Group A} `{Group B} (f : A -> B).

  Class Group_Isomorphism :=
    {
      giso_homo :> Group_Homomorphism f;
      giso_f_bij :> Bijective f
    }.

End GROUP_ISOMORPHISM.

(***************************************** Normal SubGroup *****************************************)

Class NormalSubGroup (A : Type) {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A} (PA : Pred A) : Prop :=
  {
    normal_subgroup_as_subgroup :> SubGroup A PA;
    normal_comm : forall (x y : A), pred (x & y) -> pred (y & x);
  }.

Section NORMAL_SUBGROUP.

  Context `{NSG : NormalSubGroup A}.

  Instance quotient_group_by_normal_subgroup : @Group A (right_coset_rel PA) _ _ _.
  Proof.
    pose proof normal_subgroup_as_subgroup. pose proof (@super_group _ _ _ _ _ _ normal_subgroup_as_subgroup).
    constructor; [ | repeat intro; unfold equiv, right_coset_rel in * ..].
    - apply equiv_right_coset; auto.
    - rewrite neg_op, <- op_assoc. apply normal_comm. rewrite <- !op_assoc, (op_assoc (neg y & x)). apply normal_comm, op_pred; auto. apply normal_comm. auto.
    - rewrite double_neg, <- (double_neg (neg x & y)). apply neg_pred; auto. rewrite neg_op, double_neg. apply normal_comm. auto.
    - rewrite <- op_assoc. rewrite neg_right. apply one_pred; auto.
    - rewrite op_assoc, neg_right, one_right. apply one_pred; auto.
    - rewrite neg_left, neg_right. apply one_pred; auto.
  Qed.

  Instance normal_subgroup_natural_homm : @Group_Homomorphism A Ae _ _ _ _ (right_coset_rel PA) _ _ _ id.
  Proof. constructor; [exact super_group | exact quotient_group_by_normal_subgroup | exact quotient_setoid_natural_morph | intros; unfold id; auto]. Qed.

End NORMAL_SUBGROUP.

Section FIRST_ISOMORPHISM_THEOREM.

  Context `{GA : Group A} `{GB : Group B} {f : A -> B} `{GH : !Group_Homomorphism f}.

  Instance homm_kernel_normal_subgroup : NormalSubGroup A (kernel_pred f).
  Proof.
    constructor; [exact homm_kernel_subgroup | unfold pred, kernel_pred; intros x y; rewrite !preserve_gr_op; intros; apply neg_unique in H; rewrite H; apply neg_left].
  Qed.

  Notation iso_a := (@quotient_group_by_normal_subgroup A _ _ _ _ _ homm_kernel_normal_subgroup).

  Notation iso_b := (subgroup_as_group homm_image_subgroup).

  Theorem image_f_setoid_morph : @Setoid_Morphism A (right_coset_rel (kernel_pred f)) (Sub (image_pred f)) (sub_equiv (image_pred f)) image_f.
  Proof.
    constructor.
    - exact (@gr_as_setoid _ _ _ _ _ iso_a).
    - exact (@gr_as_setoid _ _ _ _ _ iso_b).
    - repeat intro. unfold image_f, equiv, sub_equiv, proj1_sig. unfold equiv, right_coset_rel, pred, kernel_pred in H.
      rewrite preserve_gr_op in H. rewrite preserve_negate in H. rewrite (eq_right (neg (f y))), neg_right. auto.
  Qed.

  Theorem first_isomorphism_theorem : @Group_Isomorphism
                                       A (right_coset_rel (kernel_pred f)) _ _ _
                                       (Sub (image_pred f)) _ (sg_op homm_image_subgroup) (sg_unit homm_image_subgroup) (sg_negate homm_image_subgroup) image_f.
  Proof.
    constructor; constructor.
    - exact iso_a.
    - exact iso_b.
    - exact image_f_setoid_morph.
    - intros x y. unfold image_f, equiv, sub_equiv, proj1_sig. simpl. apply preserve_gr_op.
    - constructor.
      + unfold image_f, equiv, sub_equiv, proj1_sig, right_coset_rel, pred, kernel_pred. intros. rewrite preserve_gr_op, preserve_negate, H, neg_right; auto.
      + exact image_f_setoid_morph.
    - constructor.
      + intros x. destruct x as [x ?H]. unfold image_f, equiv, sub_equiv, proj1_sig. unfold pred, image_pred in H. destruct H as [o ?]. exists o; auto.
      + exact image_f_setoid_morph.
  Qed.

End FIRST_ISOMORPHISM_THEOREM.

Definition sub_prod_pred {A} {Ae : Equiv A} {Aop : BinOp A} (P1 P2 : Pred A) : Pred A := fun m => exists (a1 : Sub P1) (a2 : Sub P2), m = (proj1_sig a1) & (proj1_sig a2).

Definition sub_int_pred {A} (P1 P2 : Pred A) : Pred A := fun m => (@pred _ P1) m /\ (@pred _ P2) m.

Section SUBGROUP_CONSTRUNCTION.

  Context `{G : Group A} `(S1 : !SubGroup A P1) `(S2 : !SubGroup A P2).

  Lemma fst_in_sub_prod : forall (x : Sub P1), sub_prod_pred P1 P2 (proj1_sig x).
  Proof. intros. exists x, (sg_unit S2). destruct x. unfold sg_unit, proj1_sig. rewrite one_right; auto. Qed.

  Lemma snd_in_sub_prod : forall (x : Sub P2), sub_prod_pred P1 P2 (proj1_sig x).
  Proof. intros. exists (sg_unit S1), x. destruct x. unfold sg_unit, proj1_sig. rewrite one_left; auto. Qed.

  Lemma sub_prod_is_subgroup : pointwise_relation A impl (sub_prod_pred P2 P1) (sub_prod_pred P1 P2) -> SubGroup A (sub_prod_pred P1 P2).
  Proof.
    unfold pointwise_relation, sub_prod_pred. intros. constructor; auto.
    - constructor. 1 : exact gr_as_setoid. repeat intro. unfold pred. split; intros.
      + destruct H1 as [a1 [a2 ?]]. rewrite H0 in H1. exists a1, a2. auto.
      + destruct H1 as [a1 [a2 ?]]. rewrite <- H0 in H1. exists a1, a2. auto.
    - unfold pred. exists one, (sg_unit S1), (sg_unit S2). unfold sg_unit. simpl. rewrite one_left; auto.
    - unfold pred. intros. destruct H0 as [x1 [x2 ?]]. destruct H1 as [y1 [y2 ?]]. rewrite neg_iff, neg_op in H1. rewrite (sg_neg_proj S1), (sg_neg_proj S2) in H1.
      assert (exists (ny1 : Sub P1) (ny2 : Sub P2), neg y = proj1_sig ny1 & proj1_sig ny2) by (apply H; exists (sg_negate S2 y2), (sg_negate S1 y1); auto).
      destruct H2 as [ny1 [ny2 ?]]. assert (exists (nny1 : Sub P1) (nx2 : Sub P2), proj1_sig x2 & proj1_sig ny1 = proj1_sig nny1 & proj1_sig nx2) by
          (apply H; exists x2, ny1; auto). destruct H3 as [nny1 [nx2 ?]]. exists (sg_op S1 x1 nny1), (sg_op S2 nx2 ny2). rewrite H0, H2.
      rewrite <- op_assoc, (op_assoc (proj1_sig x1)), H3, <- (sg_op_proj S1), <- (sg_op_proj S2), <- !op_assoc. auto.
  Qed.

  Lemma sub_prod_is_subgroup_necessary : SubGroup A (sub_prod_pred P1 P2) -> pointwise_relation A iff (sub_prod_pred P1 P2) (sub_prod_pred P2 P1).
  Proof.
    intros. unfold pointwise_relation. intros. split; intros.
    - apply (neg_pred H) in H0. destruct H0 as [a1 [a2 ?]]. rewrite neg_iff, double_neg, neg_op, (sg_neg_proj S1), (sg_neg_proj S2) in H0.
      exists (sg_negate S2 a2), (sg_negate S1 a1). auto.
    - destruct H0 as [a2 [a1 ?]]. pose proof (op_pred H _ _ (snd_in_sub_prod a2) (fst_in_sub_prod a1)). unfold pred, sub_prod_pred in H1. destruct H1 as [b1 [b2 ?]].
      rewrite <- H0 in H1. exists b1, b2. auto.
  Qed.

  Lemma sub_prod_is_subgroup_iff : SubGroup A (sub_prod_pred P1 P2) <-> pointwise_relation A iff (sub_prod_pred P1 P2) (sub_prod_pred P2 P1).
  Proof. split; intros; [ apply sub_prod_is_subgroup_necessary | apply sub_prod_is_subgroup; unfold pointwise_relation in *; intros; destruct (H a)]; auto. Qed.

  Instance sub_int_subgroup : SubGroup A (sub_int_pred P1 P2).
  Proof.
    constructor; auto.
    - constructor. 1 : exact gr_as_setoid. repeat intro. unfold pred, sub_int_pred. rewrite H. intuition.
    - exists one. unfold pred, sub_int_pred. split. apply (one_pred S1). apply (one_pred S2).
    - intros x y. unfold pred, sub_int_pred. intros. destruct H, H0. split; apply sub_criteria; auto.
  Qed.

End SUBGROUP_CONSTRUNCTION.
