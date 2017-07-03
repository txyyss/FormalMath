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

Section GROUP_IFF.

  Context (A : Type) {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A}.

  Definition trivial_pred : Pred A := fun _ => True.

  Lemma setoid_iff : Setoid A <-> Setoid (Sub trivial_pred).
  Proof.
    split; intros.
    - hnf. apply sub_equivalence. constructor; auto. repeat intro. unfold pred; intuition.
    - hnf. hnf in H. unfold equiv in H. unfold trivial_pred, sub_equiv in H. destruct H. constructor.
      + unfold Reflexive in *. intros. specialize (Equivalence_Reflexive (exist _ x I)). simpl in *. auto.
      + unfold Symmetric in *. intros. specialize (Equivalence_Symmetric (exist _ x I) (exist _ y I)). simpl in *. auto.
      + unfold Transitive in *. intros. specialize (Equivalence_Transitive (exist _ x I) (exist _ y I)(exist _ z I)). simpl in *. auto.
  Qed.

  Instance trivial_op : BinOp (Sub trivial_pred) := fun x y => exist _ (proj1_sig x & proj1_sig y) I.

  Instance trivial_unit : GrUnit (Sub trivial_pred) := exist _ one I.

  Instance trivial_neg : Negate (Sub trivial_pred) := fun x => exist _ (neg (proj1_sig x)) I.

  Lemma group_iff : Group A <-> Group (Sub trivial_pred).
  Proof.
    intros. split; intros; constructor; repeat intro.
    - rewrite <- setoid_iff. exact H.
    - destruct x, y, x0, y0. unfold equiv, sub_equiv, proj1_sig, pred, trivial_pred in *. simpl. rewrite H0, H1. auto.
    - destruct x, y. unfold equiv, sub_equiv, proj1_sig in *. simpl. rewrite H0. auto.
    - destruct x, y, z. unfold equiv, sub_equiv, proj1_sig in *. simpl. rewrite op_assoc. auto.
    - destruct x. unfold equiv, sub_equiv, proj1_sig, bi_op, trivial_op in *. simpl. apply one_left.
    - destruct x. unfold equiv, sub_equiv, bi_op, trivial_op, neg, trivial_neg, proj1_sig in *. simpl. apply neg_left.
    - rewrite setoid_iff. exact H.
    - exact (@gr_op_proper _ _ _ _ _ H (exist _ x I) (exist _ y I) H0 (exist _ x0 I) (exist _ y0 I) H1).
    - exact (@negate_proper _ _ _ _ _ H (exist _ x I) (exist _ y I) H0).
    - exact (@op_assoc _ _ _ _ _ H (exist _ x I) (exist _ y I) (exist _ z I)).
    - exact (@one_left _ _ _ _ _ H (exist _ x I)).
    - exact (@neg_left _ _ _ _ _ H (exist _ x I)).
Qed.

End GROUP_IFF.

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

Section SUBGROUP_PROP.

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

  Lemma normal_condition_iff_right : (forall x y : A, pred (x & y) -> pred (y & x)) <-> (forall a h, pred h -> exists h', pred h' /\ a & h = h' & a).
  Proof.
    split; intros.
    - specialize (H (h & (neg a)) a). exists (a & h & (neg a)). rewrite op_assoc, neg_left, one_right, <- op_assoc in H.
      specialize (H H0). split; auto. rewrite op_assoc, neg_left, one_right. auto.
    - specialize (H (neg x) (x & y) H0). destruct H as [h' [? ?]]. rewrite <- op_assoc, neg_left, one_left in H1. rewrite H1, op_assoc, neg_left, one_right. auto.
  Qed.

  Lemma normal_condition_iff_left : (forall x y : A, pred (x & y) -> pred (y & x)) <-> (forall a h, pred h -> exists h', pred h' /\ h & a = a & h').
  Proof.
    split; intros.
    - specialize (H a (neg a & h)). exists (neg a & h & a). rewrite <- op_assoc, neg_right, one_left in H.
      specialize (H H0). split; auto. rewrite op_assoc, <- op_assoc, neg_right, one_left. auto.
    - specialize (H (neg y) (x & y) H0). destruct H as [h' [? ?]]. rewrite op_assoc, neg_right, one_right in H1. rewrite H1, <- op_assoc, neg_right, one_left. auto.
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
  Proof. constructor; [exact super_group | exact equiv_right_coset | exact subrelation_right_coset]. Qed.

End SUBGROUP_PROP.

Existing Instance right_coset_quotient_setoid.

Existing Instance sg_op.

Existing Instance sg_unit.

Existing Instance sg_negate.

Arguments right_coset_rel [_ _ _] _.

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

  Context {A : Type} {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A}.
  Context {B : Type} {Be : Equiv B} {Bop : BinOp B} {Bunit : GrUnit B} {Bnegate : Negate B}.
  Context {f : A -> B} `{GH : !Group_Homomorphism f}.

  Lemma preserve_gr_unit : f one = one.
  Proof. intros. destruct GH. pose proof (preserve_gr_op (one : A) one). rewrite (one_left one) in H. symmetry in H. apply one_unique in H. auto. Qed.

  Lemma preserve_negate : forall x, f (neg x) = neg (f x).
  Proof. intros. destruct GH. rewrite (eq_left (f x)). rewrite <- preserve_gr_op. rewrite 2!neg_right. apply preserve_gr_unit. Qed.

  Instance kernel_pred : Pred A := fun x => f x = one.

  Instance image_pred : Pred B := fun x => exists o, f o = x.

  Instance homm_kernel_subgroup : SubGroup A kernel_pred.
  Proof.
    assert (GA: Group A) by (destruct GH; auto). assert (GB: Group B) by (destruct GH; auto). constructor.
    + exact GA.
    + constructor. 1 : exact GA. repeat intro. unfold pred, kernel_pred. rewrite H. tauto.
    + exists one. unfold pred. apply preserve_gr_unit.
    + unfold pred, kernel_pred. intros. rewrite preserve_gr_op, preserve_negate, H, H0. apply neg_right.
  Qed.

  Instance homm_image_subgroup : SubGroup B image_pred.
  Proof.
    assert (GA: Group A) by (destruct GH; auto). assert (GB: Group B) by (destruct GH; auto). constructor.
    + exact GB.
    + constructor. 1 : exact GB. repeat intro. unfold pred, image_pred. split; intros; destruct H0 as [o ?]; exists o; rewrite H0; [|symmetry]; auto.
    + exists one. exists one. apply preserve_gr_unit.
    + unfold pred, image_pred. intros. destruct H as [xo ?]. destruct H0 as [yo ?]. exists (xo & neg yo). rewrite <- H, <- H0.
      rewrite <- preserve_negate. apply preserve_gr_op.
  Qed.

  Definition image_f : A -> Sub (image_pred). Proof. unfold Sub, image_pred. intro m. exists (f m). unfold pred. exists m. auto. Defined.

  Context {C : Type} {Ce : Equiv C} {Cop : BinOp C} {Cunit : GrUnit C} {Cnegate : Negate C}.
  Context {g: B -> C} `{GH' : !Group_Homomorphism g}.

  Instance group_homomorphism_trans: Group_Homomorphism (compose g f).
  Proof.
    assert (GA: Group A) by (destruct GH; auto). assert (GC: Group C) by (destruct GH'; auto). constructor; [exact GA | exact GC | .. ].
    - destruct GH, GH'. apply setoid_morphism_trans; auto.
    - intros. unfold compose. rewrite preserve_gr_op. rewrite preserve_gr_op. auto.
  Qed.

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

Section GROUP_ISOMORPHISM_PROP.

    Context {A : Type} {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A}.
    Context {B : Type} {Be : Equiv B} {Bop : BinOp B} {Bunit : GrUnit B} {Bnegate : Negate B}.
    Context {C : Type} {Ce : Equiv C} {Cop : BinOp C} {Cunit : GrUnit C} {Cnegate : Negate C}.
    Context {f: A -> B} {g: B -> C} `{GH: !Group_Isomorphism f} `{GH': !Group_Isomorphism g}.

    Instance group_isomorphism_trans: Group_Isomorphism (compose g f). Proof. constructor; [apply group_homomorphism_trans | destruct GH, GH'; apply bijective_trans; auto]. Qed.

End GROUP_ISOMORPHISM_PROP.

Section SUBGROUP_IFF.

  Context `{G : Group A} {P1 P2 : Pred A}.

  Lemma pred_equiv_subgroup_iff : pred_equiv P1 P2 -> SubGroup A P1 <-> SubGroup A P2.
  Proof.
    unfold pred_equiv, pointwise_relation. intros. split; intros; constructor; auto.
    - rewrite <- (pred_equiv_subsetoid_iff H). exact sub_setoid.
    - destruct not_empty as [x ?]. exists x. rewrite <- H. auto.
    - intros. rewrite <- H in H1. rewrite <- H in H2. rewrite <- H. apply sub_criteria; auto.
    - rewrite (pred_equiv_subsetoid_iff H). exact sub_setoid.
    - destruct not_empty as [x ?]. exists x. rewrite H. auto.
    - intros. rewrite H in H1. rewrite H in H2. rewrite H. apply sub_criteria; auto.
  Qed.

  Context (G1: SubGroup A P1) (G2: SubGroup A P2).

  Hypothesis (H: pred_equiv P1 P2).

  Lemma iff_sub_map_ok: forall x : Sub P1, @pred A P2 (proj1_sig x). Proof. intros. destruct x as [x ?H]. hnf in H. simpl. destruct (H x). apply H1. auto. Qed.

  Definition iff_sub_map (x: Sub P1) : (Sub P2) := exist _ (proj1_sig x) (iff_sub_map_ok x).

  Lemma iff_sub_inv_ok: forall x : Sub P2, @pred A P1 (proj1_sig x). Proof. intros. destruct x as [x ?H]. hnf in H. simpl. destruct (H x). apply H2. auto. Qed.
  
  Definition iff_sub_inv (x: Sub P2) : (Sub P1) := exist _ (proj1_sig x) (iff_sub_inv_ok x).

  Lemma iff_setoid_morphism: Setoid_Morphism iff_sub_map.
  Proof. constructor; [exact (subgroup_as_group G1) | exact (subgroup_as_group G2) | repeat intro; unfold iff_sub_map; unfold equiv, sub_equiv in *; simpl; auto]. Qed.
  
  Lemma iff_group_isomorphism: Group_Isomorphism iff_sub_map.
  Proof.
    constructor; constructor; [exact (subgroup_as_group G1) | exact (subgroup_as_group G2) | exact iff_setoid_morphism | | |].
    - intros. unfold iff_sub_map. unfold bi_op at 3. unfold equiv, sub_equiv. simpl. destruct x as [x ?]. destruct y as [y ?]. simpl. auto.
    - constructor. 2: exact iff_setoid_morphism. intros x y. unfold iff_sub_map. unfold equiv, sub_equiv. unfold sub_equiv. simpl. auto.
    - constructor. 2: exact iff_setoid_morphism. intros x. exists (iff_sub_inv x). unfold iff_sub_map, iff_sub_inv, equiv, sub_equiv. simpl. auto.
  Qed.

End SUBGROUP_IFF.

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

  Lemma normal_subgroup_op_right: forall (h: Sub PA) (a: A), exists h': Sub PA, a & proj1_sig h = proj1_sig h' & a.
  Proof.
    intros. destruct h as [h ?H]. pose proof normal_comm. rewrite normal_condition_iff_right in H0. 2: exact normal_subgroup_as_subgroup. specialize (H0 a h H).
    destruct H0 as [h' [? ?]]. simpl. exists (exist _ h' H0). simpl; auto.
  Qed.

  Lemma normal_subgroup_op_left: forall (h: Sub PA) (a: A), exists h': Sub PA, proj1_sig h & a = a & proj1_sig h'.
  Proof.
    intros. destruct h as [h ?H]. pose proof normal_comm. rewrite normal_condition_iff_left in H0. 2: exact normal_subgroup_as_subgroup. specialize (H0 a h H).
    destruct H0 as [h' [? ?]]. simpl. exists (exist _ h' H0). simpl; auto.
  Qed.
  
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
    - exact iso_a.
    - exact iso_b.
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

Section SUBGROUP_CONSTRUNCTION.

  Context {A : Type} {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A} {Anegate : Negate A}.
  Context `(S1 : !SubGroup A P1) `(S2 : !SubGroup A P2).

  Lemma fst_in_sub_prod : forall (x : Sub P1), sub_prod_pred P1 P2 (proj1_sig x).
  Proof. intros. exists x, (sg_unit S2). destruct x. unfold sg_unit, proj1_sig. rewrite one_right; auto. Qed.

  Lemma snd_in_sub_prod : forall (x : Sub P2), sub_prod_pred P1 P2 (proj1_sig x).
  Proof. intros. exists (sg_unit S1), x. destruct x. unfold sg_unit, proj1_sig. rewrite one_left; auto. Qed.

  Lemma sub_prod_is_subgroup : pred_impl (sub_prod_pred P2 P1) (sub_prod_pred P1 P2) -> SubGroup A (sub_prod_pred P1 P2).
  Proof.
    unfold pred_impl, pointwise_relation, sub_prod_pred. intros. constructor; auto.
    - exact super_group.
    - constructor. 1: exact super_group. repeat intro. unfold pred. split; intros.
      + destruct H1 as [a1 [a2 ?]]. rewrite H0 in H1. exists a1, a2. auto.
      + destruct H1 as [a1 [a2 ?]]. rewrite <- H0 in H1. exists a1, a2. auto.
    - unfold pred. exists one, (sg_unit S1), (sg_unit S2). unfold sg_unit. simpl. rewrite one_left; auto.
    - unfold pred. intros. destruct H0 as [x1 [x2 ?]]. destruct H1 as [y1 [y2 ?]]. rewrite neg_iff, neg_op in H1. rewrite (sg_neg_proj S1), (sg_neg_proj S2) in H1.
      assert (exists (ny1 : Sub P1) (ny2 : Sub P2), neg y = proj1_sig ny1 & proj1_sig ny2) by (apply H; exists (sg_negate S2 y2), (sg_negate S1 y1); auto).
      destruct H2 as [ny1 [ny2 ?]]. assert (exists (nny1 : Sub P1) (nx2 : Sub P2), proj1_sig x2 & proj1_sig ny1 = proj1_sig nny1 & proj1_sig nx2) by
          (apply H; exists x2, ny1; auto). destruct H3 as [nny1 [nx2 ?]]. exists (sg_op S1 x1 nny1), (sg_op S2 nx2 ny2). rewrite H0, H2.
      rewrite <- op_assoc, (op_assoc (proj1_sig x1)), H3, <- (sg_op_proj S1), <- (sg_op_proj S2), <- !op_assoc. auto.
  Qed.

  Lemma sub_prod_is_subgroup_necessary : SubGroup A (sub_prod_pred P1 P2) -> pred_equiv (sub_prod_pred P1 P2) (sub_prod_pred P2 P1).
  Proof.
    intros. unfold pointwise_relation. intros. split; intros.
    - apply (neg_pred H) in H0. destruct H0 as [a1 [a2 ?]]. rewrite neg_iff, double_neg, neg_op, (sg_neg_proj S1), (sg_neg_proj S2) in H0.
      exists (sg_negate S2 a2), (sg_negate S1 a1). auto.
    - destruct H0 as [a2 [a1 ?]]. pose proof (op_pred H _ _ (snd_in_sub_prod a2) (fst_in_sub_prod a1)). unfold pred, sub_prod_pred in H1. destruct H1 as [b1 [b2 ?]].
      rewrite <- H0 in H1. exists b1, b2. auto.
  Qed.

  Lemma sub_prod_is_subgroup_iff : SubGroup A (sub_prod_pred P1 P2) <-> pred_equiv (sub_prod_pred P1 P2) (sub_prod_pred P2 P1).
  Proof. split; intros; [apply sub_prod_is_subgroup_necessary | apply sub_prod_is_subgroup; rewrite pred_equiv_impl in H; destruct H]; auto. Qed.

  Instance sub_int_subgroup : SubGroup A (sub_int_pred P1 P2).
  Proof.
    constructor; auto.
    - exact super_group.
    - constructor. 1 : exact super_group. repeat intro. unfold pred, sub_int_pred. rewrite H. intuition.
    - exists one. unfold pred, sub_int_pred. split. apply (one_pred S1). apply (one_pred S2).
    - intros x y. unfold pred, sub_int_pred. intros. destruct H, H0. split; apply sub_criteria; auto.
  Qed.

  Instance subsub_int_subgroup : SubGroup (Sub P1) (subsub_int_pred P1 P2).
  Proof.
    constructor.
    - exact (subgroup_as_group S1).
    - constructor. 1 : exact (subgroup_as_group S1). repeat intro. unfold equiv, sub_equiv in H. unfold pred, subsub_int_pred. rewrite H. tauto.
    - exists (sg_unit S1). unfold pred, subsub_int_pred, sg_unit. simpl. apply one_pred; auto.
    - unfold pred, subsub_int_pred. intros. destruct x as [x ?]. destruct y as [y ?]. simpl in *. apply sub_criteria; auto.
  Qed.

  Notation iso_a := (subgroup_as_group sub_int_subgroup).

  Notation iso_b := (subgroup_as_group subsub_int_subgroup).

  Lemma subgroup_setoid_morphism : Setoid_Morphism (sub_subsub P1 P2).
  Proof.
    constructor; [exact iso_a | exact iso_b |]. intros x y. unfold equiv, sub_equiv, sub_subsub.
    destruct x as [x [?H ?H]]. destruct y as [y [?H ?H]]. simpl. intros. unfold equiv. simpl. auto.
  Qed.

  Lemma subgroup_has_isomorphism : Group_Isomorphism (sub_subsub P1 P2).
  Proof.
    constructor; constructor.
    - exact iso_a.
    - exact iso_b.
    - exact subgroup_setoid_morphism.
    - intros. destruct x as [x [?H ?H]]. destruct y as [y [?H ?H]]. unfold sub_subsub. unfold bi_op. simpl. unfold equiv, sub_equiv. simpl. unfold equiv. simpl. reflexivity.
    - constructor. 2 : exact subgroup_setoid_morphism. intros x y. destruct x as [x [?H ?H]]. destruct y as [y [?H ?H]].
      unfold sub_subsub. unfold equiv, sub_equiv. simpl. unfold equiv. simpl. intuition.
    - constructor. 2 : exact subgroup_setoid_morphism. intros. exists (subsub_sub P1 P2 x). destruct x as [[x ?H] ?H]. unfold pred, subsub_int_pred in H0. simpl in H0.
      unfold sub_subsub, equiv, sub_equiv. simpl. unfold equiv. simpl. reflexivity.
  Qed.

End SUBGROUP_CONSTRUNCTION.

Section SECOND_ISOMORPHISM_THEOREM.

  Context `{G : Group A} `(H : !SubGroup A PH) `(N : !NormalSubGroup A PN).

  Notation N_SG := (@normal_subgroup_as_subgroup _ _ _ _ _ _ N).
  
  Instance normal_subsub_int_subgroup : NormalSubGroup (Sub PH) (subsub_int_pred PH PN).
  Proof.
    constructor. 1 : exact (subsub_int_subgroup H N_SG). intros x y. destruct x as [x ?H]. destruct y as [y ?H].
    unfold pred, subsub_int_pred. simpl. intros. destruct N. apply normal_comm0; auto.
  Qed.

  Lemma normal_subgroup_comm_impl : pred_impl (sub_prod_pred PN PH) (sub_prod_pred PH PN).
  Proof.
    hnf. intros. cut ((@pred A (sub_prod_pred PN PH) a) -> (@pred A (sub_prod_pred PH PN) a)); auto. unfold pred, sub_prod_pred. intros. destruct H0 as [a1 [a2 ?]].
    destruct (normal_subgroup_op_left a1 (proj1_sig a2)) as [h' ?]. rewrite <- H0 in H1. exists a2, h'; auto.
  Qed.

  Instance HN_SUB : SubGroup A (sub_prod_pred PH PN) := sub_prod_is_subgroup H N_SG normal_subgroup_comm_impl.

  Notation HN := (subgroup_as_group HN_SUB).

  Notation NsHN := (sub_int_subgroup HN_SUB N_SG).

  Instance NssHN : SubGroup (Sub (sub_prod_pred PH PN)) (subsub_int_pred (sub_prod_pred PH PN) PN) := (subsub_int_subgroup HN_SUB N_SG).
  
  Lemma N_is_HN_int_N: pred_equiv PN (sub_int_pred (sub_prod_pred PH PN) PN).
  Proof.
    hnf. intros. unfold pred at 2. unfold sub_int_pred, sub_prod_pred. intuition. unfold pred. exists (sg_unit H), (exist _ a H0). unfold sg_unit. simpl. rewrite one_left. auto.
  Qed.

  Instance N_HN_in_N_isomorphism: Group_Isomorphism (compose (sub_subsub (sub_prod_pred PH PN) PN) (iff_sub_map N_is_HN_int_N)).
  Proof.
    apply @group_isomorphism_trans with (Be := (sub_equiv (sub_int_pred (sub_prod_pred PH PN) PN))) (Bop := sg_op NsHN) (Bunit := sg_unit NsHN) (Bnegate := sg_negate NsHN).
    - apply iff_group_isomorphism.
    - apply (subgroup_has_isomorphism HN_SUB N_SG).
  Qed.

  Instance N_is_normal_subgroup_of_HN : NormalSubGroup (Sub (sub_prod_pred PH PN)) (subsub_int_pred (sub_prod_pred PH PN) PN).
  Proof. constructor; [exact NssHN |]. intros x y. destruct x as [x ?H]. destruct y as [y ?H]. unfold pred, subsub_int_pred, sub_prod_pred. simpl. apply normal_comm. Qed.

  Lemma second_f_ok: forall (x : Sub PH), (@pred _ (sub_prod_pred PH PN)) (proj1_sig x).
  Proof. intros; exists x, (sg_unit N_SG). unfold sg_unit. simpl. rewrite one_right. auto. Qed.

  Definition second_f (x : Sub PH) : Sub (sub_prod_pred PH PN) := exist _ (proj1_sig x) (second_f_ok x).

  Notation iso_a := (@quotient_group_by_normal_subgroup _ _ _ _ _ _ normal_subsub_int_subgroup).

  Notation iso_b := (@quotient_group_by_normal_subgroup _ _ _ _ _ _ N_is_normal_subgroup_of_HN).

  Theorem second_f_setoid_morph : @Setoid_Morphism (Sub PH) (right_coset_rel (subsub_int_pred PH PN))
                                                   (Sub (sub_prod_pred PH PN)) (right_coset_rel (subsub_int_pred (sub_prod_pred PH PN) PN))
                                                   second_f.
  Proof.
    constructor.
    - exact iso_a.
    - exact iso_b.
    - intros x y. destruct x as [x ?H]. destruct y as [y ?H]. unfold second_f, equiv, right_coset_rel, bi_op, neg, sg_op, sg_negate, pred, subsub_int_pred. simpl; auto.
  Qed.

  Theorem second_isomorphism_theorem : @Group_Isomorphism (Sub PH) (right_coset_rel (subsub_int_pred PH PN)) (sg_op H) (sg_unit H) (sg_negate H)
                                                          (Sub (sub_prod_pred PH PN)) (right_coset_rel (subsub_int_pred (sub_prod_pred PH PN) PN))
                                                          (sg_op HN_SUB) (sg_unit HN_SUB) (sg_negate HN_SUB) second_f.
  Proof.
    constructor; constructor.
    - exact iso_a.
    - exact iso_b.
    - exact second_f_setoid_morph.
    - intros x y. destruct x as [x ?H]. destruct y as [y ?H]. unfold second_f, equiv, right_coset_rel, bi_op, neg, sg_op, sg_negate, pred, subsub_int_pred. simpl; auto.
      rewrite neg_op, <- op_assoc, (op_assoc x y (neg y)), neg_right, one_right, neg_right. apply one_pred. destruct N. auto.
    - constructor. 2: exact second_f_setoid_morph. intros x y. destruct x as [x ?H]. destruct y as [y ?H]. unfold second_f, equiv, right_coset_rel, subsub_int_pred. simpl; auto.
    - constructor. 2: exact second_f_setoid_morph. intros x. destruct x as [x [x1 [x2 ?]]]. exists x1. unfold second_f, equiv, right_coset_rel, pred, subsub_int_pred.
      simpl; auto. apply normal_comm. rewrite e, neg_op, op_assoc, neg_left, one_right. destruct N. apply neg_pred; auto.
  Qed.
  
End SECOND_ISOMORPHISM_THEOREM.
