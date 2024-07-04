Require Export FormalMath.Infra.

(****************************** Group ******************************)

Class BinOp A := bi_op : A -> A -> A.
Infix "&" := bi_op (at level 50, left associativity) : math_scope.
Notation "(&)" := bi_op (only parsing) : math_scope.
Notation "( x &)" := (bi_op x) (only parsing) : math_scope.
Notation "(& x )" := (fun y => y & x) (only parsing) : math_scope.

Class GrUnit A := one : A.

Class Negate A := neg : A -> A.

Class Group (A : Type) {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A}
      {Anegate : Negate A} : Prop :=
  {
    gr_as_setoid :: Setoid A;
    gr_op_proper :: Proper ((=) ==> (=) ==> (=)) (&);
    negate_proper :: Proper ((=) ==> (=)) neg;
    op_assoc : forall x y z, (x & y) & z = x & (y & z);
    one_left : forall x, one & x = x;
    neg_left : forall x, neg x & x = one
  }.

Coercion gr_as_setoid : Group >-> Setoid.

Class AbelianGroup (A : Type) {Ae : Equiv A} {Aop : BinOp A} {Aunit : GrUnit A}
      {Anegate : Negate A} : Prop :=
  {
    abgroup_as_group :: Group A;
    bi_op_comm : forall x y, x & y = y & x
  }.

#[export] Hint Rewrite @one_left: group.
#[export] Hint Rewrite @neg_left: group.

(* Coercion abgroup_as_group : AbelianGroup >-> Group. *)

Section GROUP_PROP.

  Context `{G : Group A}.

  Lemma one_unique : forall x,  x & x = x -> x = one.
  Proof. intros; rewrite <- (one_left x), <- (neg_left x), op_assoc, H; auto. Qed.

  Lemma neg_right : forall x, x & neg x = one.
  Proof.
    intros; apply one_unique.
    rewrite <- op_assoc, (op_assoc x (neg x) x), neg_left, op_assoc, one_left; auto.
  Qed.

  Lemma one_right : forall x, x & one = x.
  Proof. intros; rewrite <- (neg_left x), <- op_assoc, neg_right, one_left; auto. Qed.

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

  Lemma neg_unique : forall x y, x & y = one -> y = neg x.
  Proof. intros; apply (eq_left x); rewrite H, neg_right; auto. Qed.

  Lemma double_neg : forall x, neg (neg x) = x.
  Proof.
    intro. generalize (neg_left x); intro. apply neg_unique in H.
    rewrite <- H; auto.
  Qed.

  Lemma neg_op : forall x y, neg (x & y) = neg y & neg x.
  Proof.
    intros. symmetry. apply neg_unique.
    rewrite <- op_assoc, (op_assoc x y (neg y)), neg_right, one_right, neg_right; auto.
  Qed.

  Lemma neg_one : neg one = one.
  Proof. apply one_unique. rewrite <- neg_op, one_right. auto. Qed.

  Lemma neg_iff : forall x y, x = y <-> neg x = neg y.
  Proof.
    intros; split; intros;
      [rewrite H |
       rewrite (eq_left (neg x)), neg_left; rewrite (eq_right y) in H;
       rewrite H, neg_left]; auto.
  Qed.

  Lemma fold_left_op_one: forall l i, fold_left (&) l i = i & fold_left (&) l one.
  Proof.
    intros l. remember (length l).
    assert (length l <= n) by (symmetry in Heqn; apply PeanoNat.Nat.eq_le_incl; auto).
    clear Heqn. revert l H.
    induction n; intros; destruct l; simpl in *; try (rewrite one_right; reflexivity).
    1: inversion H.
    assert (length l <= n) by (now apply le_S_n). rewrite (IHn l H0 (i & a)).
    rewrite (IHn l H0 (one & a)). rewrite <- op_assoc, one_left. reflexivity.
  Qed.

  Lemma fold_left_neg: forall x l, x = fold_left (&) l one ->
                                   neg x = fold_left (&) (map neg (rev l)) one.
  Proof.
    intros x l. remember (length l).
    assert (length l <= n) by (symmetry in Heqn; apply PeanoNat.Nat.eq_le_incl; auto).
    clear Heqn. revert x l H.
    induction n; intros; destruct l; simpl in *; try (rewrite H0; apply neg_one).
    1: inversion H. rewrite map_app, fold_left_app. simpl.
    assert (length l <= n) by (now apply le_S_n).
    rewrite fold_left_op_one, one_left in H0.
    assert (fold_left bi_op l one = fold_left bi_op l one) by auto.
    specialize (IHn _ _ H1 H2). rewrite H0, neg_op, IHn. reflexivity.
  Qed.

  Lemma fold_left_conjugate: forall l x,
      fold_left (&) (map (fun i => x & i & neg x) l) one =
      x & (fold_left (&) l one) & neg x.
  Proof.
    intro l. remember (length l).
    assert (length l <= n) by (symmetry in Heqn; apply PeanoNat.Nat.eq_le_incl; auto).
    clear Heqn. revert l H.
    induction n; intros; destruct l; simpl in *;
      try (rewrite one_right, neg_right; reflexivity). 1: inversion H.
    assert (length l <= n) by (now apply le_S_n).
    specialize (IHn _ H0). clear H0.
    rewrite fold_left_op_one, (fold_left_op_one _ (one & a)),
    !one_left, !op_assoc, <- !eq_left, IHn, <- !op_assoc, neg_left, one_left; auto.
  Qed.

End GROUP_PROP.

#[export] Hint Rewrite @neg_right: group.
#[export] Hint Rewrite @one_right: group.
#[export] Hint Rewrite @neg_one: group.
#[export] Hint Rewrite @double_neg: group.

(****************************** Group Homomorphism ******************************)

Section GROUP_HOMOMORPHISM.

  Context `{Group A} `{Group B}.

  Class Group_Homomorphism (f : A -> B) :=
  {
    grmor_a : Group A;
    grmor_b : Group B;
    grmor_setmore :: Setoid_Morphism f;
    preserve_gr_op : forall x y, f (x & y) = f x & f y
  }.

End GROUP_HOMOMORPHISM.

Section GROUP_HOMOMORPHISMS_PROP.

  Context {A : Type} {Ae : Equiv A} {Aop : BinOp A}
          {Aunit : GrUnit A} {Anegate : Negate A}.
  Context {B : Type} {Be : Equiv B} {Bop : BinOp B}
          {Bunit : GrUnit B} {Bnegate : Negate B}.
  Context {f : A -> B} `{GH : !Group_Homomorphism f}.

  Lemma preserve_gr_unit : f one = one.
  Proof.
    intros. destruct GH. pose proof (preserve_gr_op (one : A) one).
    rewrite (one_left one) in H. symmetry in H. apply one_unique in H. auto.
  Qed.

  Lemma preserve_negate : forall x, f (neg x) = neg (f x).
  Proof.
    intros. destruct GH. rewrite (eq_left (f x)), <- preserve_gr_op.
    autorewrite with group; [| eauto..].
    apply preserve_gr_unit.
  Qed.

  Context {C : Type} {Ce : Equiv C} {Cop : BinOp C}
          {Cunit : GrUnit C} {Cnegate : Negate C}.
  Context {g : B -> C} `{GH' : !Group_Homomorphism g}.

  Lemma group_hom_compose: Group_Homomorphism (compose g f).
  Proof.
    assert (Group A) by now destruct GH.
    assert (Group B) by now destruct GH.
    assert (Group C) by now destruct GH'.
    constructor; try apply _.
    - apply setoid_morphism_trans; [apply GH | apply GH'].
    - intros. unfold compose. rewrite !preserve_gr_op. auto.
  Qed.

End GROUP_HOMOMORPHISMS_PROP.

(****************************** SubGroup ******************************)

Class SubGroupCondition (A: Type) (P: A -> Prop) `{Group A} : Prop :=
  {
    pred_proper :: Proper ((=) ==> iff) P;
    non_empty: exists x, P x;
    sub_criteria: forall x y: A, P x -> P y -> P (x & (neg y));
  }.

Definition Subpart (A: Type) (P: A -> Prop) := {x: A | P x}.

#[export] Instance subgroup_rep {A P}: Cast (Subpart A P) A := fun x => proj1_sig x.

Section SUBGROUP.

  Context `{SA : SubGroupCondition A P}.

  Lemma one_pred: P one.
  Proof.
    destruct (non_empty) as [x ?H]. generalize (sub_criteria _ _ H0 H0).
    rewrite (neg_right x). auto.
  Qed.

  Lemma neg_pred: forall x: A, P x -> P (neg x).
  Proof.
    intros. pose proof one_pred. pose proof (sub_criteria _ _ H1 H0).
    rewrite one_left in H2. auto.
  Qed.

  Lemma op_pred: forall x y: A, P x -> P y -> P (x & y).
  Proof.
    intros. pose proof (neg_pred _ H1). pose proof (sub_criteria _ _ H0 H2).
    rewrite double_neg in H3. auto.
  Qed.

  #[global] Instance subgroup_equiv: Equiv (Subpart A P) := fun x y => ('x) = ('y).

  #[global] Instance subgroup_binop: BinOp (Subpart A P).
  Proof.
    intros x y. destruct x as [x ?H]. destruct y as [y ?H]. exists (x & y).
    apply op_pred; auto.
  Defined.

  #[global] Instance subgroup_gunit: GrUnit (Subpart A P) := exist _ _ one_pred.

  #[global] Instance subgroup_neg: Negate (Subpart A P).
  Proof. intro x. destruct x as [x ?H]. exists (neg x). apply neg_pred; auto. Defined.

  Lemma sg_neg_proj : forall (x : Subpart A P), neg ('x) =  '(neg x).
  Proof. intros. destruct x. unfold cast, subgroup_rep, proj1_sig. simpl. auto. Qed.

  Lemma sg_op_proj : forall (x y : Subpart A P), ('x) & ('y) = '(x & y).
  Proof. intros; destruct x, y. unfold cast, subgroup_rep, proj1_sig. simpl. auto. Qed.

  Instance: Setoid (Subpart A P).
  Proof.
    constructor; unfold equiv, subgroup_equiv, cast, subgroup_rep, proj1_sig;
      [intros [x]; auto | intros [x] [y] ?; now symmetry |
       intros [x] [y] [z] ? ?; now transitivity y].
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) subgroup_binop.
  Proof.
    intros [x] [y] ? [x0] [y0] ?. hnf in H0, H1 |- *.
    unfold cast, subgroup_rep, proj1_sig in H0, H1 |-* . simpl.
    apply gr_op_proper; auto.
  Qed.

  Instance: Proper ((=) ==> (=)) subgroup_neg.
  Proof.
    intros [x] [y] ?. hnf in H0 |-* . unfold cast, subgroup_rep, proj1_sig in H0 |-* .
    simpl. apply negate_proper; auto.
  Qed.

  #[global] Instance subGroup: Group (Subpart A P).
  Proof.
    repeat (constructor; try apply _); repeat intros [?];
      unfold bi_op, neg, subgroup_binop, subgroup_neg, one, equiv,
      subgroup_equiv, subgroup_gunit, cast, subgroup_rep, proj1_sig;
      [apply op_assoc | apply one_left | apply neg_left].
  Qed.

End SUBGROUP.

(****************************** Coset ******************************)

Inductive RightCoset A (P: A -> Prop) := right_coset_inject: A -> RightCoset A P.
Arguments right_coset_inject {A P} _.

#[export] Instance right_coset_rep {A P}: Cast (RightCoset A P) A :=
  fun x => match x with right_coset_inject x => x end.

Inductive LeftCoset A (P: A -> Prop) := left_coset_inject: A -> LeftCoset A P.
Arguments left_coset_inject {A P} _.

#[export] Instance left_coset_rep {A P}: Cast (LeftCoset A P) A :=
  fun x => match x with left_coset_inject x => x end.

Section COSET.

  Context `{SA: SubGroupCondition A P}.

  #[global] Instance right_coset_equiv: Equiv (RightCoset A P) :=
    fun x y => P ('x & (neg ('y))).

  #[global] Instance rightCosetoid: Setoid (RightCoset A P).
  Proof.
    constructor; unfold equiv, right_coset_equiv, cast, right_coset_rep.
    - intros [x]. rewrite neg_right. apply one_pred.
    - intros [x] [y] ?. apply neg_pred in H0. rewrite neg_op, double_neg in H0. auto.
    - intros [x] [y] [z] ? ?. pose proof (op_pred _ _ H0 H1).
      rewrite <- op_assoc, (op_assoc x (neg y) y), neg_left, one_right in H2. auto.
  Qed.

  #[global] Instance left_coset_equiv: Equiv (LeftCoset A P) :=
    fun x y => P ((neg ('x)) & 'y).

  #[global] Instance leftCosetoid: Setoid (LeftCoset A P).
  Proof.
    constructor; unfold equiv, left_coset_equiv, cast, left_coset_rep.
    - intros [x]. rewrite neg_left. apply one_pred.
    - intros [x] [y] ?. apply neg_pred in H0. rewrite neg_op, double_neg in H0. auto.
    - intros [x] [y] [z] ? ?. pose proof (op_pred _ _ H0 H1).
      rewrite <- op_assoc, (op_assoc (neg x) y (neg y)), neg_right, one_right in H2.
      assumption.
  Qed.

  Definition left2right_coset (x: LeftCoset A P): RightCoset A P :=
    right_coset_inject (neg (' x)).

  Instance inv_left2right: Inverse left2right_coset :=
    fun x => left_coset_inject (neg (' x)).

  Instance left2right_Setoid_Morphism: Setoid_Morphism left2right_coset.
  Proof.
    constructor; [apply _ ..|]. intros [x] [y] ?.
    unfold left2right_coset, cast, equiv, right_coset_equiv, cast. simpl.
    unfold equiv, left_coset_equiv, cast in H0. simpl in H0. rewrite double_neg.
    assumption.
  Qed.

  Instance left2right_bijection: Bijective left2right_coset.
  Proof.
    constructor; constructor; try apply _.
    - intros [x] [y]. unfold left2right_coset, cast, equiv, left_coset_equiv,
                      right_coset_equiv, cast. simpl. intros.
      rewrite double_neg in H0. assumption.
    - intros [x]. unfold left2right_coset, inverse, cast, equiv, right_coset_equiv,
                  inv_left2right, cast. simpl. rewrite double_neg, neg_right.
      apply one_pred.
  Qed.

  Lemma coset_cardinals_the_same:
    forall n, Cardinals (LeftCoset A P) n <-> Cardinals (RightCoset A P) n.
  Proof. intros. apply (bijective_the_same_cardinals _ _ left2right_coset). Qed.

End COSET.

(****************************** QuotientGroup ******************************)

Class NormalSubGroupCondition (A: Type) (P: A -> Prop) `{Group A} : Prop :=
  {
    still_subgroup :: SubGroupCondition A P;
    normal_comm: forall (x y: A), P (x & y) -> P (y & x)
  }.

Inductive Quotient A (P: A -> Prop) := quotient_inject: A -> Quotient A P.
Arguments quotient_inject {A P} _.

#[export] Instance quotient_rep {A P}: Cast (Quotient A P) A :=
  fun x => match x with quotient_inject x => x end.

Section QUOTIENT_GROUP.

  Context `{NSA: NormalSubGroupCondition A P}.

  #[global] Instance quotient_equiv: Equiv (Quotient A P) :=
    fun x y => P (' x & (neg ('y))).

  #[global] Instance quotient_binop: BinOp (Quotient A P) :=
    fun x y => quotient_inject (' x & ' y).

  #[global] Instance quotient_gunit: GrUnit (Quotient A P) := quotient_inject one.

  #[global] Instance quotient_neg: Negate (Quotient A P) :=
    fun x => quotient_inject (neg (' x)).

  Instance: Setoid (Quotient A P).
  Proof.
    constructor; unfold equiv, quotient_equiv, cast, quotient_rep.
    - intros [x]. rewrite neg_right. apply one_pred.
    - intros [x] [y] ?. apply neg_pred in H0. rewrite neg_op, double_neg in H0. auto.
    - intros [x] [y] [z] ? ?. pose proof (op_pred _ _ H0 H1).
      rewrite <- op_assoc, (op_assoc x (neg y) y), neg_left, one_right in H2. auto.
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) quotient_binop.
  Proof.
    intros [x] [y] ? [x0] [y0] ?. hnf in H0, H1 |- *.
    unfold quotient_binop, cast, quotient_rep in H0, H1 |-* .
    rewrite neg_op, <- op_assoc. apply normal_comm.
    rewrite <- !op_assoc, (op_assoc (neg y & x)). apply normal_comm, op_pred; auto.
    apply normal_comm. auto.
  Qed.

  Instance: Proper ((=) ==> (=)) quotient_neg.
  Proof.
    intros [x] [y] ?. hnf in H0 |-* .
    unfold quotient_binop, quotient_neg, cast, quotient_rep in H0 |-* .
    rewrite double_neg, <- (double_neg (neg x & y)). apply neg_pred; auto.
    rewrite neg_op, double_neg. apply normal_comm. auto.
  Qed.

  #[global] Instance quotientGroup: Group (Quotient A P).
  Proof.
    constructor; try apply _;
      unfold bi_op, neg, one, equiv, quotient_equiv, quotient_binop,
      quotient_neg, quotient_gunit, quotient_rep, cast.
    - intros [x] [y] [z]. rewrite <- op_assoc, neg_right. apply one_pred; auto.
    - intros [x]. rewrite op_assoc, neg_right, one_right. apply one_pred; auto.
    - intros [x]. rewrite neg_left, neg_right. apply one_pred; auto.
  Qed.

End QUOTIENT_GROUP.

Section SUBGROUP_GEN.

  Context `{Group A}.

  Variable P : A -> Prop.

  Definition subgroup_gen : A -> Prop :=
    fun x => exists l,
        x = fold_left (&) l one /\
        forall i, In i l -> exists s: A, P s /\ (i = s \/ i = neg s).

  Instance: Proper ((=) ==> iff) subgroup_gen.
  Proof.
    constructor; unfold subgroup_gen; intros [l [? ?]];
      exists l; split; auto. now rewrite <- H0.
  Qed.

  Lemma subgroup_gen_neg: forall x, subgroup_gen x -> subgroup_gen (neg x).
  Proof.
    intros x [l [? ?]]. exists (map neg (rev l)). split.
    1: apply fold_left_neg in H0; assumption.
    intros. rewrite in_map_iff in H2. destruct H2 as [pi [? ?]].
    rewrite <- in_rev in H3. specialize (H1 _ H3). destruct H1 as [sp [? ?]].
    exists sp. split; auto; destruct H4; [right | left];
                 rewrite <- H2, H4; [|rewrite double_neg]; reflexivity.
  Qed.

  Lemma subgroup_gen_op: forall x y,
      subgroup_gen x -> subgroup_gen y -> subgroup_gen (x & y).
  Proof.
    intros x y [xl [? ?]] [yl [? ?]]. exists (xl ++ yl). split.
    - rewrite fold_left_app, fold_left_op_one, H0, H2. reflexivity.
    - intros. rewrite in_app_iff in H4. destruct H4; [apply H1 | apply H3]; auto.
  Qed.

  #[global] Instance: SubGroupCondition A subgroup_gen.
  Proof.
    constructor; [apply _ | exists one, nil; simpl; intuition |
                  intros; apply subgroup_gen_op; auto; apply subgroup_gen_neg; auto].
  Qed.

End SUBGROUP_GEN.

Lemma subgroup_gen_false: forall `{Group A} x,
    subgroup_gen (fun _ => False) x -> x = one.
Proof.
  intros. red in H0. destruct H0 as [l [? ?]]. destruct l.
  - simpl in H0. assumption.
  - assert (In a (a :: l)) by (simpl; left; reflexivity). specialize (H1 _ H2).
    destruct H1 as [s [? ?]]. exfalso; assumption.
Qed.

Section NORMAL_GENERATION.

  Context `{Group A}.

  Variable P: A -> Prop.

  Definition normal_gen : A -> Prop :=
    fun x => exists l,
        x = fold_left (&) l one /\
        forall i, In i l -> exists (g s: A),
            P s /\ (i = g & s & (neg g) \/ i = g & (neg s) & (neg g)).

  Lemma normal_gen_neg: forall x, normal_gen x -> normal_gen (neg x).
  Proof.
    intros x [l [? ?]]. exists (map neg (rev l)). split.
    1: apply fold_left_neg in H0; assumption.
    intros. rewrite in_map_iff in H2. destruct H2 as [pi [? ?]].
    rewrite <- in_rev in H3. specialize (H1 _ H3). destruct H1 as [gp [sp [? ?]]].
    exists gp, sp.
    split; auto; destruct H4; [right | left];
      rewrite <- H2, H4, !neg_op, !double_neg, op_assoc; reflexivity.
  Qed.

  Lemma normal_gen_op: forall x y, normal_gen x -> normal_gen y -> normal_gen (x & y).
  Proof.
    intros x y [xl [? ?]] [yl [? ?]]. exists (xl ++ yl). split.
    - rewrite fold_left_app, fold_left_op_one, H0, H2. reflexivity.
    - intros. rewrite in_app_iff in H4. destruct H4; [apply H1 | apply H3]; auto.
  Qed.

  Lemma normal_gen_op_comm: forall x y, normal_gen (x & y) -> normal_gen (y & x).
  Proof.
    intros x y [l [? ?]]. exists (map (fun i => y & i & neg y) l). split.
    - rewrite fold_left_conjugate, <- H0, !op_assoc,
      neg_right, one_right; reflexivity.
    - intros. rewrite in_map_iff in H2. destruct H2 as [pi [? ?]].
      specialize (H1 _ H3). destruct H1 as [gp [sp [? ?]]].
      exists (y & gp), sp. split; auto. rewrite <- H2, neg_op.
      destruct H4; [left | right]; rewrite H4; rewrite <- !op_assoc; reflexivity.
  Qed.

  Instance: Proper ((=) ==> iff) normal_gen.
  Proof.
    constructor; unfold normal_gen; intros [l [? ?]];
      exists l; split; auto. now rewrite <- H0.
  Qed.

  Instance: SubGroupCondition A normal_gen.
  Proof.
    constructor; [apply _ | exists one, nil; simpl; intuition |
                  intros; apply normal_gen_op; auto; apply normal_gen_neg; auto].
  Qed.

  #[global] Instance normal_gen_normalcond: NormalSubGroupCondition A normal_gen.
  Proof. constructor; [apply _ | apply normal_gen_op_comm]. Qed.

End NORMAL_GENERATION.
