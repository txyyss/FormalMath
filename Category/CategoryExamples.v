Require Import Coq.Logic.Classical.
Require Import Coq.Classes.RelationClasses.
Require Import FormalMath.Category.Category.
Require Import FormalMath.Algebra.Group.

(** * Chapter 1.4 Examples of categories *)

(** Chapter 1.4.1 *)
Section FUNCTION_CATEGORY.

  Instance funArrows: Arrows Set := fun (A B: Set) => A -> B.
  Instance funExtEq: forall A B: Set, Equiv (A ~> B) :=
    fun (A B : Set) (f g : A ~> B) => forall x : A, f x == g x.
  Instance funCatId: CatId Set := fun (A: Set) (x: A) => x.
  Instance funCatComp: CatComp Set :=
    fun (A B C : Set) (g : B ~> C) (f : A ~> B) (x : A) => g (f x).

  Instance funCategory: Category Set.
  Proof.
    constructor; repeat intro; hnf; unfold comp, funCatComp, cat_id, funCatId; auto.
    - constructor; repeat intro; auto. rewrite H. apply H0.
    - rewrite H0. rewrite H. easy.
  Qed.

  (** Proposition 2.2 *)
  Lemma monic_iff_injective: forall {A B: Set} (f: A ~> B),
      Monomorphism f <-> (forall x y: A, f x == f y -> x == y).
  Proof.
    intros. split; repeat intro.
    - red in H. intros. specialize (H unit (fun _ => x) (fun _ => y)).
      unfold equiv, funExtEq, comp, funCatComp in H. apply H. 2: exact tt. now intros.
    - unfold equiv, funExtEq, comp, funCatComp in H0. specialize (H0 x). now apply H.
  Qed.

  Lemma surjective_is_epic: forall {A B: Set} (f: A ~> B),
      (forall y: B, exists x, f x == y) -> Epimorphism f.
  Proof.
    repeat intro. unfold equiv, funExtEq, comp, funCatComp in H0. specialize (H x).
    destruct H as [x' ?]. specialize (H0 x'). now rewrite H in H0.
  Qed.

  Lemma epic_is_surjective: forall {A B: Set} (f: A ~> B),
      (forall b1 b2: B, {b1 == b2} + {b1 =/= b2}) ->
      Epimorphism f -> (forall y: B, exists x, f x == y).
  Proof.
    intros ? ? ? X ?. repeat red in H. unfold equiv, funExtEq, comp, funCatComp in H.
    intros. apply NNPP. intro.
    assert (forall x, f x =/= y). {
      repeat intro. apply H0. now exists x. } clear H0.
    specialize (H nat (fun _ => O) (fun x => if (X x y) then 1 else O)). simpl in H.
    assert (forall x : A, 0 == (if X (f x) y then 1 else 0)). {
      intros. destruct (X (f x) y); auto. exfalso. now apply (H1 x). }
    specialize (H H0 y). destruct (X y y). 2: now apply n. inversion H.
  Qed.

  (** Example 2.11.1 *)
  Instance emptyInitialArrow: InitialArrow Empty_set := fun _ H => match H with end.

  Instance emptyInitial: Initial Empty_set.
  Proof. repeat intro. destruct x. Qed.

  Instance unitTerminalArrow: TerminalArrow unit := fun _ _ => tt.

  Instance unitTerminal: Terminal unit.
  Proof.
    repeat intro. unfold terminal_arrow, unitTerminalArrow. now destruct (f' x).
  Qed.

End FUNCTION_CATEGORY.

(** Chapter 1.4.2 *)
Section GROUPS_AS_CATEGORY.

  Record GroupObj: Type := {
      gr_obj :> Type;
      go_equiv: Equiv gr_obj;
      go_op: BinOp gr_obj;
      go_unit: GrUnit gr_obj;
      go_neg: Negate gr_obj;
      go_group: Group gr_obj;
    }.

  Existing Instances go_equiv go_op go_unit go_neg go_group.

  Record GrpArrow (g1 g2: GroupObj): Type := {
      ga_map :> gr_obj g1 -> gr_obj g2;
      gr_hom: Group_Homomorphism ga_map;
    }.

  Existing Instance gr_hom.

  Instance GrpArrows: Arrows GroupObj := GrpArrow.
  Arguments ga_map {_ _} _.

  Instance grpCatEq: forall a b: GroupObj, Equiv (a ~> b) :=
    fun a b H1 H2 => forall (x: gr_obj a), ga_map H1 x == ga_map H2 x.

  Lemma id_grp_hom: forall (g: GroupObj), Group_Homomorphism (@id g).
  Proof.
    intros. constructor; try apply _.
    - constructor; try apply _.
    - intros. unfold id. auto.
  Qed.

  Instance grpCatId : CatId GroupObj :=
    fun x : GroupObj => {| ga_map := id; gr_hom := id_grp_hom x |}.

  Instance grpCatComp: CatComp GroupObj :=
    fun x y z G1 G2 =>
      {| ga_map := compose G1 G2; gr_hom := group_hom_compose |}.

  Instance grpCatSetoid: forall (a b: GroupObj), Setoid (a ~> b).
  Proof.
    intros. constructor; unfold equiv, grpCatEq; repeat intro; auto.
    now rewrite H.
  Qed.

  Instance grpCategory: Category GroupObj.
  Proof.
    constructor; intros; try apply _; unfold comp, grpCatComp.
    - repeat intro. simpl. repeat red in H. repeat red in H0. unfold compose.
      now rewrite H0, H.
    - simpl. repeat red. simpl. intros. easy.
    - simpl. repeat red. simpl. intros. unfold compose, id. auto.
    - simpl. repeat red. simpl. intros. unfold compose, id. auto.
  Qed.

End GROUPS_AS_CATEGORY.

(** Chapter 1.4.4 *)
Section RELATION_CATEGORY.

  Instance relArrows: Arrows Set := fun (A B: Set) => A -> B -> Prop.
  Instance relIff: forall A B: Set, Equiv (A ~> B) :=
    fun (A B : Set) (f g : A ~> B) => forall a b, f a b <-> g a b.
  Instance relCatId: CatId Set := fun (A: Set) (x y: A) => x == y.
  Instance relCatComp: CatComp Set :=
    fun (A B C : Set) (g : B ~> C) (f : A ~> B) (a : A) (c: C) =>
      exists (b : B), f a b /\ g b c.

  (** * Chapter 1.9 Exercises 1.(a) *)
  Instance relCategory: Category Set.
  Proof.
    constructor; repeat intro; hnf; unfold comp, relCatComp, cat_id, relCatId.
    - constructor; repeat intro.
      + tauto.
      + unfold equiv, relIff in H. rewrite H. tauto.
      + unfold equiv, relIff in *. rewrite H. apply H0.
    - unfold equiv, relIff in *. split; intros; destruct H1 as [m [? ?]]; exists m.
      + rewrite <- H, <- H0. now split.
      + rewrite H, H0. now split.
    - split; intros.
      + destruct H as [m [[n [? ?]] ?]]. exists n. split; auto. exists m; now split.
      + destruct H as [m [? [n [? ?]]]]. exists n. split; auto. exists m; now split.
    - split; intros.
      + destruct H as [b1 [? ?]]. now rewrite <- H0.
      + exists b0. now split.
    - split; intros.
      + destruct H as [b1 [? ?]]. now rewrite H.
      + exists a0. now split.
  Qed.

  (** * Chapter 1.9 Exercises 1.(b) *)
  Instance setsRelFmap: @Fmap Set funArrows Set relArrows id :=
    fun _ _ f A B => f A == B.

  Instance setsRelFunc: @Functor Set funArrows funExtEq funCatId funCatComp
                                 Set relArrows relIff relCatId relCatComp
                                 id setsRelFmap.
  Proof.
    pose proof funCategory. constructor; try apply _; unfold fmap, setsRelFmap.
    - intros. constructor; try apply _. repeat intro. rewrite H0. tauto.
    - repeat intro. unfold cat_id, relCatId, funCatId. tauto.
    - repeat intro. unfold comp, relCatComp, funCatComp, id. split; intros.
      + exists (f a). now split.
      + destruct H0 as [fa [? ?]]. now rewrite H0.
  Qed.

  (** * Chapter 1.9 Exercises 1.(c) *)
  Instance oppoRelFmap: @Fmap Set oppoArrows Set relArrows id :=
    fun _ _ r => flip r.

  Instance oppoRelFunc: @Functor Set oppoArrows oppoCatEq oppoCatId oppoCatComp
                                 Set relArrows relIff relCatId relCatComp
                                 id oppoRelFmap.
  Proof.
    pose proof oppoCategory. constructor; try apply _; unfold fmap, oppoRelFmap, flip.
    - intros. constructor; try apply _. repeat intro.
      unfold equiv, oppoCatEq, relIff in H0. now rewrite H0.
    - intros. unfold cat_id, oppoCatId, relCatId, id. split; intros; easy.
    - intros. unfold comp, oppoCatComp, relCatComp, flip.
      split; intros; destruct H0 as [S [? ?]]; exists S; easy.
  Qed.

End RELATION_CATEGORY.

(** Chapter 1.4.5: category 1 *)
Section UNIT_CATEGORY.

  Instance unitArrows: Arrows unit := fun _ _ => unit.
  Instance unitEq: forall A B: unit, Equiv (A ~> B) := fun _ _ => (==).
  Instance unitCatId: CatId unit := fun _ => tt.
  Instance unitCatComp: CatComp unit := fun _ _ _ _ _ => tt.
  Instance unitCategory: Category unit.
  Proof.
    constructor; repeat intro; hnf; auto.
    - constructor; repeat intro; auto.
    - destruct f. easy.
    - destruct f. easy.
  Qed.

End UNIT_CATEGORY.

(** Chapter 1.4.5: category 0 *)
Section EMPTY_CATEGORY.

  Definition Empty_map {A: Empty_set -> Type} : forall x : Empty_set, A x :=
    fun x => match x with end.

  Instance emptyArrows: Arrows Empty_set := Empty_map.
  Instance emptyCatId: CatId Empty_set := Empty_map.
  Instance emptyCatComp: CatComp Empty_set := Empty_map.
  Instance emptyEq: forall A B: Empty_set, Equiv (A ~> B) := Empty_map.
  Instance emptySetoid: forall A B: Empty_set, Setoid (A ~> B) := Empty_map.
  Instance emptyCategory: Category Empty_set.
  Proof. constructor; exact Empty_map. Qed.

End EMPTY_CATEGORY.

(** Chapter 1.4.7 *)
Section PREORDER_CATEGORY.

  Context `{P: @PreOrder C pord}.

  Instance preorderArrow: Arrows C := fun a b => pord a b.
  Instance preorderCatEq: forall A B, Equiv (A ~> B) := fun _ _ _ _ => True.

  Instance preorderCatId: CatId C.
  Proof. repeat intro. apply P. Defined.

  Instance preorderCatComp: CatComp C.
  Proof.
    repeat intro. repeat red in X, X0. repeat red.
    eapply P; eauto.
  Defined.

  Instance preorderCategory: Category C.
  Proof.
    constructor; intros.
    - constructor; repeat intro; auto.
    - repeat intro. auto.
    - unfold equiv, preorderCatEq. auto.
    - unfold equiv, preorderCatEq. auto.
    - unfold equiv, preorderCatEq. auto.
  Qed.

  Lemma preorder_monic: forall `(f: A ~> B), Monomorphism f.
  Proof. intros. repeat intro. auto. Qed.

  Lemma preorder_epic: forall `(f: A ~> B), Epimorphism f.
  Proof. intros. repeat intro. auto. Qed.

End PREORDER_CATEGORY.

(** * Chapter 1.5 Isomorphisms *)

(** Definition 1.4 *)
Section ONE_GROUP_AS_CATEGORY.

  Context `{G: Group A}.

  Instance groupArrow: Arrows unit := fun _ _ => A.
  Instance groupCatEq: forall A B, Equiv (A ~> B) := fun _ _ => (=).
  Instance groupCatId: CatId unit := fun _ => one.
  Instance groupCatComp: CatComp unit := fun _ _ _ a b => a & b.
  Instance groupAsCategory: Category unit.
  Proof.
    constructor; intros.
    - apply gr_as_setoid.
    - apply gr_op_proper.
    - unfold comp, groupCatComp. now rewrite op_assoc.
    - apply one_left.
    - apply one_right.
  Qed.

  Lemma group_arrow_is_iso: forall `(f: x ~> y), Isomorphism f (neg f).
  Proof. repeat intro. constructor; [apply neg_left | apply neg_right]. Qed.

End ONE_GROUP_AS_CATEGORY.
