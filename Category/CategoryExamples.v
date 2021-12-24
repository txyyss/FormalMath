Require Import Coq.Logic.Eqdep.
Require Export FormalMath.lib.Coqlib.
Require Import FormalMath.Category.Category.
Require Import FormalMath.Algebra.Group.

(** * Chapter 1.4 Examples of categories *)

(** 1 *)
Section FUNCTION_CATEGORY.

  Instance funArrows: Arrows Type := fun (A B: Type) => A -> B.
  Instance funExtEq: forall A B: Type, Equiv (A ~> B) :=
    fun (A B : Type) (f g : A ~> B) => forall x : A, f x == g x.
  Instance funCatId: CatId Type := fun (A: Type) (x: A) => x.
  Instance funCatComp: CatComp Type :=
    fun (A B C : Type) (g : B ~> C) (f : A ~> B) (x : A) => g (f x).

  Instance funCategory: Category Type.
  Proof.
    constructor; repeat intro; hnf; unfold comp, funCatComp, cat_id, funCatId; auto.
    - constructor; repeat intro; auto. rewrite H. apply H0.
    - rewrite H0. rewrite H. easy.
  Qed.

End FUNCTION_CATEGORY.

(** 4 *)
Section RELATION_CATEGORY.

  Instance relArrows: Arrows Type := fun (A B: Type) => A -> B -> Prop.
  Instance relIff: forall A B: Type, Equiv (A ~> B) :=
    fun (A B : Type) (f g : A ~> B) => forall a b, f a b <-> g a b.
  Instance relCatId: CatId Type := fun (A: Type) (x y: A) => x == y.
  Instance relCatComp: CatComp Type :=
    fun (A B C : Type) (g : B ~> C) (f : A ~> B) (a : A) (c: C) =>
      exists (b : B), f a b /\ g b c.

  (** * Chapter 1.9 Exercises 1.(a) *)
  Instance relCategory: Category Type.
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
  Instance setsRelFmap: @Fmap Type funArrows Type relArrows id :=
    fun _ _ f A B => f A == B.

  Instance setsRelFunc: @Functor Type funArrows funExtEq funCatId funCatComp
                                 Type relArrows relIff relCatId relCatComp
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
  Instance oppoRelFmap: @Fmap Type oppoArrows Type relArrows id :=
    fun _ _ r => flip r.

  Instance oppoRelFunc: @Functor Type oppoArrows oppoCatEq oppoCatId oppoCatComp
                                 Type relArrows relIff relCatId relCatComp
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

(** 5: category 1 *)
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

(** 5: category 0 *)
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

(** 6: All categories as a category *)
Section CATEGORIES_AS_CATEGORY.

  Record catObj: Type := {
      obj:> Type;
      cat_arrows: Arrows obj;
      cat_equiv: forall a b: obj, Equiv (a ~> b);
      cat_catid: CatId obj;
      cat_catcomp: CatComp obj;
      cat_category: Category obj
    }.

  Arguments Build_catObj _ {_ _ _ _ _}.
  Existing Instance cat_arrows.
  Hint Extern 0 (Equiv (_ ~> _)) => eapply @cat_equiv : typeclass_instances.
  Existing Instance cat_catid.
  Existing Instance cat_catcomp.
  Existing Instance cat_category.

  Record catArrow (a b: catObj): Type := {
      cat_map :> obj a -> obj b;
      cat_Fmap: Fmap cat_map;
      cat_Functor: Functor cat_map _
    }.

  Arguments Build_catArrow {_ _} _ {_ _}.
  Arguments cat_map {_ _} _ _.
  Arguments cat_Fmap {_ _}.
  Existing Instance cat_Fmap.
  Existing Instance cat_Functor.

  Instance catArrows: Arrows catObj := catArrow.

  Instance catEquiv: forall a b: catObj, Equiv (a ~> b) :=
    fun a b F1 F2 => sigT_relation (@fmapEquiv (obj a) (cat_arrows a)
                                               (obj b) (cat_arrows b) (cat_equiv b))
                                   (existT _ (cat_map F1) (cat_Fmap F1))
                                   (existT _ (cat_map F2) (cat_Fmap F2)).

  Instance catCatId: CatId catObj := fun x => @Build_catArrow x x id _ _.

  Instance catCatComp: CatComp catObj :=
    fun x y z f g => @Build_catArrow x z (compose f g) _ _.

  Instance catCategory: Category catObj.
  Proof.
    constructor; intros.
    - constructor; repeat intro; unfold equiv, catEquiv in *.
      + now constructor.
      + apply sigT_relation_symmetric; auto. apply _.
      + eapply sigT_relation_transitive; eauto. apply _.
    - repeat intro. unfold comp, catCatComp. apply path_sigT_relation in H.
      destruct H, x, y. simpl in *. subst. simpl in *. apply path_sigT_relation in H0.
      destruct H0, x0, y0. simpl in *. subst. simpl in *.
      constructor. simpl. unfold fmapEquiv in *. intros.
      unfold compFmap, fmap, compose. rewrite f0. apply f.
    - unfold comp, catCatComp. constructor. simpl. unfold fmapEquiv. now intros.
    - unfold comp, catCatComp. constructor. simpl. unfold fmapEquiv. now intros.
    - unfold comp, catCatComp. constructor. simpl. unfold fmapEquiv. now intros.
  Qed.

End CATEGORIES_AS_CATEGORY.

(** * Chapter 1.5 Isomorphisms *)

(** Definition 1.4 *)
Section GROUP_AS_CATEGORY.

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

  Lemma group_arrow_is_iso: forall `(f: x ~> y), iso_arrows f (neg f).
  Proof. repeat intro. red. split; [apply neg_left | apply neg_right]. Qed.

End GROUP_AS_CATEGORY.
