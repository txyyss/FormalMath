Require Export FormalMath.lib.Coqlib.
Require Import FormalMath.Category.Category.
Require Import FormalMath.Category.CategoryExamples.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Eqdep.

(** Chapter 1.4.6: All categories as a category *)
Record CatObj: Type := {
    obj :> Type;
    cat_arrows: Arrows obj;
    cat_equiv: forall a b: obj, Equiv (a ~> b);
    cat_catid: CatId obj;
    cat_catcomp: CatComp obj;
    cat_category: Category obj
  }.

Arguments Build_CatObj _ {_ _ _ _ _}.
#[local] Existing Instance cat_arrows.
#[local] Hint Extern 0 (Equiv (_ ~> _)) => eapply @cat_equiv : typeclass_instances.
#[local] Existing Instance cat_catid.
#[local] Existing Instance cat_catcomp.
#[local] Existing Instance cat_category.

Record CatArrow (a b: CatObj): Type := {
    cat_map :> obj a -> obj b;
    cat_Fmap: Fmap cat_map;
    cat_Functor: Functor cat_map _
  }.

Arguments Build_CatArrow {_ _} _ {_ _}.
Arguments cat_map {_ _} _ _.
Arguments cat_Fmap {_ _}.
#[local] Existing Instance cat_Fmap.
#[local] Existing Instance cat_Functor.

#[local] Instance CatArrows: Arrows CatObj := CatArrow.

#[local] Instance catEquiv: forall a b: CatObj, Equiv (a ~> b) :=
  fun a b F1 F2 => sigT_relation (@fmapEquiv (obj a) (cat_arrows a)
                                             (obj b) (cat_arrows b) (cat_equiv b))
                                 (existT _ (cat_map F1) (cat_Fmap F1))
                                 (existT _ (cat_map F2) (cat_Fmap F2)).

#[local] Instance catCatId: CatId CatObj := fun x => @Build_CatArrow x x id _ _.

#[local] Instance catCatComp: CatComp CatObj :=
  fun x y z f g => @Build_CatArrow x z (compose f g) _ _.

#[local] Instance catCategory: Category CatObj.
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

(** * Chapter 1.9 Exercises 5 Question 2 *)
Definition sliceToArrowObj {M: Type} {AM: Arrows M} (o: M) (so: sliceObj o): arrowObj.
Proof.
  destruct so. exists (x, o). exact a.
Defined.

Section SLICE_TO_ARROW_FUNCTOR.

  Context `{Category C}.
  Context {o: C}.

  Instance sliceToArrowFmap : @Fmap (sliceObj o) (sliceArrows o)
                                    arrowObj arrowArrows (sliceToArrowObj o).
  Proof.
    repeat intro. destruct v as [v fv]. destruct w as [w fw].
    destruct X as [fvw ?H]. cbn. exists (fvw, cat_id). simpl. rewrite H1.
    apply left_identity.
  Defined.

  Instance sliceToArrowFunc:
    @Functor (sliceObj o) (sliceArrows o) (sliceCatEq o) (sliceCatId o)
             (sliceCatComp o) arrowObj arrowArrows arrowCatEq arrowCatId arrowCatComp
             (sliceToArrowObj o) _.
  Proof.
    pose proof (sliceCategory o). pose proof arrowCategory.
    constructor; try apply _; intros; unfold sliceToArrowObj.
    - constructor; try apply _. repeat intro.
      destruct a as [a aa]. destruct b as [b ab]. cbn in x, y.
      destruct x as [fx ?H]. destruct y as [fy ?H]. cbn in H3. cbn. now split.
    - destruct a as [a aa]. cbn. now split.
    - destruct x as [x ax]. destruct y as [y ay]. destruct z as [z az].
      cbn in f, g. destruct f as [fxy ?H]. destruct g as [fyz ?H]. cbn. split; auto.
      symmetry. apply left_identity.
  Qed.

  Definition sliceCatObj: CatObj :=
    @Build_CatObj (sliceObj o) (sliceArrows o) (sliceCatEq o) (sliceCatId o)
                  (sliceCatComp o) (sliceCategory o).

  Definition arrowCatObj: CatObj :=
    @Build_CatObj arrowObj arrowArrows arrowCatEq arrowCatId
                  arrowCatComp arrowCategory.

  Definition sliceToArrowCatArrow: sliceCatObj ~> arrowCatObj :=
    Build_CatArrow _.

  Definition cCatObj: CatObj := Build_CatObj C.

  Definition domCatArrow: arrowCatObj ~> cCatObj :=
    @Build_CatArrow arrowCatObj cCatObj _ domFmap domFunctor.

  Definition sliceForgetCatArrow: sliceCatObj ~> cCatObj :=
    @Build_CatArrow sliceCatObj cCatObj _ (sliceForgetFmap o) (sliceForgetFunctor o).

  Lemma dom_F_U: domCatArrow >>> sliceToArrowCatArrow = sliceForgetCatArrow.
  Proof.
    unfold domCatArrow, sliceToArrowCatArrow, sliceForgetCatArrow.
    unfold comp, catCatComp, sliceCatObj, arrowCatObj, cCatObj, compose. cbn.
    unfold equiv, catEquiv. cbn. apply path_sigT_relation. simpl.
    assert ((fun x : sliceObj o => fst (projT1 (sliceToArrowObj o x))) ==
              projT1 (P:=fun dom : C => dom ~> o)). {
      extensionality x. destruct x as [x ar]. now simpl. } exists H1.
    unfold eq_rect. unfold fmapEquiv. intros.
    destruct v as [v fv]. destruct w as [w fw]. destruct ar as [ar ?H]. simpl.
  Abort.

End SLICE_TO_ARROW_FUNCTOR.

(** Example 2.11.2 *)
Section INITIAL_TERMINAL.

  Definition emptyCatObj : CatObj :=
    @Build_CatObj Empty_set emptyArrows emptyEq emptyCatId emptyCatComp emptyCategory.

  Definition toAny (c: CatObj) (s: obj emptyCatObj) : obj c.
  Proof. destruct s. Defined.

  Definition toAnyFmap (c: CatObj): Fmap (toAny c).
  Proof. repeat intro. destruct v. Defined.

  Instance emptyCatInitArrow : InitialArrow emptyCatObj.
  Proof.
    repeat intro. exists (toAny c) (toAnyFmap c). constructor; try apply _.
    - intros. destruct a.
    - intros. destruct a.
    - intros. destruct x.
  Defined.

  Instance emptyCatInitial: Initial emptyCatObj.
  Proof.
    repeat intro. repeat red. unfold initial_arrow.
    unfold emptyCatInitArrow. simpl. apply path_sigT_relation. simpl.
    assert (cat_map f' == toAny c). { extensionality x. destruct x. } exists H.
    red. intros. destruct v.
  Qed.

  Definition unitCatObj : CatObj :=
    @Build_CatObj unit unitArrows unitEq unitCatId unitCatComp unitCategory.

  Definition fromAny (c: CatObj) (x: obj c): obj unitCatObj := tt.

  Definition fromAnyFmap (c: CatObj): Fmap (fromAny c) := fun _ _ _ => tt.

  Instance unitCatTermArrow: TerminalArrow unitCatObj.
  Proof.
    repeat intro. exists (fromAny c) (fromAnyFmap c). constructor; try apply _.
    - intros. constructor; try apply _. repeat intro. reflexivity.
    - intros. reflexivity.
    - intros. reflexivity.
  Defined.

  Instance unitTerminal: Terminal unitCatObj.
  Proof.
    repeat intro. repeat red. unfold terminal_arrow. unfold unitCatTermArrow. simpl.
    apply path_sigT_relation. simpl.
    assert (cat_map f' == fromAny c). {
      extensionality x. destruct (f' x). destruct (fromAny c x). easy. }
    exists H. unfold fmapEquiv. intros. unfold fromAnyFmap.
    destruct (@eq_rect (c -> unit) f' (@Fmap _ _ _ unitArrows)
                       (cat_Fmap f') (fromAny c) H v w ar). easy.
  Qed.

End INITIAL_TERMINAL.
