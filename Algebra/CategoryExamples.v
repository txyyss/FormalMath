Require Import FormalMath.Algebra.Category.
Require Import FormalMath.Algebra.Group.

(** * Chapter 1.4 Examples of categories *)

(** 1 *)
Section FUNCTION_CATEGORY.

  Instance funArrows: Arrows Type := fun (A B: Type) => A -> B.
  Instance funCatId: CatId Type := fun (A: Type) (x: A) => x.
  Instance funCatComp: CatComp Type :=
    fun (A B C : Type) (g : B ~> C) (f : A ~> B) (x : A) => g (f x).
  Instance funExtEq: forall A B: Type, Equiv (A ~> B) :=
    fun (A B : Type) (f g : A ~> B) => forall x : A, f x == g x.

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
  Instance relCatId: CatId Type := fun (A: Type) (x: A) => fun y => x == y.
  Instance relCatComp: CatComp Type :=
    fun (A B C : Type) (g : B ~> C) (f : A ~> B) (a : A) (c: C) =>
      exists (b : B), f a b /\ g b c.
  Instance relIff: forall A B: Type, Equiv (A ~> B) :=
    fun (A B : Type) (f g : A ~> B) => forall a b, f a b <-> g a b.

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

End RELATION_CATEGORY.

(** 5: category 1 *)
Section UNIT_CATEGORY.

  Instance unitArrows: Arrows unit := fun _ _ => unit.
  Instance unitCatId: CatId unit := fun _ => tt.
  Instance unitCatComp: CatComp unit := fun _ _ _ _ _ => tt.
  Instance unitEq: forall A B: unit, Equiv (A ~> B) := fun _ _ => (==).
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

(** * Chapter 1.5 Isomorphisms *)

(** Definition 1.4 *)
Section GROUP_AS_CATEGORY.

  Context `{G: Group A}.

  Instance groupArrow: Arrows unit := fun _ _ => A.
  Instance groupCatId: CatId unit := fun _ => one.
  Instance groupCatComp: CatComp unit := fun _ _ _ a b => a & b.
  Instance groupCatEq: forall A B, Equiv (A ~> B) := fun _ _ => (=).
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
