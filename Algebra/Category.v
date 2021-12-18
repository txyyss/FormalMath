Require Export FormalMath.Infra.

(** The definition of a category and related concepts and theorems
    follow Steve Awodey's "Category Theory". *)

(** * Chapter 1.3 Definition of a category *)

Class Arrows (O: Type): Type := Arrow: O -> O -> Type.
Typeclasses Transparent Arrows.
Infix "~>" := Arrow (at level 90, right associativity): math_scope.

Class CatId O `{Arrows O} := cat_id: forall x, x ~> x.
Class CatComp O `{Arrows O} := comp: forall x y z, (y ~> z) -> (x ~> y) -> (x ~> z).

Arguments cat_id {O arrows CatId x} : rename.
Arguments comp {O arrow CatComp} _ _ _ _ _ : rename.

Infix ">>>" := (comp _ _ _) (at level 40, left associativity) : math_scope.

#[universes (polymorphic, cumulative)]
 Class Category O `{!Arrows O} `{forall a b: O, Equiv (a ~> b)}
 `{!CatId O} `{!CatComp O}: Prop := {
    arrow_equiv :> forall a b, Setoid (a ~> b);
    comp_proper :> forall a b c, Proper ((=) ==> (=) ==> (=)) (comp a b c);
    comp_assoc : forall `(f: a ~> b) `(g: b ~> c) `(h: c ~> d),
      h >>> (g >>> f) = (h >>> g) >>> f;
    left_identity: forall `(f: a ~> b), cat_id >>> f = f;
    right_identity: forall `(f: a ~> b), f >>> cat_id = f;
  }.

Arguments comp_assoc {O arrows eq CatId CatComp Category a b} _ {c} _ {d} _ : rename.

(** * Chapter 1.4 Examples of categories *)

(** 6: Functor *)
Section FUNCTOR.

  Context `{Category C} `{Category D}.
  Context (M: C -> D).

  Class Fmap: Type := fmap: forall {v w: C}, (v ~> w) -> (M v ~> M w).

  Class Functor `(Fmap): Prop := {
      functor_from: Category C;
      functor_to: Category D;
      functor_morphism :> forall a b, Setoid_Morphism (@fmap _ a b);
      preserves_id: forall {a}, fmap (cat_id: a ~> a) = cat_id;
      preserves_comp: forall `(g: y ~> z) `(f: x ~> y),
        fmap (g >>> f) = fmap g >>> fmap f
    }.

End FUNCTOR.

Typeclasses Transparent Fmap.

Section IDENTITY_FUNCTOR.

  Context `{Category C}.

  Instance idFmap: Fmap id := fun _ _ => id.

  Instance idFunctor: Functor (id: C -> C) _.
  Proof.
    constructor; try apply _; try easy.
    intros. constructor; try apply _; try easy.
  Qed.

End IDENTITY_FUNCTOR.

(** * Chapter 1.5 Isomorphisms *)

Section ISOMORPHISM.

  Context `{Category C}.

  (** Definition 1.3 *)
  Definition iso_arrows `(f: A ~> B) (g: B ~> A): Prop :=
    g >>> f = cat_id /\ f >>> g = cat_id.

  Lemma iso_arrows_unique: forall `(f: A ~> B) (g1 g2: B ~> A),
      iso_arrows f g1 -> iso_arrows f g2 -> g1 = g2.
  Proof.
    intros. destruct H1, H2. rewrite <- left_identity.
    rewrite <- H2, <- comp_assoc. rewrite H3. apply right_identity.
  Qed.

  Lemma iso_arrows_sym: forall `(f: A ~> B) (g: B ~> A),
      iso_arrows f g -> iso_arrows g f.
  Proof. intros. destruct H1. split; auto. Qed.

End ISOMORPHISM.

(** * Chapter 1.6 Constructions on categories *)

(** 1: product *)
Section PRODUCT_CATEGORY.

  Context `{Category C} `{Category D}.
  Instance prodArrows: Arrows (C * D) :=
    fun p1 p2 => ((fst p1 ~> fst p2) * (snd p1 ~> snd p2))%type.
  Instance prodCatId: CatId (C * D) := fun _ => (cat_id, cat_id).
  Instance prodCatComp: CatComp (C * D) :=
    fun _ _ _ a1 a2 => (fst a1 >>> fst a2, snd a1 >>> snd a2).
  Instance prodCatEq: forall A B: (C * D), Equiv (A ~> B) :=
    fun _ _ p1 p2 => fst p1 = fst p2 /\ snd p1 = snd p2.
  Instance prodCatSetoid: forall A B: (C * D), Setoid (A ~> B).
  Proof.
    intros. constructor; red; unfold equiv, prodCatEq;
      intros; split; try easy; destruct H3, H4; firstorder.
  Qed.

  Instance prodCategory: Category (C * D).
  Proof.
    constructor; intros; try apply _.
    - repeat intro. destruct x, x0, y, y0, H3, H4. unfold comp, prodCatComp.
      simpl in *. split; simpl.
      + now rewrite H3, H4.
      + now rewrite H5, H6.
    - destruct h, g, f. split; simpl; apply comp_assoc.
    - unfold comp, prodCatComp. destruct f. split; simpl; apply left_identity.
    - unfold comp, prodCatComp. destruct f. split; simpl; apply right_identity.
  Qed.

End PRODUCT_CATEGORY.
