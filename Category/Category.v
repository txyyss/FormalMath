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

  #[global] Instance fmapEquiv: Equiv Fmap :=
    fun F1 F2 => forall (v w: C) (ar: v ~> w), F1 v w ar = F2 v w ar.

  #[global] Instance fmapSetoid: Setoid Fmap.
  Proof.
    constructor; repeat intro; try easy.
    specialize (H3 v w ar). specialize (H4 v w ar). now transitivity (y v w ar).
  Qed.

End FUNCTOR.

Typeclasses Transparent Fmap.

Section IDENTITY_FUNCTOR.

  Context `{Category C}.

  #[global] Instance idFmap: Fmap id := fun _ _ => id.

  #[global] Instance idFunctor: Functor (id: C -> C) _.
  Proof.
    constructor; try apply _; try easy.
    intros. constructor; try apply _; try easy.
  Qed.

End IDENTITY_FUNCTOR.

Section COMPOSE_FUNCTOR.

  Context
    A B C
    `{!Arrows A} `{!Arrows B} `{!Arrows C}
    `{!CatId A} `{!CatId B} `{!CatId C}
    `{!CatComp A} `{!CatComp B} `{!CatComp C}
    `{forall a b: A, Equiv (a ~> b)}
    `{forall a b: B, Equiv (a ~> b)}
    `{forall a b: C, Equiv (a ~> b)}
    `{!Functor (f: B -> C) f'} `{!Functor (g: A -> B) g'}.

  #[global] Instance compFmap: Fmap (compose f g) :=
    fun _ _ => compose (fmap f) (fmap g).

  #[global] Instance compFunctor: Functor (compose f g) _.
  Proof.
    pose proof (functor_from g). pose proof (functor_to g). pose proof (functor_to f).
    constructor; intros; try apply _; unfold fmap, compFmap.
    - apply setoid_morphism_trans.
      + apply (functor_morphism g).
      + apply (functor_morphism f).
    - unfold compose. repeat rewrite preserves_id; auto.
    - unfold compose. repeat rewrite preserves_comp; auto.
  Qed.

End COMPOSE_FUNCTOR.

(** * Chapter 1.5 Isomorphisms *)

Section ISOMORPHISM.

  Context `{Category C}.

  (** Definition 1.3 *)
  Class Isomorphism `(f: A ~> B) (g: B ~> A): Prop := {
      iso_comp1: g >>> f = cat_id;
      iso_comp2: f >>> g = cat_id;
    }.

  Lemma iso_inverse_unique: forall `(f: A ~> B) (g1 g2: B ~> A),
      Isomorphism f g1 -> Isomorphism f g2 -> g1 = g2.
  Proof.
    intros. destruct H1, H2. rewrite <- left_identity.
    rewrite <- iso_comp5, <- comp_assoc. rewrite iso_comp4. apply right_identity.
  Qed.

  Lemma isomorphism_sym: forall `(f: A ~> B) (g: B ~> A),
      Isomorphism f g -> Isomorphism g f.
  Proof. intros. destruct H1. split; auto. Qed.

End ISOMORPHISM.

(** * Chapter 1.6 Constructions on categories *)

(** 1: product category *)
Section PRODUCT_CATEGORY.

  Context `{Category C} `{Category D}.
  Instance prodArrows: Arrows (C * D) :=
    fun p1 p2 => ((fst p1 ~> fst p2) * (snd p1 ~> snd p2))%type.
  Instance prodCatEq: forall A B: (C * D), Equiv (A ~> B) :=
    fun _ _ p1 p2 => fst p1 = fst p2 /\ snd p1 = snd p2.
  Instance prodCatId: CatId (C * D) := fun _ => (cat_id, cat_id).
  Instance prodCatComp: CatComp (C * D) :=
    fun _ _ _ a1 a2 => (fst a1 >>> fst a2, snd a1 >>> snd a2).
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

  Instance fstFmap: Fmap fst := fun _ _ => fst.

  Instance fstFunctor: Functor fst _.
  Proof.
    constructor; try apply _; intros.
    - constructor; try apply _. repeat intro. destruct H3. apply H3.
    - destruct a. reflexivity.
    - destruct x, y, z, f, g. easy.
  Qed.

  Instance sndFmap: Fmap snd := fun _ _ => snd.

  Instance sndFunctor: Functor snd _.
  Proof.
    constructor; try apply _; intros.
    - constructor; try apply _. repeat intro. destruct H3. apply H4.
    - destruct a. reflexivity.
    - destruct x, y, z, f, g. easy.
  Qed.

End PRODUCT_CATEGORY.

(** 2: opposite category *)
Section OPPOSITE_CATEGORY.

  Context `{@Category C ArrowsC CatEquivC CatIdC CatCompC}.

  Instance oppoArrows: Arrows C := flip ArrowsC.
  Instance oppoCatEq: forall A B: C, Equiv (oppoArrows A B) :=
    fun A B => CatEquivC B A.
  Instance oppoCatId: @CatId C oppoArrows := CatIdC.
  Instance oppoCatComp: @CatComp C oppoArrows := fun a b c => flip (CatCompC c b a).
  Instance oppoCatSetoid: forall A B: C, Setoid (oppoArrows A B).
  Proof. intros. change (Setoid (ArrowsC B A)). apply arrow_equiv. Qed.

  Lemma oppoCategory: @Category C oppoArrows oppoCatEq oppoCatId oppoCatComp.
  Proof.
    constructor; try apply _; intros; unfold comp, oppoCatComp, Arrow,
      oppoArrows, cat_id, oppoCatId, equiv, oppoCatEq,  flip.
    - repeat intro. change (CatCompC c b a x0 x = CatCompC c b a y0 y).
      now apply comp_proper.
    - symmetry. apply comp_assoc.
    - apply right_identity.
    - apply left_identity.
  Qed.

End OPPOSITE_CATEGORY.

(** 3: arrow category *)
Section ARROW_CATEGORY.

  Context `{Category C}.

  Definition arrowObj := {domcod: C * C & fst domcod ~> snd domcod}.

  Instance arrowArrows: Arrows arrowObj.
  Proof.
    intros [[A B] f] [[A' B'] f']. simpl in *.
    exact {g: (A ~> A') * (B ~> B') | (snd g) >>> f = f' >>> (fst g)}.
  Defined.

  Instance arrowCatEq: forall (A B: arrowObj), Equiv (A ~> B).
  Proof.
    intros [[A B] f] [[A' B'] g]. unfold Arrow, arrowArrows.
    intros [[g1 g2] ?H] [[g3 g4] ?H].
    exact ((g1 = g3) /\ (g2 = g4)).
  Defined.

  Instance arrowCatId: CatId arrowObj.
  Proof.
    intros [[A B] f]. simpl in f. unfold Arrow, arrowArrows.
    exists (cat_id, cat_id). simpl. now rewrite left_identity, right_identity.
  Defined.

  Instance arrowCatComp: CatComp arrowObj.
  Proof.
    intros [[A1 A2] fA] [[B1 B2] fB] [[C1 C2] fC].
    intros [[h1 h2] ?H]. intros [[g1 g2] ?H]. unfold Arrow, arrowArrows.
    exists (h1 >>> g1, h2 >>> g2). simpl in *.
    now rewrite <- comp_assoc, H2, comp_assoc, H1, comp_assoc.
  Defined.

  Instance arrowCatSetoid: forall (A B: arrowObj), Setoid (A ~> B).
  Proof.
    intros [[A1 A2] fA] [[B1 B2] fB]. unfold Arrow, arrowArrows.
    constructor; repeat intro.
    - destruct x as [[g1 g2] ?H]. cbn. now split.
    - destruct x as [[x1 x2] ?H]. destruct y as [[y1 y2] ?H]. simpl in *. cbn in *.
      destruct H0. split; now symmetry.
    - destruct x as [[x1 x2] ?H]. destruct y as [[y1 y2] ?H].
      destruct z as [[z1 z2] ?H]. simpl in *. cbn in *. destruct H1, H2.
      split; etransitivity; eauto.
  Qed.

  Instance arrowCategory: Category arrowObj.
  Proof.
    constructor; try apply _; intros.
    - destruct a as [[a1 a2] fa]. destruct b as [[b1 b2] fb].
      destruct c as [[c1 c2] fc]. repeat intro. cbn in x, y, x0, y0.
      destruct x as [[gx1 gx2] ?H]. destruct y as [[gy1 gy2] ?H].
      destruct x0 as [[gz1 gz2] ?H]. destruct y0 as [[gw1 gw2] ?H]. cbn in *.
      destruct H1, H2. split.
      + now rewrite H1, H2.
      + now rewrite H7, H8.
    - destruct a as [[a1 a2] fa]. destruct b as [[b1 b2] fb].
      destruct c as [[c1 c2] fc]. destruct d as [[d1 d2] fd]. cbn in f, g, h.
      destruct f as [[f1 f2] ?H]. destruct g as [[g1 g2] ?H].
      destruct h as [[h1 h2] ?H]. cbn in *. split; apply comp_assoc.
    - destruct a as [[a1 a2] fa]. destruct b as [[b1 b2] fb]. cbn in f.
      destruct f as [[f1 f2] ?H]. cbn. split; apply left_identity.
    - destruct a as [[a1 a2] fa]. destruct b as [[b1 b2] fb]. cbn in f.
      destruct f as [[f1 f2] ?H]. cbn. split; apply right_identity.
  Qed.

  Instance domFmap: Fmap (C := arrowObj) (compose fst (@projT1 _ _)).
  Proof.
    repeat intro. destruct v as [[v1 v2] av]. destruct w as [[w1 w2] aw].
    exact (fst (proj1_sig X)).
  Defined.

  Instance domFunctor: Functor (compose fst (@projT1 _ _)) _.
  Proof.
    constructor; try apply _; repeat intro.
    - destruct a as [[a1 a2] aa]. destruct b as [[b1 b2] ab].
      constructor; try apply _. repeat intro. cbn in x, y. cbn.
      destruct x as [[x1 x2] ?H]. destruct y as [[y1 y2] ?H]. cbn in H1. simpl in *.
      destruct H1. easy.
    - destruct a as [[a1 a2] aa]. cbn. easy.
    - destruct x as [[x1 x2] ax]. destruct y as [[y1 y2] ay].
      destruct z as [[z1 z2] az]. cbn in f, g.
      destruct g as [[g1 g2] ?H]. destruct f as [[f1 f2] ?H]. cbn. easy.
  Qed.

  Instance codFmap: Fmap (C := arrowObj) (compose snd (@projT1 _ _)).
  Proof.
    repeat intro. destruct v as [[v1 v2] av]. destruct w as [[w1 w2] aw].
    exact (snd (proj1_sig X)).
  Defined.

  Instance codFunctor: Functor (compose snd (@projT1 _ _)) _.
  Proof.
    constructor; try apply _; repeat intro.
    - destruct a as [[a1 a2] aa]. destruct b as [[b1 b2] ab].
      constructor; try apply _. repeat intro. cbn in x, y. cbn.
      destruct x as [[x1 x2] ?H]. destruct y as [[y1 y2] ?H]. cbn in H1. simpl in *.
      destruct H1. easy.
    - destruct a as [[a1 a2] aa]. cbn. easy.
    - destruct x as [[x1 x2] ax]. destruct y as [[y1 y2] ay].
      destruct z as [[z1 z2] az]. cbn in f, g.
      destruct g as [[g1 g2] ?H]. destruct f as [[f1 f2] ?H]. cbn. easy.
  Qed.

End ARROW_CATEGORY.

(** 4: slice category *)
Section SLICE_CATEGORY.

  Context `{Category C}.

  Definition sliceObj (o: C) := {dom: C & dom ~> o}.

  Instance sliceArrows (o: C): Arrows (sliceObj o).
  Proof.
    intros [A fA] [B fB]. exact {fab: A ~> B | fB >>> fab = fA}.
  Defined.

  Instance sliceCatEq (o: C): forall A B: (sliceObj o), Equiv (A ~> B).
  Proof.
    intros [A fA] [B fB]. unfold Arrow, sliceArrows.
    intros [fab1 ?H] [fab2 ?H]. exact (fab1 = fab2).
  Defined.

  Instance sliceCatId (o: C): CatId (sliceObj o).
  Proof.
    intros [A f]. unfold Arrow, sliceArrows. exists cat_id. apply right_identity.
  Defined.

  Instance sliceCatComp (o: C): CatComp (sliceObj o).
  Proof.
    intros [X fX] [Y fY] [Z fZ]. cbn.
    intros [fyz ?H]. intros [fxy ?H]. exists (fyz >>> fxy).
    rewrite <- H2, <- H1. apply comp_assoc.
  Defined.

  Instance sliceCatSetoid (o: C): forall (A B: sliceObj o), Setoid (A ~> B).
  Proof.
    intros [A fA] [B fB]. cbn. constructor; repeat intro.
    - destruct x as [f ?H]. now cbn.
    - destruct x as [fx ?H]. destruct y as [fy ?H]. cbn in *. now symmetry.
    - destruct x as [fx ?H]. destruct y as [fy ?H]. destruct z as [fz ?H].
      cbn in *. etransitivity; eauto.
  Qed.

  Instance sliceCategory (o: C): Category (sliceObj o).
  Proof.
    constructor; try apply _; intros.
    - destruct a as [a fa]. destruct b as [b fb]. destruct c as [c fc].
      repeat intro. cbn in x, y, x0, y0. destruct x as [fx ?H].
      destruct y as [fy ?H]. destruct x0 as [fz ?H]. destruct y0 as [fw ?H].
      cbn in *. now rewrite H1, H2.
    - destruct a as [a fa]. destruct b as [b fb]. destruct c as [c fc].
      destruct d as [d fd]. cbn in f, g, h. destruct f as [f ?H].
      destruct g as [g ?H]. destruct h as [h ?H]. cbn. apply comp_assoc.
    - destruct a as [a fa]. destruct b as [b fb]. cbn in f. destruct f as [f ?].
      cbn. apply left_identity.
    - destruct a as [a fa]. destruct b as [b fb]. cbn in f. destruct f as [f ?].
      cbn. apply right_identity.
  Qed.

  (** * Chapter 1.9 Exercises 5 Question 1 *)
  Instance sliceForgetFmap (o: C): Fmap (C := sliceObj o) (@projT1 _ _).
  Proof.
    repeat intro. destruct v as [v av]. destruct w as [w aw]. cbn in X.
    cbn. exact (proj1_sig X).
  Defined.

  Instance sliceForgetFunctor (o: C): Functor (C := sliceObj o) (@projT1 _ _) _.
  Proof.
    constructor; try apply _; intros.
    - destruct a as [a fa]. destruct b as [b fb]. constructor; try apply _.
      repeat intro. cbn in x, y. destruct x as [fx ?H]. destruct y as [fy ?H].
      cbn in *. easy.
    - destruct a as [a fa]. cbn. easy.
    - destruct x as [x fx]. destruct y as [y fy]. destruct z as [z fz].
      cbn in f, g. destruct g as [fg ?H]. destruct f as [ff ?H]. cbn. easy.
  Qed.

  Section SLICE_COMP_FUNCTOR.

    Context {c d: C} {g: c ~> d}.

    Definition gM (f: sliceObj c) : sliceObj d.
    Proof. destruct f as [X f]. exists X. exact (g >>> f). Defined.

    Instance sliceCompFmap: Fmap gM.
    Proof.
      repeat intro. destruct v as [dv fv]. destruct w as [dw fw].
      cbn. cbn in X. destruct X as [fab ?H]. exists fab.
      rewrite <- comp_assoc. rewrite H1. easy.
    Defined.

    Instance sliceCompFunctor: Functor gM _.
    Proof.
      constructor; try apply _; intros.
      - constructor; try apply _. repeat intro.
        destruct a as [da fa]. destruct b as [db fb]. cbn in x, y.
        destruct x as [fx ?H]. destruct y as [fy ?H]. cbn. cbn in H1. easy.
      - destruct a as [da fa]. cbn. easy.
      - destruct x as [x fx]. destruct y as [y fy]. destruct z as [z fz].
        cbn in g0, f. destruct g0 as [fg ?H]. destruct f as [ff ?H]. cbn. easy.
    Qed.

  End SLICE_COMP_FUNCTOR.

End SLICE_CATEGORY.

(** 4: coslice category *)
Section COSLICE_CATEGORY.

  Context `{Category C}.
  Context {o : C}.

  Definition cosliceObj := {cod: C & o ~> cod}.

  Instance cosliceArrows: Arrows cosliceObj.
  Proof.
    intros [A fA] [B fB]. exact {fab: A ~> B | fab >>> fA = fB}.
  Defined.

  Instance cosliceCatEq: forall A B: cosliceObj, Equiv (A ~> B).
  Proof.
    intros [A fA] [B fB]. unfold Arrow, cosliceArrows.
    intros [fab1 ?H] [fab2 ?H]. exact (fab1 = fab2).
  Defined.

  Instance cosliceCatId: CatId cosliceObj.
  Proof.
    intros [A f]. unfold Arrow, cosliceArrows. exists cat_id. apply left_identity.
  Defined.

  Instance cosliceCatComp: CatComp cosliceObj.
  Proof.
    intros [X fX] [Y fY] [Z fZ]. cbn.
    intros [fyz ?H]. intros [fxy ?H]. exists (fyz >>> fxy).
    rewrite <- H1, <- H2. symmetry. apply comp_assoc.
  Defined.

  Instance cosliceCatSetoid: forall (A B: cosliceObj), Setoid (A ~> B).
  Proof.
    intros [A fA] [B fB]. cbn. constructor; repeat intro.
    - destruct x as [f ?H]. now cbn.
    - destruct x as [fx ?H]. destruct y as [fy ?H]. cbn in *. now symmetry.
    - destruct x as [fx ?H]. destruct y as [fy ?H]. destruct z as [fz ?H].
      cbn in *. etransitivity; eauto.
  Qed.

  Instance cosliceCategory: Category cosliceObj.
  Proof.
    constructor; try apply _; intros.
    - destruct a as [a fa]. destruct b as [b fb]. destruct c as [c fc].
      repeat intro. cbn in x, y, x0, y0. destruct x as [fx ?H].
      destruct y as [fy ?H]. destruct x0 as [fz ?H]. destruct y0 as [fw ?H].
      cbn in *. now rewrite H1, H2.
    - destruct a as [a fa]. destruct b as [b fb]. destruct c as [c fc].
      destruct d as [d fd]. cbn in f, g, h. destruct f as [f ?H].
      destruct g as [g ?H]. destruct h as [h ?H]. cbn. apply comp_assoc.
    - destruct a as [a fa]. destruct b as [b fb]. cbn in f. destruct f as [f ?].
      cbn. apply left_identity.
    - destruct a as [a fa]. destruct b as [b fb]. cbn in f. destruct f as [f ?].
      cbn. apply right_identity.
  Qed.

End COSLICE_CATEGORY.
