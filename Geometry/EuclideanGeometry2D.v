Require Import Coq.Reals.Reals.
Require Import FormalMath.Algebra.Group.

Definition Point := (R * R)%type.

Definition distance (x y: Point) := sqrt ((fst x - fst y)² + (snd x - snd y)²).

Class Isometric (f: Point -> Point) :=
  {
    inverse: Point -> Point;
    injective: forall x y, f x == f y -> x == y;
    surjective: forall x, f (inverse x) == x;
    distance_preserve: forall x y, distance x y == distance (f x) (f y)
  }.

Arguments inverse _ {_} _.
Arguments injective _ {_} _ _.
Arguments surjective _ {_} _.

Definition Isometry := sigT (fun func => Isometric func).

Global Instance iso_equiv: Equiv Isometry :=
  fun f1 f2 => forall x, (projT1 f1) x == (projT1 f2) x.

Global Instance iso_binop: BinOp Isometry.
Proof.
  intros [f1] [f2].
  refine (existT _ (fun x => f1 (f2 x))
                 (Build_Isometric _ (fun x => (inverse f2) (inverse f1 x)) _ _ _));
    intros.
  - apply (injective f2), (injective f1); auto.
  - do 2 rewrite surjective; reflexivity.
  - transitivity (distance (f2 x) (f2 y)); apply distance_preserve.
Defined.

Global Instance iso_gunit: GrUnit Isometry.
Proof.
  refine (existT _ (fun x => x) (Build_Isometric _ (fun x => x) _ _ _)); intros; auto.
Defined.

Global Instance iso_neg: Negate Isometry.
Proof.
  intros [f].
  refine (existT _ (inverse f) (Build_Isometric _ f _ _ _));
    assert (forall x : Point, inverse f (f x) == x) by
      (intros; apply (injective f), surjective); intros; auto.
  - pose proof (surjective f x). pose proof (surjective f y).
    rewrite <- H0, H1 in H2; assumption.
  - rewrite <- (surjective f x), <- (surjective f y), !H. symmetry.
    apply distance_preserve.
Defined.

Instance: Setoid Isometry.
Proof. constructor; repeat intro; [| rewrite H | rewrite H, H0]; reflexivity. Qed.

Instance: Proper ((=) ==> (=) ==> (=)) iso_binop.
Proof.
  repeat intro. unfold iso_binop. destruct x, y, x0, y0.
  unfold equiv, iso_equiv in H, H0. simpl in *. rewrite H0, H. reflexivity.
Qed.

Instance: Proper ((=) ==> (=)) iso_neg.
Proof.
  repeat intro. unfold iso_neg. destruct x, y. unfold equiv, iso_equiv in H.
  simpl in *. apply (injective x). rewrite surjective, H, surjective. reflexivity.
Qed.

Global Instance isometryGroup: Group Isometry.
Proof.
  constructor; try apply _; intros; unfold bi_op, iso_binop, one, iso_gunit,
                                    neg, iso_neg, equiv, iso_equiv.
  - destruct x, y, z; intros; simpl. reflexivity.
  - destruct x; intros; simpl; reflexivity.
  - destruct x. intros; simpl. apply (injective x). rewrite surjective; reflexivity.
Qed.

Class DiscreteIsometryCondition (P: Isometry -> Prop) :=
  {
    discrete_sub :> SubGroupCondition Isometry P;
    discrete_cond : forall (O: Point) (radius: R), exists (l: list Point),
          forall (g: Subpart Isometry P) (Og: Point),
            Og == projT1 (proj1_sig g) O -> (distance O Og <= radius)%R -> In Og l;
  }.
