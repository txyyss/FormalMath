Global Generalizable All Variables.
Global Set Automatic Introduction.
Global Set Warnings "-notation-overridden".

Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Lists.List.
Require Export Coq.Lists.SetoidList.

(******************************* Hint *******************************)

Hint Unfold Proper respectful.
Hint Unfold Reflexive Symmetric Transitive.
Hint Constructors PreOrder.

Ltac auto_symm :=
  match goal with
    [ H : ?R ?x ?y |- ?R ?y ?x] => apply (symmetry H)
  end.

Ltac auto_trans :=
  match goal with
    [ H : ?R ?x ?y, I : ?R ?y ?z |- ?R ?x ?z] => apply (transitivity H I)
  end.

Ltac exist_hyp := match goal with [ H : sig ?P |- ?P _  ] => exact (proj2_sig H) end.
Hint Extern 0 => exist_hyp : core typeclass_instances.

Ltac exist_proj1 :=
  match goal with
    | [ |- context [proj1_sig ?x] ] => apply (proj2_sig x)
  end.
Hint Extern 0 => exist_proj1 : core typeclass_instances.

(******************************* Equality *******************************)

Class Equiv A := equiv : relation A.

Typeclasses Transparent Equiv.

Infix "=" := equiv : type_scope.

Notation "(=)" := equiv (only parsing) : math_scope.
Notation "( x =)" := (equiv x) (only parsing) : math_scope.
Notation "(= x )" := (fun y => equiv y x) (only parsing) : math_scope.

Delimit Scope math_scope with math.
Global Open Scope math_scope.

Hint Extern 2 (?x = ?x) => reflexivity.
Hint Extern 2 (?x = ?y) => auto_symm.
Hint Extern 2 (?x = ?y) => auto_trans.

Instance equiv_default_relation `{Equiv A} : DefaultRelation (=) | 3.

Infix "==" := eq (at level 70, no associativity) : math_scope.
Notation "(==)" := eq (only parsing) : math_scope.
Notation "( x ==)" := (eq x) (only parsing) : math_scope.
Notation "(== x )" := (fun y => eq y x) (only parsing) : math_scope.
Notation "(=/=)" := (fun x y => ~ x == y) (only parsing) : math_scope.
Notation "x =/= y" := (~ x == y) (at level 70, no associativity) : math_scope.
Notation "( x =/=)" := (fun y => x =/= y) (only parsing) : math_scope.
Notation "(=/= x )" := (fun y => y =/= x) (only parsing) : math_scope.

(******************************* Setoid *******************************)

Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

Section SETOID_MORPHISM.
  
  Context `{Ae : Equiv A} `{Be : Equiv B} (f : A -> B).

  Class Setoid_Morphism :=
    {
      setoidmor_a : Setoid A ;
      setoidmor_b : Setoid B ;
      sm_proper :> Proper ((=) ==> (=)) f
    }.

End SETOID_MORPHISM.

Section SETOID_MORPHISM_PROP.

  Context `{Ae : Equiv A} `{Be : Equiv B} `{Ce : Equiv C} (f : A -> B) (g: B -> C) `{morphAB: !Setoid_Morphism f} `{morphBC: !Setoid_Morphism g}.

  Lemma setoid_morphism_trans: Setoid_Morphism (compose g f).
  Proof. constructor; [exact (setoidmor_a f) | exact (setoidmor_b g) | repeat intro; unfold compose; apply sm_proper; auto; apply sm_proper; auto]. Qed.
  
End SETOID_MORPHISM_PROP.

Arguments sm_proper {A Ae B Be f Setoid_Morphism} _ _ _.

Hint Extern 4 (?f _ = ?f _) => eapply (sm_proper (f := f)).

Class Pred A := pred : A -> Prop.

Definition Sub {A} (PA : Pred A) := {x : A | pred x}.

Definition sub_int_pred {A} (P1 P2 : Pred A) : Pred A := fun m => (@pred _ P1) m /\ (@pred _ P2) m.

Definition subsub_int_pred {A} (P1 P2 : Pred A) : Pred (Sub P1) := fun m => (@pred _ P2) (proj1_sig m).

Instance sub_equiv `{Equiv A} (PA : Pred A) : Equiv (Sub PA) := fun x y => proj1_sig x = proj1_sig y.

Definition pred_equiv {A} (P1 P2 : Pred A) := pointwise_relation A iff (@pred _ P1) (@pred _ P2).

Instance pred_equiv_equiv {A} : Equivalence (@pred_equiv A) := Equivalence.pointwise_equivalence iff_equivalence.

Section SUB_SUB.
  
  Context {A} (P1 P2: Pred A).

  Lemma subsub_sub_satisfied: forall (x : Sub (subsub_int_pred P1 P2)), (@pred _ (sub_int_pred P1 P2)) (proj1_sig (proj1_sig x)). Proof. intros. split; auto. Qed.
  
  Definition subsub_sub (x : Sub (subsub_int_pred P1 P2)) : Sub (sub_int_pred P1 P2) := exist _ (proj1_sig (proj1_sig x)) (subsub_sub_satisfied x).

  Definition sub_subsub (x: Sub (sub_int_pred P1 P2)) : Sub (subsub_int_pred P1 P2) := exist _ (exist _ (proj1_sig x) (proj1 (proj2_sig x))) (proj2 (proj2_sig x)).

End SUB_SUB.

Class SubSetoid A {Ae : Equiv A} (PA : Pred A) : Prop :=
  {
    super_setoid :> Setoid A;
    pred_proper :> Proper ((=) ==> iff) pred
  }.

Section SUBSETOID_PROP.

  Context `(SS : SubSetoid A).

  Lemma sub_eq_refl : forall (x : Sub PA), x = x. Proof. intros. unfold sub_equiv. red. auto. Qed.

  Lemma sub_eq_sym : forall (x y : Sub PA), x = y -> y = x. Proof. intros. unfold equiv, sub_equiv. symmetry; auto. Qed.

  Lemma sub_eq_trans : forall (x y z : Sub PA), x = y -> y = z -> x = z.
  Proof. unfold sub_equiv; intros. unfold equiv, sub_equiv. transitivity (proj1_sig y); auto. Qed.

  Instance sub_equivalence : Equivalence (sub_equiv PA). Proof. constructor; hnf. apply sub_eq_refl. apply sub_eq_sym. apply sub_eq_trans. Qed.

  Instance subsetoid_as_setoid : Setoid (Sub PA). Proof. apply sub_equivalence. Qed.

End SUBSETOID_PROP.

Definition pred_impl {A} (P1 P2: Pred A) := pointwise_relation A impl (@pred _ P1) (@pred _ P2).

Lemma pred_equiv_impl {A}: forall (P1 P2: Pred A), pred_equiv P1 P2 <-> (pred_impl P1 P2 /\ pred_impl P2 P1).
Proof.
  unfold pred_equiv, pred_impl, pointwise_relation. split; intros; split; intros; [rewrite H; intro | rewrite H; intro | destruct H; apply H | destruct H; apply H1]; auto. 
Qed.  

Section SUBSETOID_IFF.

  Context `{S : Setoid A} {P1 P2 : Pred A}.

  Lemma pred_equiv_subsetoid_iff : pred_equiv P1 P2 -> SubSetoid A P1 <-> SubSetoid A P2.
  Proof. unfold pred_equiv, pointwise_relation. intros. split; intros; constructor; auto; repeat intro; [rewrite <- !H | rewrite !H]; rewrite H1; tauto. Qed.

  Lemma setoid_sub_another : pred_equiv P1 P2 -> SubSetoid A P1 -> Setoid (Sub P2).
  Proof. intros. rewrite pred_equiv_subsetoid_iff in H0; [apply subsetoid_as_setoid |]; auto. Qed.

End SUBSETOID_IFF.

(* Existing Instance subsetoid_as_setoid. *)

(* Coercion subsetoid_as_setoid : SubSetoid >-> Setoid. *)

Class FiniteSetoid `(SA : Setoid A) := all_members : {l : list A | NoDupA (=) l /\ forall x, InA (=) x l}.

Definition cardinal `(SA : Setoid A) {FA : FiniteSetoid SA} := length (proj1_sig FA).

Class QuotientSetoid A (Ae : Equiv A) (Asub : Equiv A) : Prop :=
  {
    q_super_setoid : @Setoid A Ae;
    still_eq :> Equivalence Asub;
    sub_rel :> subrelation Ae Asub;
  }.

Section QUOTIENT_SETOID.

  Context `{QS : QuotientSetoid A}.

  Instance quotient_setoid_as_setoid : @Setoid A Asub. Proof. apply still_eq. Qed.

  Instance quotient_setoid_natural_morph : @Setoid_Morphism A Ae A Asub id.
  Proof. constructor; [exact q_super_setoid | exact quotient_setoid_as_setoid | repeat intro; unfold id; rewrite H; auto]. Qed.

End QUOTIENT_SETOID.

(* Existing Instance quotientsetoid_as_setoid. *)

(* Coercion quotientsetoid_as_setoid : QuotientSetoid >-> Setoid. *)

(******************************* Bijection *******************************)

Section Jections.

  Context `{Ae : Equiv A} `{Be : Equiv B} (f : A -> B).

  Class Injective : Prop :=
    {
      injective : forall x y, f x = f y -> x = y ;
      injective_mor : Setoid_Morphism f
    }.

  Class Surjective : Prop :=
    {
      surjective : forall x, exists y, f y = x;
      surjective_mor : Setoid_Morphism f
    }.

  Class Bijective : Prop :=
    {
      bijective_injective :> Injective;
      bijective_surjective :> Surjective
    }.

End Jections.

Section BIJECTIVE_TRANS.

  Context `{Ae : Equiv A} `{Be : Equiv B} `{Ce : Equiv C} (f : A -> B) (g: B -> C).
  Context `{biAB: !Bijective f} `{biBC: !Bijective g}.

  Instance bijective_trans: Bijective (compose g f).
  Proof.
    assert (SM: Setoid_Morphism (compose g f)) by (apply setoid_morphism_trans; [exact (injective_mor f) | exact (injective_mor g)]). constructor; constructor; auto.
    - intros. unfold compose in H. apply (injective f), (injective g); auto.
    - intros. unfold compose. destruct (surjective g x) as [fy ?]. destruct (surjective f fy) as [y' ?]. exists y'.
      pose proof (injective_mor g). destruct H1. rewrite <- H0 in H. auto.
  Qed.
  
End BIJECTIVE_TRANS.
