Global Generalizable All Variables.
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

Class Cast A B := cast: A -> B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20) : math_scope.
Instance: Params (@cast) 3.
Typeclasses Transparent Cast.
