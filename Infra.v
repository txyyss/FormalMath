Global Generalizable All Variables.
Global Set Warnings "-notation-overridden".

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

  Context `{Ae : Equiv A} `{Be : Equiv B} `{Ce : Equiv C} (f : A -> B)
          (g: B -> C) `{morphAB: !Setoid_Morphism f} `{morphBC: !Setoid_Morphism g}.

  Lemma setoid_morphism_trans: Setoid_Morphism (compose g f).
  Proof.
    constructor; [exact (setoidmor_a f) | exact (setoidmor_b g) |
                  repeat intro; unfold compose; apply sm_proper;
                  auto; apply sm_proper; auto].
  Qed.

End SETOID_MORPHISM_PROP.

Arguments sm_proper {A Ae B Be f Setoid_Morphism} _ _ _.

Hint Extern 4 (?f _ = ?f _) => eapply (sm_proper (f := f)).

Class Cast A B := cast: A -> B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20) : math_scope.
Instance: Params (@cast) 3.
Typeclasses Transparent Cast.

Definition Cardinals `(s: Setoid A) (n: nat) : Prop :=
  exists l, NoDupA Ae l /\ length l == n /\ forall x: A, InA Ae x l.

Class Inverse `(A -> B) : Type := inverse: B -> A.
Arguments inverse {A B} _ {Inverse} _.
Typeclasses Transparent Inverse.

Section JECTIONS.

  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A -> B) `{inv : !Inverse f}.

  Class Injective : Prop :=
    {
      injective : forall x y, f x = f y -> x = y;
      injective_mor : Setoid_Morphism f
    }.

  Class Surjective : Prop :=
    {
      surjective : forall x: B, f (inverse f x) = x;
      surjective_mor : Setoid_Morphism f
    }.

  Class Bijective : Prop :=
    {
      bijective_injective :> Injective;
      bijective_surjective :> Surjective
    }.

End JECTIONS.

Lemma bijective_the_same_cardinals_forward:
  forall `{Ae: Equiv A} `{Be: Equiv B} (sa: Setoid A) (sb: Setoid B) (f: A -> B)
         `{inv: !Inverse f} `{Bi: !Bijective f} n,
    Cardinals sa n -> Cardinals sb n.
Proof.
  unfold Cardinals. intros. destruct H as [l [? [? ?]]]. exists (map f l).
  split; [|split]. 2: rewrite map_length; assumption. destruct Bi as [Binj Bsur].
  - clear H0 H1. induction l; simpl; constructor; inversion H; subst.
    2: apply IHl; assumption. intro. apply H2. clear H2.
    rewrite InA_alt in H0. destruct H0 as [y [? ?]].
    rewrite in_map_iff in H1. destruct H1 as [x [? ?]].
    assert (f x = f a) by (rewrite H0; rewrite H1; reflexivity).
    apply injective in H4. 2: assumption. rewrite <- H4. apply In_InA; assumption.
  - intros. pose proof (surjective f x). rewrite <- H2.
    cut (InA Ae (inverse f x) l).
    + intros. remember (inverse f x) as y. clear H H0 H1 x Heqy H2.
      induction l; simpl. 1: inversion H3. rewrite InA_cons in H3 |-* .
      destruct Bi as [[_ ?H] _].
      destruct H3; [left; rewrite H0; reflexivity | right; apply IHl; assumption].
    + rewrite InA_alt. specialize (H1 (inverse f x)). rewrite InA_alt in H1.
      destruct H1 as [y [? ?]]. exists y; split; assumption.
Qed.

Lemma bijective_the_same_cardinals_backward:
  forall `{Ae: Equiv A} `{Be: Equiv B} (sa: Setoid A) (sb: Setoid B) (f: A -> B)
         `{inv: !Inverse f} `{Bi: !Bijective f} n,
    Cardinals sb n -> Cardinals sa n.
Proof.
  intros. remember (inverse f) as g. destruct Bi as [[?H ?H] [?H _]].
  assert (Setoid_Morphism g). {
    constructor; [exact (setoidmor_b f) | exact (setoidmor_a f) |]. subst g.
    intros x y ?. rewrite <- (H2 x), <- (H2 y) in H3. apply H0 in H3. assumption. }
  assert (@Bijective _ _ _ _ g f). {
    split; split; try assumption; simpl; intros.
    - subst g. pose proof (H2 x). pose proof (H2 y).
      rewrite H4 in H5. rewrite H5 in H6. assumption.
    - assert (@inverse _ _ g f == f) by reflexivity.
      rewrite H4. subst g. apply H0, H2. }
  apply (@bijective_the_same_cardinals_forward _ _ _ _ sb sa g f); assumption.
Qed.

Lemma bijective_the_same_cardinals:
  forall `{Ae: Equiv A} `{Be: Equiv B} (sa: Setoid A) (sb: Setoid B) (f: A -> B)
         `{inv: !Inverse f} `{Bi: !Bijective f} n, Cardinals sa n <-> Cardinals sb n.
Proof.
  intros. split; intros.
  - apply (bijective_the_same_cardinals_forward sa sb f); assumption.
  - apply (bijective_the_same_cardinals_backward sa sb f); assumption.
Qed.
