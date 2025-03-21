Require Import FormalMath.lib.Sets_ext.
Require Import Stdlib.Logic.Description.

Inductive invertible {X Y: Type} (f: X -> Y): Prop :=
| invertible_intro: forall g: Y -> X,
    (forall x: X, g (f x) = x) -> (forall y: Y, f (g y) = y) -> invertible f.

Inductive FiniteT: Type -> Prop :=
| empty_finite: FiniteT False
| add_finite: forall T: Type, FiniteT T -> FiniteT (option T)
| bij_finite: forall (X Y:Type) (f: X -> Y), FiniteT X -> invertible f -> FiniteT Y.

Lemma True_finite: FiniteT True.
Proof.
  apply bij_finite with (option False) (fun _ => I). 1: constructor; constructor.
  exists (True_rect None).
  - intros. destruct x. 1: easy. remember (True_rect None I) as LHS.
    destruct LHS; easy.
  - exact (fun y: True => match y with | I => refl_equal I end).
Qed.

Lemma finite_dep_choice: forall (A: Type) (B: forall x: A, Type)
                                (R: forall x: A, B x -> Prop),
    FiniteT A -> (forall x: A, exists y: B x, R x y) ->
    exists f: (forall x: A, B x), forall x: A, R x (f x).
Proof.
  intros. revert B R H0. induction H; intros.
  - exists (fun x: False => False_rect (B x) x). destruct x.
  - pose proof (IHFiniteT (fun x: T => B (Some x)) (fun x: T => R (Some x))
                          (fun x: T => H0 (Some x))). destruct H1.
    pose proof (H0 None). destruct H2.
    exists (fun y:option T => match y return (B y) with
                              | Some y0 => x y0 | None => x0 end). destruct x1.
    apply H1. assumption.
  - destruct H0. pose proof (IHFiniteT (fun x: X => B (f x)) (fun x: X => R (f x))
                                       (fun x: X => H1 (f x))). destruct H3.
    pose (f0 := fun y: Y => x (g y)).
    pose (conv := fun (y: Y) (a: B (f (g y))) => eq_rect (f (g y)) B a y (H2 y)).
    exists (fun y:Y => conv y (x (g y))). intro. unfold conv; simpl.
    generalize (H2 x0). pattern x0 at 2 3 6. rewrite <- H2. intro.
    rewrite <- eq_rect_eq. apply H3.
Qed.

Lemma finite_choice:  forall (A B: Type) (R: A -> B -> Prop),
    FiniteT A -> (forall x: A, exists y: B, R x y) ->
    exists f: A -> B, forall x: A, R x (f x).
Proof. intros. now apply finite_dep_choice. Qed.

Lemma exclusive_dec: forall P Q: Prop, ~(P /\ Q) -> (P \/ Q) -> {P} + {Q}.
Proof.
  intros. assert ({x: bool | if x then P else Q}). {
    apply constructive_definite_description. case H0.
    - exists true. red; split; auto. destruct x'; tauto.
    - exists false. red; split; auto. destruct x'; tauto. }
  destruct H1. destruct x; [left | right]; easy.
Qed.

Lemma EqDec_Finite_FiniteT: forall {X:Type} (S: Ensemble X),
    (forall a b: X, {a = b} + {a <> b}) -> Finite S -> FiniteT {x: X | In S x}.
Proof.
  intros. induction H.
  - apply bij_finite with False (False_rect _). 1: constructor.
    assert (g: {x:X | In Empty_set x} -> False). {
      intro. destruct X1. destruct i. } exists g.
    + destruct x.
    + destruct y. destruct g.
  - assert (Included A (Add A x)) by auto with sets.
    assert (In (Add A x) x) by auto with sets.
    pose (g := fun (y: option {x: X | In A x}) =>
                 match y return {x0: X | In (Add A x) x0} with
                 | Some (exist _ y0 i) =>
                   exist (fun x2: X => In (Add A x) x2) y0 (H1 y0 i)
                 | None => exist (fun x2: X => In (Add A x) x2) x H2
                 end). apply bij_finite with _ g.
    + now apply add_finite.
    + assert (h:forall x0:X, In (Add A x) x0 -> { In A x0 } + { x0 = x }). {
        clear -X0. intros. destruct (X0 x0 x). 1: right; auto. left.
        destruct H; auto. inversion H. now subst. }
      pose (ginv := fun s:{x0: X | In (Add A x) x0} =>
                      match s return option {x: X | In A x} with
                      | exist _ x0 i => match (h x0 i) with
                                        | left iA => Some (exist _ x0 iA)
                                        | right _ => None
                                        end
                      end). exists ginv.
      * intro; destruct x0.
        -- destruct s. simpl. remember (h x0 (H1 x0 i)) as sum; destruct sum.
           ++ now destruct (proof_irrelevance _ i i0).
           ++ now subst x0.
        -- simpl. remember (h x H2) as sum; destruct sum; easy.
      * intro. unfold ginv. destruct y. destruct (h x0 i); simpl.
        -- generalize (H1 x0 i0); intro. now destruct (proof_irrelevance _ i i1).
        -- destruct e. now destruct (proof_irrelevance _ H2 i).
Qed.

Lemma Finite_FiniteT: forall {X:Type} (S:Ensemble X),
    Finite S -> FiniteT {x: X | In S x}.
Proof.
  intros. induction H.
  - apply bij_finite with False (False_rect _). 1: constructor.
    assert (g: {x:X | In Empty_set x} -> False). {
      intro. destruct X0. destruct i. } exists g.
    + destruct x.
    + destruct y. destruct g.
  - assert (Included A (Add A x)) by auto with sets.
    assert (In (Add A x) x) by auto with sets.
    pose (g := fun (y: option {x: X | In A x}) =>
                 match y return {x0: X | In (Add A x) x0} with
                 | Some (exist _ y0 i) =>
                   exist (fun x2: X => In (Add A x) x2) y0 (H1 y0 i)
                 | None => exist (fun x2: X => In (Add A x) x2) x H2
                 end). apply bij_finite with _ g.
    + now apply add_finite.
    + assert (h:forall x0:X, In (Add A x) x0 -> { In A x0 } + { x0 = x }). {
        clear -H0. intros; apply exclusive_dec.
        - intuition. subst; auto.
        - destruct H. 1: now left. inversion H. now right. }
      pose (ginv := fun s:{x0: X | In (Add A x) x0} =>
                      match s return option {x: X | In A x} with
                      | exist _ x0 i => match (h x0 i) with
                                        | left iA => Some (exist _ x0 iA)
                                        | right _ => None
                                        end
                      end). exists ginv.
      * intro; destruct x0.
        -- destruct s. simpl. remember (h x0 (H1 x0 i)) as sum; destruct sum.
           ++ now destruct (proof_irrelevance _ i i0).
           ++ now subst x0.
        -- simpl. remember (h x H2) as sum; destruct sum; easy.
      * intro. unfold ginv. destruct y. destruct (h x0 i); simpl.
        -- generalize (H1 x0 i0); intro. now destruct (proof_irrelevance _ i i1).
        -- destruct e. now destruct (proof_irrelevance _ H2 i).
Qed.

Lemma finite_or_exists: forall (X:Type) (P: X -> Prop),
    FiniteT X -> (forall x:X, (P x) \/ (~ P x)) ->
    (exists x:X, P x) \/ (forall x:X, ~ P x).
Proof.
  intros. revert P H0. induction H.
  - right. destruct x.
  - intros. case (IHFiniteT (fun x:T => P (Some x)) (fun x:T => H0 (Some x))).
    + left. destruct H1. exists (Some x). assumption.
    + intro. case (H0 None).
      * left. exists None. assumption.
      * right. destruct x.
        -- apply H1.
        -- assumption.
  - destruct H0. intros.
    case (IHFiniteT (fun x:X => P (f x)) (fun x:X => H2 (f x))).
    + left. destruct H3. exists (f x). assumption.
    + right. intro. rewrite <- H1 with x. apply H3.
Qed.

Lemma FiniteT_img: forall (X Y:Type) (f:X->Y),
    FiniteT X -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) ->
    Finite (Im Full_set f).
Proof.
  intros. induction H.
  - replace (Im Full_set f) with (@Empty_set Y). 1: constructor.
    apply Extensionality_Ensembles; split; red; intros; destruct H. destruct x.
  - assert ((exists x:T, f (Some x) = f None) \/ (forall x:T, f (Some x) <> f None)).
    + apply finite_or_exists; auto.
    + case H1.
      * intro. pose (g := fun (x:T) => f (Some x)).
        replace (Im Full_set f) with (Im Full_set g). 1: apply IHFiniteT.
        apply Extensionality_Ensembles; split; red; intros.
        -- destruct H3. subst. exists (Some x); easy.
        -- destruct H3. subst. destruct x.
           ++ exists t; easy.
           ++ destruct H2. exists x.
              ** constructor.
              ** destruct H3. subst g. symmetry. assumption.
      * intros. pose (g := fun x:T => f (Some x)).
        replace (Im Full_set f) with (Add (Im Full_set g) (f None)).
        -- constructor.
           ++ apply IHFiniteT.
           ++ red; intro. destruct H3. contradiction (H2 x). symmetry; assumption.
        -- apply Extensionality_Ensembles; split; red; intros.
           ++ red; intros. destruct H3, H3; [exists (Some x) | exists None]; easy.
           ++ red; intros. destruct H3. destruct x.
              ** left. exists t; easy.
              ** right. auto with sets.
  - pose (g := fun (x:X) => f (f0 x)).
    replace (Im Full_set f) with (Im Full_set g). 1: apply IHFiniteT.
    apply Extensionality_Ensembles; split; red; intros.
    + destruct H2. exists (f0 x); easy.
    + destruct H2, H1. subst. rewrite <- H4 with x. now exists (g0 x).
Qed.
