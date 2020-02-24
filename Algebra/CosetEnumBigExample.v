Require Import Coq.Classes.EquivDec.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import FormalMath.Algebra.Word.
Require Import FormalMath.Algebra.CosetEnum.
Require Import FormalMath.lib.List_ext.
Import ListNotations.

Local Open Scope positive_scope.

Section TWO_GEN_COSET_ENUM.

  Inductive TwoGenT := X | Y.

  Instance TwoGenTEqDec: EqDec TwoGenT eq.
  Proof.
    intros x y. unfold complement, Equivalence.equiv.
    change (x = y -> False) with (~ x = y). decide equality.
  Defined.

  Instance FG_TwoGenT: FiniteGenerators TwoGenT.
  Proof.
    apply (Build_FiniteGenerators TwoGenT TwoGenTEqDec [X ; Y] 2); intros.
    - repeat constructor; intuition; simpl in H; intuition. discriminate.
    - destruct x; intuition.
    - simpl. reflexivity.
  Defined.

  (* Mathieu group M11 *)
  Definition M11_gens :=
    [repeat (Pe X) 2; repeat (Pe Y) 4; flatten (repeat [Pe X; Pe Y] 11);
       flatten (repeat [Pe X; Pe Y; Pe Y] 6);
       [Pe X; Pe Y; Pe X; Pe Y; Pe X; Ne Y; Pe X; Pe Y; Pe X; Pe Y; Pe Y; Pe X; Ne Y;
          Pe X; Pe Y; Pe X; Ne Y; Pe X; Ne Y]].

  Definition M11_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) M11_gens).

  (* 385465 cosets will be generated *)
  Definition M11_group := compress (coset_enumration_r M11_gens_rep nil 385500).

  Lemma M11_group_size: num_coset M11_group = 7920.
  Proof. idtac "Computing M11 group...". Time native_compute. reflexivity. Qed.

End TWO_GEN_COSET_ENUM.

Section THREE_GEN_COSET_ENUM.

  Inductive ThreeGenT := A | C | D.

  Instance ThreeGenTEqDec: EqDec ThreeGenT eq.
  Proof.
    intros x y. unfold complement, Equivalence.equiv.
    change (x = y -> False) with (~ x = y). decide equality.
  Defined.

  Instance FG_ThreeGenT: FiniteGenerators ThreeGenT.
  Proof.
    apply (Build_FiniteGenerators ThreeGenT ThreeGenTEqDec [A; C; D] 3); intros.
    - repeat constructor; intuition; simpl in H; intuition; discriminate.
    - destruct x; intuition.
    - simpl. reflexivity.
  Defined.

  (* Mathieu Group M12 *)
  Definition M12_gens :=
    [repeat (Pe A) 11; repeat (Pe C) 2; repeat (Pe D) 2;
       flatten (repeat [Pe A; Pe C] 3); flatten (repeat [Pe A; Pe D] 3);
         flatten (repeat [Pe C; Pe D] 10);
         [Pe A; Pe A; Pe C; Pe D; Pe C; Pe D; Pe A; Ne D; Ne C; Ne D; Ne C]].

  Definition M12_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) M12_gens).

  (* 573191 cosets will be generated *)
  Definition M12_group := compress (coset_enumration_r M12_gens_rep nil 573200).

  Lemma M12_group_size: num_coset M12_group = 95040.
  Proof. idtac "Computing M12 group...". Time native_compute. reflexivity. Qed.

End THREE_GEN_COSET_ENUM.
