Require Import Coq.Classes.EquivDec.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import FormalMath.Word.
Require Import FormalMath.CosetEnum.
Import ListNotations.

Local Open Scope positive_scope.

Fixpoint flatten {A: Type} (l: list (list A)): list A :=
  match l with
  | nil => nil
  | lh :: lt => lh ++ flatten lt
  end.

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

  Definition print_coset_table (ct: CosetTable) :=
    map (fun x => map (fun y => PM.find (tableKey x y) (table ct)) all_gen_reps)
        (gen_pos_list (num_coset ct)).

  Compute (fg_size~0).

  Compute (map positive_to_alphabet [1; 2; 3; 4]).

  (* The Roration Group of a Regular Tetrahedron *)
  Definition T_gens := [repeat (Pe X) 3; repeat (Pe Y) 2;
                          flatten (repeat [Pe X; Pe Y] 3)].

  Definition T_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) T_gens).

  Definition T_group := (compress (coset_enumration_r T_gens_rep nil 16)).

  Lemma T_group_size: num_coset T_group = 12.
  Proof. native_compute. reflexivity. Qed.

  Compute (print_coset_table T_group).

  (* The Roration Group of a Regular Octahedron *)
  Definition O_gens := [repeat (Pe X) 3; repeat (Pe Y) 2;
                          flatten (repeat [Pe X; Pe Y] 4)].

  Definition O_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) O_gens).

  Definition O_group := standardize (compress (coset_enumration_r O_gens_rep nil 35)).

  Compute (num_coset O_group).

  Lemma O_group_size: num_coset O_group = 24.
  Proof. native_compute. reflexivity. Qed.

  Compute (generator_permutations O_group).

  (* The Roration Group of a Regular Icosahedron *)
  Definition I_gens := [repeat (Pe X) 5; repeat (Pe Y) 2;
                          flatten (repeat [Pe X; Pe Y] 3)].

  Definition I_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) I_gens).

  Definition I_group := standardize (compress (coset_enumration_r I_gens_rep nil 72)).

  Compute (num_coset I_group).

  Lemma I_group_size: num_coset I_group = 60.
  Proof. native_compute. reflexivity. Qed.

  Compute (generator_permutations I_group).

  (* The Symmetry Group of the 24-Cell *)
  Definition F4_gens := [repeat (Pe X) 6; repeat (Pe Y) 6;
                           flatten (repeat [Pe X; Pe Y] 4);
                           flatten (repeat [Pe X; Pe X; Pe X; Pe Y] 2);
                           flatten (repeat [Pe X; Pe Y; Pe Y; Pe Y] 2)].

  Definition F4_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) F4_gens).

  Definition F4_group :=
    standardize (compress (coset_enumration_r F4_gens_rep nil 1500)).

  Lemma F4_group_size: num_coset F4_group = 1152.
  Proof. native_compute. reflexivity. Qed.

  (* The Symmetry Group of the 600-Cell *)

  Definition H4_gens :=
    [repeat (Pe X) 10; repeat (Pe Y) 6; flatten (repeat [Pe X; Pe Y] 3);
       flatten (repeat (repeat (Pe X) 5 ++ [Pe Y]) 2);
       flatten (repeat (Pe X :: repeat (Pe Y) 3) 2)].

  Definition H4_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) H4_gens).

  Definition H4_group := compress (coset_enumration_r H4_gens_rep nil 19000).

  Lemma H4_group_size: num_coset H4_group = 14400.
  Proof. idtac "Computing H4 group...". Time native_compute. reflexivity. Qed.

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

  (* Linear Group L_2(27) *)
  Definition L_2_27_gens :=
    [repeat (Pe A) 3; repeat (Pe D) 13; repeat (Pe C) 2;
       flatten (repeat [Pe D; Pe C] 2); flatten (repeat [Pe A; Pe C] 3);
         [Ne D; Ne D; Ne D; Pe A; Pe D; Pe D; Pe D; Ne D; Ne A; Pe D; Ne A];
         [Pe A; Ne D; Pe A; Pe D; Ne A; Ne D; Ne A; Pe D]].

  Definition L_2_27_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) L_2_27_gens).

  (* 21743 cosets will be generated *)
  Definition L_2_27_group := compress (coset_enumration_r L_2_27_gens_rep nil 21750).

  Lemma L_2_27_group_size: num_coset L_2_27_group = 9828.
  Proof. idtac "Compute L_2(27) group...". Time native_compute. reflexivity. Qed.

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
