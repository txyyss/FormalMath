Require Import Coq.Classes.EquivDec.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import FormalMath.Word.
Require Import FormalMath.CosetEnum.
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

  Definition print_coset_table (ct: CosetEnum) :=
    map (fun x => map (fun y => table_find x y (coset_table ct))
                      all_gen_reps) (gen_pos_list (num_coset ct)).

  Definition print_coset_map (ct: CosetEnum) :=
    filter_option
      (map (fun x => PM.find x (coset_map ct)) (gen_pos_list (num_coset ct))).

  Compute (fg_size~0).

  Compute (map positive_to_alphabet [1; 2; 3; 4]).

  (* The Roration Group of a Regular Tetrahedron *)
  Definition T_gens := [repeat (Pe X) 3; repeat (Pe Y) 2;
                          flatten (repeat [Pe X; Pe Y] 3)].

  Definition T_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) T_gens).

  Definition T_group := (standardize
                           (compress (coset_enumration_r T_gens_rep nil 16))).

  Lemma T_group_size: num_coset T_group = 12.
  Proof. native_compute. reflexivity. Qed.

  Lemma T_group_rep_test: one_mult_all_rep T_group = gen_pos_list (num_coset T_group).
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

  Lemma O_group_rep_test: one_mult_all_rep O_group = gen_pos_list (num_coset O_group).
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

  Lemma I_group_rep_test: one_mult_all_rep I_group = gen_pos_list (num_coset I_group).
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

  Lemma F4_group_rep_test: one_mult_all_rep F4_group =
                           gen_pos_list (num_coset F4_group).
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

  Lemma H4_group_rep_test: one_mult_all_rep H4_group =
                           gen_pos_list (num_coset H4_group).
  Proof. native_compute. reflexivity. Qed.

  Definition test1_gens := [repeat (Pe X) 3; repeat (Pe Y) 3;
                              [Ne X; Ne Y; Pe X; Pe Y]].
  Definition test1_sub_gens := [[Pe X]].
  Definition test1_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) test1_gens).
  Definition test1_sub_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) test1_sub_gens).
  Definition test1_group :=
    standardize (compress (coset_enumration_r test1_gens_rep test1_sub_gens_rep 10)).
  Eval native_compute in (num_coset test1_group).
  Eval native_compute in (print_coset_table test1_group).

  Definition test2_gens := [repeat (Pe X) 2; repeat (Pe Y) 3;
                              flatten (repeat [Pe X; Pe Y] 3)].
  Definition test2_sub_gens := [[Pe X; Pe Y]].
  Definition test2_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) test2_gens).
  Definition test2_sub_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) test2_sub_gens).
  Definition test2_group :=
    standardize (compress (coset_enumration_r test2_gens_rep test2_sub_gens_rep 10)).
  Eval native_compute in (num_coset test2_group).
  Eval native_compute in (print_coset_table test2_group).

  Definition test3_gens := [repeat (Pe X) 2 ++ repeat (Pe Y) 2;
                              repeat (Pe X) 3 ++ repeat (Pe Y) 5].
  Definition test3_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) test3_gens).
  Definition test3_group := compress (coset_enumration_r test3_gens_rep nil 15).
  Eval native_compute in (num_coset test3_group).
  Eval native_compute in (print_coset_table test3_group).
  Definition test3_std_group := standardize test3_group.
  Eval native_compute in (print_coset_table test3_std_group).

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

  (* Full symmetry group of icosahedron *)
  Definition Ih_gens := [repeat (Pe A) 2; repeat (Pe C) 2; repeat (Pe D) 2;
                           flatten (repeat [Pe A; Pe C] 2);
                           flatten (repeat [Pe C; Pe D] 3);
                           flatten (repeat [Pe A; Pe D] 5)].

  Definition Ih_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) Ih_gens).

  Eval vm_compute in all_gen_reps.

  Definition Ih_group := compress (coset_enumration_r Ih_gens_rep nil 210).

  Lemma Ih_group_size: num_coset Ih_group = 120.
  Proof. native_compute. reflexivity. Qed.

  Lemma Ih_group_rep_test: one_mult_all_rep Ih_group =
                           gen_pos_list (num_coset Ih_group).
  Proof. native_compute. reflexivity. Qed.

  Eval native_compute in (num_coset Ih_group).

  Definition Ih_sub_gens := [[Pe A]].

  Definition Ih_sub_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) Ih_sub_gens).

  Definition Ih_sub_group :=
    compress (coset_enumration_r Ih_gens_rep Ih_sub_gens_rep 210).

  Eval native_compute in (num_coset Ih_sub_group).

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

End THREE_GEN_COSET_ENUM.
