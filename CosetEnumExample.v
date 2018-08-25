Require Import Coq.Classes.EquivDec.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import FormalMath.FreeGroup.
Require Import FormalMath.CosetEnum.
Import ListNotations.

Local Open Scope positive_scope.

Section TWO_GEN_COSET_ENUM.

  Definition print_coset_map (ct: CosetTable) :=
    map (fun x => (x, PM.find x (coset_map ct))) (gen_pos_list (num_coset ct)).

  Inductive GenT := X | Y.

  Instance GenTEqDec: EqDec GenT eq.
  Proof.
    intros x y. unfold complement, Equivalence.equiv.
    change (x == y -> False) with (~ x == y). decide equality.
  Defined.

  Instance FG_GenT: FiniteGenerators GenT.
  Proof.
    apply (Build_FiniteGenerators GenT GenTEqDec [X ; Y] 2); intros.
    - repeat constructor; intuition; simpl in H; intuition. discriminate.
    - destruct x; intuition.
    - simpl. reflexivity.
  Defined.

  Definition print_coset_table (ct: CosetTable) :=
    map (fun x => map (fun y => PM.find (tableKey x y) (table ct)) all_gen_reps)
        (gen_pos_list (num_coset ct)).

  Compute (fg_size~0).

  Compute (map positive_to_alphabet [1; 2; 3; 4]).

  Definition gen_grp_a := [[Pe X; Pe X; Pe X];
                             [Pe Y; Pe Y; Pe Y];
                             [Ne X; Ne Y; Pe X; Pe Y]].

  Compute (map (map alphabet_to_positive) gen_grp_a).

  Definition gen_grp1 := [[1; 1; 1]; [2; 2; 2]; [4; 3; 1; 2]].

  Definition ct1 := coset_enumration_r gen_grp1 nil 20.

  Compute (print_coset_table ct1).

  Compute (print_coset_map ct1).

  Definition gen_grp_b := [[Pe X; Pe Y; Pe X; Pe Y; Ne X; Ne X; Ne X];
                             [Pe X; Pe X; Pe X; Ne Y; Ne Y; Ne Y]].

  Compute (map (map alphabet_to_positive) gen_grp_b).

  Definition gen_grp2 := [[1; 2; 1; 2; 4; 4; 4]; [1; 1; 1; 3; 3; 3]].

  Definition ct2 := coset_enumration_r gen_grp2 nil 150.

  Definition cct2 := compress ct2.

  Compute (length (print_coset_table cct2)).

  Compute (print_coset_map cct2).

  Definition gen_grp_c := [[Pe X; Pe X]; [Pe Y; Pe Y; Pe Y];
                             [Pe X; Pe Y; Pe X; Pe Y;
                                Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y]].

  Compute (map (map alphabet_to_positive) gen_grp_c).

  Definition gen_grp3 := [[1; 1]; [2; 2; 2]; [1; 2; 1; 2; 1; 2; 1; 2; 1; 2]].

  Definition ct3 := coset_enumration_r gen_grp3 nil 100.

  Definition cct3 := compress ct3.

  Compute (generator_permutations cct3).

  Definition sct3 := standardize cct3.

  Compute (generator_permutations sct3).

  Definition F4_gens_a :=
    [[Pe X; Pe X; Pe X; Pe X; Pe X; Pe X];
       [Pe Y; Pe Y; Pe Y; Pe Y; Pe Y; Pe Y];
       [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y];
       [Pe X; Pe X; Pe X; Pe Y; Pe X; Pe X; Pe X; Pe Y];
       [Pe X; Pe Y; Pe Y; Pe Y; Pe X; Pe Y; Pe Y; Pe Y]].

  Definition F4_gens := Eval compute in (map (map alphabet_to_positive) F4_gens_a).

  Definition F4_grp := standardize (compress (coset_enumration_r F4_gens nil 1500)).

  Lemma F4_group_size: num_coset F4_grp == 1152.
  Proof. native_compute. reflexivity. Qed.

  Definition H4_gens_a :=
    [[Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X];
       [Pe Y; Pe Y; Pe Y; Pe Y; Pe Y; Pe Y];
       [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y];
       [Pe X; Pe X; Pe X; Pe X; Pe X; Pe Y; Pe X; Pe X; Pe X; Pe X; Pe X; Pe Y];
       [Pe X; Pe Y; Pe Y; Pe Y; Pe X; Pe Y; Pe Y; Pe Y]].

  Definition H4_gens := Eval vm_compute in (map (map alphabet_to_positive) H4_gens_a).

  Definition H4_grp := (compress (coset_enumration_r H4_gens nil 19000)).

  Lemma H4_group_size: num_coset H4_grp == 14400.
  Proof. Time native_compute. reflexivity. Qed.

End TWO_GEN_COSET_ENUM.
