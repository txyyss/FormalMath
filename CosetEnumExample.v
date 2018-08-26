Require Import Coq.Classes.EquivDec.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import FormalMath.FreeGroup.
Require Import FormalMath.CosetEnum.
Import ListNotations.

Local Open Scope positive_scope.

Section TWO_GEN_COSET_ENUM.

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

  (* The Roration Group of a Regular Tetrahedron *)
  Definition T_gens := [[Pe X; Pe X; Pe X]; [Pe Y; Pe Y];
                          [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y]].

  Definition T_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) T_gens).

  Definition T_group := standardize (compress (coset_enumration_r T_gens_rep nil 15)).

  Lemma T_group_size: num_coset T_group == 12.
  Proof. native_compute. reflexivity. Qed.

  Compute (print_coset_table T_group).

  (* The Roration Group of a Regular Octahedron *)
  Definition O_gens := [[Pe X; Pe X; Pe X; Pe X]; [Pe Y; Pe Y];
                          [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y]].

  Definition O_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) O_gens).

  Definition O_group := standardize (compress (coset_enumration_r O_gens_rep nil 30)).

  Compute (num_coset O_group).

  Lemma O_group_size: num_coset O_group == 24.
  Proof. native_compute. reflexivity. Qed.

  Compute (generator_permutations O_group).

  (* The Roration Group of a Regular Icosahedron *)
  Definition I_gens := [[Pe X; Pe X; Pe X; Pe X; Pe X]; [Pe Y; Pe Y];
                          [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y]].

  Definition I_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) I_gens).

  Definition I_group := standardize (compress (coset_enumration_r I_gens_rep nil 72)).

  Compute (num_coset I_group).

  Lemma I_group_size: num_coset I_group == 60.
  Proof. native_compute. reflexivity. Qed.

  Compute (generator_permutations I_group).

  (* The Symmetry Group of the 24-Cell *)
  Definition F4_gens :=
    [[Pe X; Pe X; Pe X; Pe X; Pe X; Pe X];
       [Pe Y; Pe Y; Pe Y; Pe Y; Pe Y; Pe Y];
       [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y];
       [Pe X; Pe X; Pe X; Pe Y; Pe X; Pe X; Pe X; Pe Y];
       [Pe X; Pe Y; Pe Y; Pe Y; Pe X; Pe Y; Pe Y; Pe Y]].

  Definition F4_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) F4_gens).

  Definition F4_group :=
    standardize (compress (coset_enumration_r F4_gens_rep nil 1500)).

  Lemma F4_group_size: num_coset F4_group == 1152.
  Proof. native_compute. reflexivity. Qed.

  (* The Symmetry Group of the 600-Cell *)
  Definition H4_gens :=
    [[Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X; Pe X];
       [Pe Y; Pe Y; Pe Y; Pe Y; Pe Y; Pe Y];
       [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y];
       [Pe X; Pe X; Pe X; Pe X; Pe X; Pe Y; Pe X; Pe X; Pe X; Pe X; Pe X; Pe Y];
       [Pe X; Pe Y; Pe Y; Pe Y; Pe X; Pe Y; Pe Y; Pe Y]].

  Definition H4_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) H4_gens).

  Definition H4_group := compress (coset_enumration_r H4_gens_rep nil 19000).

  Lemma H4_group_size: num_coset H4_group == 14400.
  Proof. idtac "Computing H4 group...". Time native_compute. reflexivity. Qed.

  (* Mathieu group M11 *)
  Definition M11_gens :=
    [[Pe X; Pe X]; [Pe Y; Pe Y; Pe Y; Pe Y];
       [Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X;
          Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y; Pe X; Pe Y];
       [Pe X; Pe Y; Pe Y; Pe X; Pe Y; Pe Y; Pe X; Pe Y; Pe Y; Pe X; Pe Y; Pe Y; Pe X;
          Pe Y; Pe Y; Pe X; Pe Y; Pe Y];
       [Pe X; Pe Y; Pe X; Pe Y; Pe X; Ne Y; Pe X; Pe Y; Pe X; Pe Y; Pe Y; Pe X; Ne Y;
          Pe X; Pe Y; Pe X; Ne Y; Pe X; Ne Y]].

  Definition M11_gens_rep :=
    Eval vm_compute in (map (map alphabet_to_positive) M11_gens).

  (* 385465 cosets will be generated *)
  Definition M11_group := compress (coset_enumration_r M11_gens_rep nil 385500).

  Lemma M11_group_size: num_coset M11_group == 7920.
  Proof. idtac "Computing M11 group...". Time native_compute. reflexivity. Qed.

End TWO_GEN_COSET_ENUM.
