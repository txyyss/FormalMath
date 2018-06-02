Require Import Coq.Classes.EquivDec.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import FormalMath.FreeGroup.
Import ListNotations.

Module PM := PositiveMap.

Local Open Scope positive_scope.

Class FiniteGenerators (A: Type) :=
  {
    fg_decidable: EqDec A eq;
    fg_gens: list A;
    fg_size: positive;
    fg_gens_nodup: NoDup fg_gens;
    fg_gens_all: forall x : A, In x fg_gens;
    fg_gens_size: length fg_gens == Pos.to_nat fg_size;
  }.

Existing Instance fg_decidable.

Tactic Notation "if_tac" :=
  match goal with |- context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ => destruct a
    | bool => destruct a eqn: ?
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
    end end.

Tactic Notation "if_tac" "in" hyp(H0)
 := match type of H0 with context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ => destruct a
    | bool => destruct a eqn: ?
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
   end end.

Section TODD_COXETER_ALGORITHM.

  Context `{FG: FiniteGenerators A}.

  Lemma fg_gens_not_nil: fg_gens == nil -> False.
  Proof.
    intros. pose proof fg_gens_size. rewrite H in H0.
    simpl in H0. pose proof (Pos2Nat.is_pos fg_size). exfalso. intuition.
  Qed.

  Definition anyA : A.
    destruct fg_gens eqn:?; [exact (False_rect A (fg_gens_not_nil Heql)) | exact a].
  Defined.

  Definition positive_to_alphabet (n: positive) : Alphabet A :=
    if (n <=? fg_size)
    then intro_gen (nth (pred (Pos.to_nat n)) fg_gens anyA)
    else intro_inv (nth (pred (Pos.to_nat (n - fg_size))) (rev fg_gens) anyA).

  Fixpoint a2p_helper (x: A) (l: list A) (n: positive): positive :=
    match l with
    | nil => n
    | y :: l' => if (equiv_dec x y) then n else a2p_helper x l' (Pos.succ n)
    end.

  Lemma a2p_helper_low: forall x l n, n <= a2p_helper x l n.
  Proof.
    intro x. induction l; intros; simpl. 1: intuition. if_tac.
    - intuition.
    - specialize (IHl (Pos.succ n)). transitivity (Pos.succ n). 2: assumption.
      rewrite <- Pos.add_1_r. apply Pos.lt_le_incl, Pos.lt_add_r.
  Qed.

  Lemma pos_add_succ: forall n m, n + Pos.succ m == Pos.succ n + m.
  Proof.
    intros. rewrite <- (Pos.add_1_l m), Pos.add_assoc, Pos.add_1_r. reflexivity.
  Qed.

  Lemma pos_succ_add_sub: forall n m, Pos.succ n + m - 1 == n + m.
  Proof.
    intros. rewrite <- Pos.add_1_r, <- Pos.add_assoc, (Pos.add_comm 1),
            Pos.add_assoc, Pos.add_sub. reflexivity.
  Qed.

  Lemma a2p_helper_In:
    forall x l n, In x l <-> a2p_helper x l n < n + Pos.of_succ_nat (length l) - 1.
  Proof.
    intros x l. induction l; intros; simpl.
    1: rewrite Pos.add_sub; intuition; apply Pos.lt_irrefl in H; auto.
    rewrite pos_add_succ. split; intros; [if_tac | if_tac in H].
    - rewrite pos_succ_add_sub. apply Pos.lt_add_r.
    - rewrite <- IHl. destruct H; auto. compute in c. exfalso; auto.
    - left; auto.
    - right. rewrite (IHl (Pos.succ n)); auto.
  Qed.

  Lemma nth_a2p_helper: forall x l n a,
      In x l -> nth (Pos.to_nat (a2p_helper x l n) - Pos.to_nat n) l a == x.
  Proof.
    intro x. induction l; intros. 1: simpl; inversion H.
    Opaque nth. simpl. if_tac. Transparent nth.
    - simpl. rewrite PeanoNat.Nat.sub_diag. rewrite e. reflexivity.
    - compute in c. simpl in H. destruct H. 1: exfalso; auto.
      specialize (IHl (Pos.succ n) a0 H). rewrite <- IHl at 2.
      rewrite Pos2Nat.inj_succ. simpl.
      destruct ((Pos.to_nat (a2p_helper x l (Pos.succ n)) - Pos.to_nat n)%nat) eqn: ?.
      + rewrite PeanoNat.Nat.sub_0_le in Heqn0. exfalso.
        pose proof (a2p_helper_low x l (Pos.succ n)).
        rewrite Pos2Nat.inj_le, Pos2Nat.inj_succ in H0. intuition.
      + rewrite PeanoNat.Nat.sub_succ_r, Heqn0, PeanoNat.Nat.pred_succ. reflexivity.
  Qed.

  Lemma a2p_heler_nth: forall x l n a,
      (Pos.to_nat x <= length l)%nat -> NoDup l ->
      a2p_helper (nth (Init.Nat.pred (Pos.to_nat x)) l a) l n == x + n - 1.
  Proof.
    intros x l. revert x. induction l; intros.
    - simpl in *. exfalso. pose proof (Pos2Nat.is_pos x). intuition.
    - Opaque nth. simpl. if_tac. Transparent nth.
      + simpl in e. destruct (pred (Pos.to_nat x)) eqn: ?.
        * clear -Heqn0. rewrite Nat.eq_pred_0 in Heqn0. destruct Heqn0.
          -- exfalso. pose proof (Pos2Nat.is_pos x). intuition.
          -- rewrite <- Pos2Nat.inj_1, Pos2Nat.inj_iff in H. subst.
             rewrite Pos.add_comm, Pos.add_sub. reflexivity.
        * exfalso. rewrite NoDup_cons_iff in H0. destruct H0 as [? _]. apply H0.
          rewrite <- e. apply nth_In. simpl in H.
          pose proof (Pos2Nat.is_pos x). omega.
      + simpl in *. destruct (pred (Pos.to_nat x)) eqn: ?.
        * exfalso. compute in c. apply c. auto.
        * rewrite NoDup_cons_iff in H0. destruct H0 as [_ ?].
          assert (1 < x) by (rewrite Pos2Nat.inj_lt, Pos2Nat.inj_1; omega).
          assert ((Pos.to_nat (x - 1) <= length l)%nat) by
              (rewrite Pos2Nat.inj_sub; auto; rewrite Pos2Nat.inj_1; omega).
          specialize (IHl (x - 1) (n + 1) a0 H2 H0).
          rewrite <- Nat.sub_1_r in *. rewrite Pos2Nat.inj_sub in *; auto.
          rewrite Pos2Nat.inj_1 in *. rewrite <- Pos.add_1_r.
          assert (n0 == (Pos.to_nat x - 1 - 1)%nat) by omega. rewrite H3.
          rewrite IHl. rewrite Pos.add_assoc, Pos.add_sub, (Pos.add_comm x n),
                       <- Pos.add_sub_assoc; auto. rewrite Pos.add_comm. reflexivity.
  Qed.

  Lemma a2p_helper_not_In:
    forall x l n, ~ In x l <-> a2p_helper x l n == n + Pos.of_succ_nat (length l) - 1.
  Proof.
    intros x l. induction l; intros; simpl. 1: rewrite Pos.add_sub; intuition.
    rewrite pos_add_succ. if_tac.
    - rewrite pos_succ_add_sub.
      pose proof (Pos.add_no_neutral n (Pos.of_succ_nat (length l))).
      rewrite Pos.add_comm in H. intuition.
    - rewrite <- IHl. intuition.
  Qed.

  Definition alphabet_to_positive (x: Alphabet A) : positive :=
    match x with
    | intro_gen y => a2p_helper y fg_gens xH
    | intro_inv y => (xI fg_size) - (a2p_helper y fg_gens xH)
    end.

  Lemma a2p2a_the_same: forall x, positive_to_alphabet (alphabet_to_positive x) == x.
  Proof.
    intros. unfold positive_to_alphabet, alphabet_to_positive.
    assert (forall x, x <= fg_size <->
                        x < 1 + Pos.of_succ_nat (length fg_gens) - 1). {
      intro. rewrite Pos.add_comm, Pos.add_sub, fg_gens_size, Pos2SuccNat.id_succ,
             Pos.lt_succ_r. apply iff_refl.
    } assert (forall a, a2p_helper a fg_gens 1 <= fg_size). {
      intros. rewrite H, <- a2p_helper_In. apply fg_gens_all.
    } destruct x.
    - if_tac.
      + rewrite Pos.leb_le, H, <- a2p_helper_In in Heqb.
        rewrite Minus.pred_of_minus, nth_a2p_helper; auto.
      + rewrite Pos.leb_nle in Heqb. exfalso. apply Heqb. apply H0.
    - pose proof (Pos.mul_xI_r 1 fg_size).
      rewrite !Pos.mul_1_l, <- Pos.add_diag, Pos.add_assoc in H1.
      assert (a2p_helper a fg_gens 1 < 1 + fg_size). {
          apply Pos.le_lt_trans with fg_size; auto. rewrite Pos.add_comm.
          apply Pos.lt_add_r.
      } assert (1 + fg_size + fg_size - a2p_helper a fg_gens 1 ==
                1 + fg_size - a2p_helper a fg_gens 1 + fg_size). {
        rewrite (Pos.add_comm 1) at 1.
        rewrite <- Pos.add_assoc,  <- Pos.add_sub_assoc, Pos.add_comm; auto.
      } if_tac.
      + rewrite Pos.leb_le in Heqb. specialize (H0 a). exfalso.
        rewrite H1 in Heqb. clear H1. rewrite H3 in Heqb. clear H3.
        apply (Pos.lt_irrefl fg_size).
        eapply Pos.lt_le_trans; eauto. rewrite Pos.add_comm. apply Pos.lt_add_r.
      + rewrite H1 in *. clear H1. rewrite Pos.leb_gt in Heqb. specialize (H0 a).
        assert ((Pos.to_nat (1 + fg_size - a2p_helper a fg_gens 1) <=
                 Pos.to_nat fg_size)%nat). {
          rewrite <- Pos2Nat.inj_le, <- Pos.lt_succ_r, <- Pos.add_1_l.
          apply Pos.sub_decr; auto.
        } rewrite H3, Pos.add_sub, rev_nth; rewrite fg_gens_size.
        * rewrite <- (Lt.S_pred _ O). 2: apply Pos2Nat.is_pos.
          rewrite Pos2Nat.inj_sub; auto.
          assert (forall (n m p : nat),
                     (p < m)%nat ->
                     ((m - p)%nat <= n)%nat -> (n - (m - p) == n + p - m)%nat). {
            clear. intros. omega.
          } rewrite H4. clear H4.
          -- rewrite Pos2Nat.inj_add.
             replace (Pos.to_nat fg_size + Pos.to_nat (a2p_helper a fg_gens 1) -
                                          (Pos.to_nat 1 + Pos.to_nat fg_size))%nat
               with (Pos.to_nat (a2p_helper a fg_gens 1) - Pos.to_nat 1)%nat by omega.
             f_equal. rewrite nth_a2p_helper; auto. apply fg_gens_all.
          -- rewrite <- Pos2Nat.inj_lt. assumption.
          -- rewrite <- Pos2Nat.inj_sub; auto.
        * assert (forall n m, (O < n)%nat -> (Nat.pred n < m <-> n <= m)%nat) by
              (intros; omega). rewrite H4; clear H4; auto. apply Pos2Nat.is_pos.
  Qed.

  Lemma p2a2p_the_same:
    forall x, x <= fg_size~0 -> alphabet_to_positive (positive_to_alphabet x) == x.
  Proof.
    intros. unfold positive_to_alphabet, alphabet_to_positive. if_tac.
    - rewrite Pos.leb_le in Heqb. rewrite a2p_heler_nth.
      + rewrite Pos.add_sub. reflexivity.
      + rewrite fg_gens_size, <- Pos2Nat.inj_le. assumption.
      + apply fg_gens_nodup.
    - rewrite Pos.leb_gt in Heqb. rewrite <- Pos.add_diag in H.
      pose proof (Pos.mul_xI_r 1 fg_size).
      rewrite !Pos.mul_1_l, <- Pos.add_diag, Pos.add_assoc in H0. rewrite H0. clear H0.
      assert (Pos.to_nat (x - fg_size) - 1 < length fg_gens)%nat. {
        rewrite fg_gens_size, Pos2Nat.inj_sub; auto.
        rewrite Pos2Nat.inj_le, Pos2Nat.inj_add in H.
        pose proof (Pos2Nat.is_pos x). pose proof (Pos2Nat.is_pos fg_size). omega.
      } rewrite <- Nat.sub_1_r, rev_nth; auto.
      remember (length fg_gens - S (Pos.to_nat (x - fg_size) - 1))%nat.
      replace n with (pred (n + 1)) by omega.
      rewrite <- (Nat2Pos.id (n + 1)) by omega.
      pose proof (Pos2Nat.is_pos fg_size). pose proof (Pos2Nat.is_pos x).
      assert (1 < x) by (rewrite Pos2Nat.inj_lt in Heqb;
                         rewrite Pos2Nat.inj_lt, Pos2Nat.inj_1; omega).
      assert (x - 1 < fg_size + fg_size). {
        rewrite Pos2Nat.inj_lt, Pos2Nat.inj_add, Pos2Nat.inj_sub; auto.
        rewrite Pos2Nat.inj_1. rewrite Pos2Nat.inj_le, Pos2Nat.inj_add in H. omega.
      } assert (length fg_gens - S (Pos.to_nat (x - fg_size) - 1) + 1 ==
                Pos.to_nat (fg_size + fg_size - (x - 1)))%nat. {
        replace (S (Pos.to_nat (x - fg_size) - 1)) with (Pos.to_nat (x - fg_size)) by
            (pose proof (Pos2Nat.is_pos (x - fg_size)); omega).
        rewrite fg_gens_size, Pos2Nat.inj_sub; auto.
        rewrite Pos2Nat.inj_lt in Heqb. rewrite Pos2Nat.inj_le, Pos2Nat.inj_add in H.
        replace (Pos.to_nat fg_size - (Pos.to_nat x - Pos.to_nat fg_size) + 1)%nat
          with (Pos.to_nat fg_size + Pos.to_nat fg_size - (Pos.to_nat x - 1))%nat
          by omega. rewrite <- Pos2Nat.inj_add, <- Pos2Nat.inj_1.
        rewrite <- !Pos2Nat.inj_sub; auto.
      } rewrite a2p_heler_nth; [ subst; rewrite H5.. | apply fg_gens_nodup].
      + rewrite Pos2Nat.id, Pos.add_sub. rewrite Pos.sub_sub_distr; auto.
        * rewrite Pos.add_comm, <- Pos.add_assoc, Pos.add_assoc, Pos.add_sub,
          Pos.sub_add; auto.
        * transitivity (fg_size + fg_size). 1: apply Pos.sub_decr; auto.
          rewrite <- Pos.add_assoc, (Pos.add_comm 1); apply Pos.lt_add_r.
      + rewrite Pos2Nat.id, fg_gens_size. rewrite !Pos2Nat.inj_sub; auto.
        rewrite Pos2Nat.inj_add, Pos2Nat.inj_1. rewrite Pos2Nat.inj_lt in Heqb. omega.
  Qed.

  Record CosetTable :=
    {
      num_coset_upper_bound: positive;
      num_coset: positive;
      coset_rep: PM.tree (list positive);
      coset_map: PM.tree positive;
      table: PM.tree positive;
    }.

  Definition initCosetTable (upper_bound: positive) :=
    Build_CosetTable
      upper_bound
      1
      (PM.add 1 nil (PM.empty (list positive)))
      (PM.add 1 1 (PM.empty positive))
      (PM.empty positive).

  Definition tableKey (a x: positive) : positive := a * fg_size~0 + x - fg_size~0.

  Definition negRep (x: positive) : positive := fg_size~1 - x.

  Definition defineNewCoset (ct: CosetTable) (a x: positive): CosetTable :=
    let M := num_coset_upper_bound ct in
    let n := num_coset ct in
    if (n =? M)
    then ct
    else let b := n + 1 in
         let p := coset_map ct in
         let newP := PM.add b b p in
         let tab := table ct in
         let newTab := PM.add (tableKey b (negRep x)) a
                              (PM.add (tableKey a x) b tab) in
         let tau := coset_rep ct in
         let aSeq := PM.find a tau in
         match aSeq with
         | None => ct
         | Some taua => let newTau := PM.add b (x :: taua) tau in
                        Build_CosetTable M b newTau newP newTab
         end.

  Fixpoint iterScan (repf: positive -> positive) (t: PM.tree positive)
           (a: positive) (w: list positive) (index: positive) :=
    match w with
    | nil => (a, index)
    | x :: w' => match PM.find (tableKey a (repf x)) t with
                 | None => (a, index)
                 | Some v => iterScan repf t v w' (Pos.succ index)
                 end
    end.

  Definition coset_map_prop (t: PM.tree positive) : Prop :=
    forall i j, PM.find i t == Some j -> j <= i.

  Theorem Pos_lt_well_founded : well_founded Pos.lt.
  Proof.
    red; intro. constructor. intros. rewrite Pos2Nat.inj_lt in H.
    remember (Pos.to_nat a) as n. clear a Heqn. revert y H. induction n; intros.
    - pose proof (Pos2Nat.is_pos y). exfalso; intuition.
    - apply lt_n_Sm_le, le_lt_or_eq in H. destruct H; auto.
      constructor. intros. rewrite Pos2Nat.inj_lt, H in H0. apply IHn. assumption.
  Defined.

  Fixpoint findRHelper (x: positive) (t: PM.tree positive) (step: nat) :=
    match step with
    | O => (x, t)
    | S n => match PM.find x t with
             | None => (x, t)
             | Some p => if (p =? x)
                         then (x, t)
                         else let (p0, t') := findRHelper p t n in
                              (p0, PM.add x p0 t')
             end
    end.

  Definition findRoot (x: positive) (t: PM.tree positive) :=
    findRHelper x t (Pos.to_nat x).

  Definition joinSets (x y: positive) (t r: PM.tree positive) (l: positive) :=
    let (rootX, t1) := findRoot x t in
    let (rootY, t2) := findRoot y t1 in
    if (rootX =? rootY)
    then (t, r, l)
    else let mi := Pos.min rootX rootY in
         let ma := Pos.max rootX rootY in
         let t3 := PM.add ma mi t2 in
         let r' := PM.add l ma r in
         (t3, r', l + 1).

  Instance: EqDec (Alphabet A) eq.
  Proof.
    repeat intro. destruct x, y.
    2, 3: right; intro; inversion H.
    1, 2: destruct (equiv_dec a a0);
      [left; rewrite e | right; intro; apply c; inversion H]; reflexivity.
  Defined.

  Record CosetEnumInput :=
    {
      group_relator: list (Word A);
      subgroup_generator: list (Word A);
    }.

End TODD_COXETER_ALGORITHM.

Section TEST_COSET_ENUM.

  Inductive ThreeT := A | B | C.

  Instance ThreeTEqDec: EqDec ThreeT eq.
  Proof.
    intros x y. destruct x, y; [left | right | right | right | left | right | right | right | left]; intuition; unfold complement; intros; inversion H.
  Defined.

  Instance FG_ThreeT: FiniteGenerators ThreeT.
  Proof.
    apply (Build_FiniteGenerators ThreeT ThreeTEqDec (A :: B :: C :: nil) 3); intros.
    - repeat constructor; intuition; simpl in H; intuition; [inversion H0 | inversion H | inversion H0].
    - destruct x; intuition.
    - simpl. reflexivity.
  Defined.

  Compute fg_size.

  Compute (a2p_helper C (A :: B :: nil) 2).

  Compute (positive_to_alphabet (alphabet_to_positive (intro_inv A))).

  Compute (alphabet_to_positive (positive_to_alphabet 6)).

  Compute fg_size~0.

  Compute (a2p_helper (nth (Init.Nat.pred (Pos.to_nat 3)) fg_gens anyA) fg_gens 1).

End TEST_COSET_ENUM.
