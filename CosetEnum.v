Require Import Coq.Classes.EquivDec.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Program.
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

Section COSET_MAP.

  Definition CosetMap := PM.tree positive.

  Fixpoint ctr_helper (x: positive) (cm: CosetMap) (steps: nat): list positive :=
    match steps with
    | O => nil (* It will not happen. *)
    | S n => match PM.find x cm with
             | None => nil (* It will not happen. *)
             | Some p => if (p =? x)
                         then x :: nil
                         else x :: ctr_helper p cm n
             end
    end.

  Definition cm_trace_root (x: positive) (cm: CosetMap) :=
    rev (ctr_helper x cm (Pos.to_nat x)).

  Definition test_map :=
    fold_right (fun x t => PM.add (fst x) (snd x) t) (PM.empty _)
               [(1, 1); (2, 1); (3, 2); (4, 2); (5, 4)].

  Compute (cm_trace_root 5 test_map).

  Definition find_rep (x: positive) (cm: CosetMap): (positive * CosetMap) :=
    let trace := cm_trace_root x cm in
    let root := hd xH trace in
    (root, fold_right (fun x => PM.add x root) cm (tl (tl trace))).

  Compute (PM.find 4 (snd (find_rep 1 test_map))).

  Definition merge (x y: positive) (cm: CosetMap) (to_be_del: list positive):
    (CosetMap * list positive) :=
    let (x_root, cm1) := find_rep x cm in
    let (y_root, cm2) := find_rep y cm1 in
    if x_root =? y_root
    then (cm2, to_be_del)
    else let min_root := Pos.min x_root y_root in
         let max_root := Pos.max x_root y_root in
         (PM.add max_root min_root cm2, max_root :: to_be_del).

End COSET_MAP.

Section GEN_POS_LIST.

  Fixpoint nat_seq (s: nat) (total: nat): list nat :=
    match total with
    | O => nil
    | S n => s :: nat_seq (S s) n
    end.

  Lemma nat_seq_length: forall s n, length (nat_seq s n) == n.
  Proof.
    intros. revert s. induction n; intros; simpl; [|rewrite IHn]; reflexivity.
  Qed.

  Lemma nat_seq_S: forall i num, nat_seq i (S num) == nat_seq i num ++ [(num + i)%nat].
  Proof.
    intros. revert i. induction num; intros. 1: simpl; reflexivity. remember (S num).
    simpl. rewrite (IHnum (S i)). subst. simpl. repeat f_equal. omega.
  Qed.

  Lemma nat_seq_In_iff: forall s n i, In i (nat_seq s n) <-> (s <= i < s + n)%nat.
  Proof. intros. revert s. induction n; intros; simpl; [|rewrite IHn]; omega. Qed.

  Lemma nat_seq_NoDup: forall s n, NoDup (nat_seq s n).
  Proof.
    intros. revert s. induction n; intros; simpl; constructor. 2: apply IHn.
    intro. rewrite nat_seq_In_iff in H. omega.
  Qed.

  Lemma nat_seq_nth: forall s num n a, (n < num)%nat ->
                                       nth n (nat_seq s num) a == (s + n)%nat.
  Proof.
    intros. revert s n H. induction num; intros. 1: exfalso; omega. simpl. destruct n.
    1: omega. specialize (IHnum (S s) n).
    replace (s + S n)%nat with (S s + n)%nat by omega.
    rewrite IHnum; [reflexivity | omega].
  Qed.

  Lemma nat_seq_app: forall s n m,
      nat_seq s (n + m) == nat_seq s n ++ nat_seq (s + n) m.
  Proof.
    intros. revert s; induction n; simpl; intros.
    - rewrite Nat.add_0_r. reflexivity.
    - f_equal. rewrite IHn. replace (S s + n)%nat with (s + S n)%nat by omega.
      reflexivity.
  Qed.

  Compute (nat_seq 1 5).

  Definition gen_pos_list (p: positive) := map Pos.of_nat (nat_seq 1 (Pos.to_nat p)).

End GEN_POS_LIST.

Section FIN_GEN_REP.

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
    then Pe (nth (pred (Pos.to_nat n)) fg_gens anyA)
    else Ne (nth (pred (Pos.to_nat (n - fg_size))) (rev fg_gens) anyA).

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
    | Pe y => a2p_helper y fg_gens xH
    | Ne y => (xI fg_size) - (a2p_helper y fg_gens xH)
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

  Record CosetEnumInput :=
    {
      group_relator: list (Word A);
      subgroup_generator: list (Word A);
    }.

  Instance: EqDec (Alphabet A) eq.
  Proof.
    repeat intro. destruct x, y.
    2, 3: right; intro; inversion H.
    1, 2: destruct (equiv_dec a a0);
      [left; rewrite e | right; intro; apply c; inversion H]; reflexivity.
  Defined.

End FIN_GEN_REP.

Section TODD_COXETER_ALGORITHM.

  Record CosetTable :=
    {
      num_coset_upper_bound: positive;
      num_coset: positive;
      coset_rep: PM.tree (list positive);
      coset_map: CosetMap;
      table: PM.tree positive;
      (* The "table" is actually a map from [1..n] * (Alphabet A) to
      [1..n]. It is flatten into a one-dimensional map by mapping the
      key (a, x) to "a * sizeOfAlphabet + x - sizeOfAlphabet". *)
    }.

  Definition init_coset_table (upper_bound: positive) :=
    Build_CosetTable
      upper_bound
      1
      (PM.add 1 nil (PM.empty _))
      (PM.add 1 1 (PM.empty _))
      (PM.empty _).

  Context `{FG: FiniteGenerators A}.

  Definition tableKey (a x: positive) : positive := a * fg_size~0 + x - fg_size~0.

  Definition negRep (x: positive) : positive := fg_size~1 - x.

  Definition should_stop (ct: CosetTable): bool :=
    num_coset_upper_bound ct <=? num_coset ct.

  Definition define_new_coset (ct: CosetTable) (a x: positive): CosetTable :=
    if should_stop ct
    then ct
    else let b := num_coset ct + 1 in
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
                        Build_CosetTable (num_coset_upper_bound ct)
                                         b newTau newP newTab
         end.

  Definition remove_cs (gamma: positive) (x: positive)
             (pa: list positive * CosetTable) :=
    let (to_be_del, ct) := pa in
    let tbl := table ct in
    match PM.find (tableKey gamma x) tbl with
    | None => pa
    | Some dlta => let newTbl := PM.remove (tableKey dlta (negRep x)) tbl in
                   let ctm := coset_map ct in
                   let (u, ctm1) := find_rep gamma ctm in
                   let (v, ctm2) := find_rep dlta ctm1 in
                   let (ctml, ntbl) :=
                       match PM.find (tableKey u x) newTbl with
                       | Some ux => (merge v ux ctm2 to_be_del, newTbl)
                       | None => match PM.find (tableKey v (negRep x)) newTbl with
                                 | Some vx => (merge u vx ctm2 to_be_del, newTbl)
                                 | None => ((ctm2, to_be_del),
                                            PM.add (tableKey v (negRep x)) u
                                                   (PM.add (tableKey u x) v newTbl))
                                 end
                       end in
                   (snd ctml, Build_CosetTable (num_coset_upper_bound ct)
                                               (num_coset ct)
                                               (coset_rep ct)
                                               (fst ctml) ntbl)
    end.

  Fixpoint remove_coset (pa: list positive * CosetTable) (steps: nat): CosetTable :=
    let (to_be_del, ct) := pa in
    match steps with
    | O => ct
    | S n => match to_be_del with
             | nil => ct
             | gamma :: rest =>
               remove_coset (fold_right (remove_cs gamma) (rest, ct)
                                        (gen_pos_list fg_size~0)) n
             end
    end.

  Definition update_coset_map (ct: CosetTable) (cm: CosetMap): CosetTable :=
    Build_CosetTable (num_coset_upper_bound ct) (num_coset ct)
                     (coset_rep ct) cm (table ct).

  Definition coincidence (a b: positive) (ct: CosetTable): CosetTable :=
    let (newCm, to_be_del) := merge a b (coset_map ct) nil in
    remove_coset (to_be_del, update_coset_map ct newCm) (Pos.to_nat (num_coset ct)).

  Fixpoint iter_scan (repf: positive -> positive) (t: PM.tree positive)
           (a: positive) (w: list positive) :=
    match w with
    | nil => (a, nil)
    | x :: w' => match PM.find (tableKey a (repf x)) t with
                 | None => (a, w)
                 | Some v => iter_scan repf t v w'
                 end
    end.

  Compute (skipn 1 [1;2;3;4;5]).

  Definition update_coset_table (ct: CosetTable) (tbl: PM.tree positive): CosetTable :=
    Build_CosetTable (num_coset_upper_bound ct) (num_coset ct)
                     (coset_rep ct) (coset_map ct) tbl.

  Fixpoint scan_and_fill_loop (a f_init: positive) (w: list positive)
           (ct: CosetTable) (steps: nat): CosetTable :=
    match steps with
    | O => ct
    | S n => let (f, new_w) := iter_scan id (table ct) f_init w in
             match new_w with
             | nil => if f =? a
                      then ct
                      else coincidence f a ct
             | xi :: _  => let (b, w2) := iter_scan negRep (table ct) a (rev new_w) in
                           match w2 with
                           | nil => coincidence f b ct
                           | xj :: nil => update_coset_table
                                            ct
                                            (PM.add (tableKey b (negRep xi)) f
                                                    (PM.add (tableKey f xi) b
                                                            (table ct)))
                           | _ => let new_ct := define_new_coset ct f xi in
                                  scan_and_fill_loop a f new_w new_ct n
                    end
             end
    end.

  Definition max_steps (ct: CosetTable): nat :=
    Pos.to_nat (num_coset_upper_bound ct) - Pos.to_nat (num_coset ct).

  Definition is_live (a: positive) (ct: CosetTable) :=
    match PM.find a (coset_map ct) with
    | None => false
    | Some p => p =? a
    end.

  Definition scan_and_fill (a: positive) (w: list positive) (ct: CosetTable) :=
    if is_live a ct
    then scan_and_fill_loop a a w ct (max_steps ct)
    else ct.

  Definition define_loop (a x: positive) (ct: CosetTable): CosetTable :=
    match PM.find (tableKey a x) (table ct) with
    | None => define_new_coset ct a x
    | _ => ct
    end.

  Fixpoint cer_loop (a: positive) (ct: CosetTable) (group_rep: list (list positive))
           (steps: nat): CosetTable :=
    match steps with
    | O => ct
    | S n => let ct2 := if is_live a ct
                        then let ct1 := fold_right (scan_and_fill a) ct group_rep in
                             if is_live a ct1
                             then fold_right (define_loop a) ct1
                                             (gen_pos_list fg_size~0)
                             else ct1
                        else ct in
             cer_loop (Pos.succ a) ct2 group_rep n
    end.

  Definition coset_enumration_r (group_rep sub_grp: list (list positive))
             (upper_bound: positive): CosetTable :=
    let ct := fold_right (scan_and_fill 1) (init_coset_table upper_bound) sub_grp in
    cer_loop 1 ct group_rep (Pos.to_nat upper_bound).

  Definition print_coset_table (ct: CosetTable) :=
    map (fun x => map (fun y => PM.find (tableKey x y) (table ct))
                      (gen_pos_list fg_size~0))
        (gen_pos_list (num_coset ct)).

  Definition print_coset_map (ct: CosetTable) :=
    map (fun x => (x, PM.find x (coset_map ct))) (gen_pos_list (num_coset ct)).

  Definition good_pair (x: positive * option positive) :=
    let (a, b) := x in
    match b with
    | None => false
    | Some c => a =? c
    end.

  Fixpoint good_row (l: list (option positive)) :=
    match l with
    | nil => true
    | p :: l => match p with
                | None => false
                | Some _ => good_row l
                end
    end.

End TODD_COXETER_ALGORITHM.

Section TEST_COSET_ENUM.

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

  Compute (fg_size~0).

  Compute (map positive_to_alphabet [1; 2; 3; 4]).

  Definition gen_grp_a := [[Pe X; Pe X; Pe X];
                             [Pe Y; Pe Y; Pe Y];
                             [Ne X; Ne Y; Pe X; Pe Y]].

  Compute (map (map alphabet_to_positive) gen_grp_a).

  Definition gen_grp := [[1; 1; 1]; [2; 2; 2]; [4; 3; 1; 2]].

  Definition gen_sub: list (list positive) := [[]].

  Definition gen_ct := coset_enumration_r gen_grp gen_sub 20.

  Compute (rev gen_grp).

  Compute (print_coset_table gen_ct).

  Compute (print_coset_map gen_ct).

  Definition gen_grp_b := [[Pe X; Pe Y; Pe X; Pe Y; Ne X; Ne X; Ne X];
                             [Pe X; Pe X; Pe X; Ne Y; Ne Y; Ne Y]].

  Compute (map (map alphabet_to_positive) gen_grp_b).

  Definition gen_grp2 := [[1; 2; 1; 2; 4; 4; 4]; [1; 1; 1; 3; 3; 3]].

  Definition ct2 := coset_enumration_r gen_grp2 nil 150.

  Compute (filter good_row (print_coset_table ct2)).

  Compute (length (filter good_pair (print_coset_map ct2))).

End TEST_COSET_ENUM.
