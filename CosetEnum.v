Global Generalizable All Variables.
Require Import Coq.Classes.EquivDec.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import FormalMath.Word.
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
    fg_gens_size: length fg_gens = Pos.to_nat fg_size;
  }.

Existing Instance fg_decidable.

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
    (root, fold_left (fun x y => PM.add y root x) (tl (tl trace)) cm).

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

  Definition gen_pos_list (p: positive) := map Pos.of_nat (nat_seq 1 (Pos.to_nat p)).

End GEN_POS_LIST.

Section FIN_GEN_REP.

  Context `{FG: FiniteGenerators A}.

  Lemma fg_gens_not_nil: fg_gens = nil -> False.
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

  Definition alphabet_to_positive (x: Alphabet A) : positive :=
    match x with
    | Pe y => a2p_helper y fg_gens xH
    | Ne y => (xI fg_size) - (a2p_helper y fg_gens xH)
    end.

End FIN_GEN_REP.

Section TODD_COXETER_ALGORITHM.

  Definition CosetTable := PM.tree positive.

  Record CosetEnum :=
    {
      num_coset_upper_bound: positive;
      num_coset: positive;
      coset_map: CosetMap;
      coset_table: CosetTable;
      (* The "coset_table" is actually a map from [1..n] * (Alphabet
      A) to [1..n]. It is flatten into a one-dimensional map by
      mapping the key (a, x) to "a * sizeOfAlphabet + x -
      sizeOfAlphabet". *)
    }.

  Definition init_coset_table (upper_bound: positive) :=
    Build_CosetEnum
      upper_bound
      1
      (PM.add 1 1 (PM.empty _))
      (PM.empty _).

  Context `{FG: FiniteGenerators A}.

  Definition tableKey (a x: positive) : positive := a * fg_size~0 + x - fg_size~0.

  Definition negRep (x: positive) : positive := fg_size~1 - x.

  Definition should_stop (ct: CosetEnum): bool :=
    num_coset_upper_bound ct <=? num_coset ct.

  Definition table_add (a x v: positive) (t: CosetTable): CosetTable :=
    PM.add (tableKey a x) v t.

  Definition table_find (a x: positive) (t: CosetTable): option positive :=
    PM.find (tableKey a x) t.

  Definition table_remove (a x: positive) (t: CosetTable): CosetTable :=
    PM.remove (tableKey a x) t.

  Definition define_new_coset (ct: CosetEnum) (a x: positive): CosetEnum :=
    if should_stop ct
    then ct
    else let b := num_coset ct + 1 in
         let p := coset_map ct in
         let newP := PM.add b b p in
         let tab := coset_table ct in
         let newTab := table_add b (negRep x) a (table_add a x b tab) in
         Build_CosetEnum (num_coset_upper_bound ct) b newP newTab.

  Definition remove_cs (gamma: positive) (pa: list positive * CosetEnum)
             (x: positive) :=
    let (to_be_del, ct) := pa in
    let tbl := coset_table ct in
    match table_find gamma x tbl with
    | None => pa
    | Some dlta => let newTbl := table_remove dlta (negRep x) tbl in
                   let ctm := coset_map ct in
                   let (u, ctm1) := find_rep gamma ctm in
                   let (v, ctm2) := find_rep dlta ctm1 in
                   let (ctml, ntbl) :=
                       match table_find u x newTbl with
                       | Some ux => (merge v ux ctm2 to_be_del, newTbl)
                       | None => match table_find v (negRep x) newTbl with
                                 | Some vx => (merge u vx ctm2 to_be_del, newTbl)
                                 | None => ((ctm2, to_be_del),
                                            table_add v (negRep x) u
                                                      (table_add u x v newTbl))
                                 end
                       end in
                   (snd ctml, Build_CosetEnum (num_coset_upper_bound ct)
                                               (num_coset ct)
                                               (fst ctml) ntbl)
    end.

  Definition all_gen_reps: list positive := gen_pos_list fg_size~0.

  Fixpoint remove_coset (pa: list positive * CosetEnum) (steps: nat): CosetEnum :=
    let (to_be_del, ct) := pa in
    match steps with
    | O => ct
    | S n => match to_be_del with
             | nil => ct
             | gamma :: rest =>
               remove_coset (fold_left (remove_cs gamma) all_gen_reps (rest, ct)) n
             end
    end.

  Definition update_coset_map (ct: CosetEnum) (cm: CosetMap): CosetEnum :=
    Build_CosetEnum (num_coset_upper_bound ct) (num_coset ct) cm (coset_table ct).

  Definition coincidence (a b: positive) (ct: CosetEnum): CosetEnum :=
    let (newCm, to_be_del) := merge a b (coset_map ct) nil in
    remove_coset (to_be_del, update_coset_map ct newCm) (Pos.to_nat (num_coset ct)).

  Fixpoint iter_scan (repf: positive -> positive) (t: CosetTable)
           (a: positive) (w: list positive) :=
    match w with
    | nil => (a, nil)
    | x :: w' => match table_find a (repf x) t with
                 | None => (a, w)
                 | Some v => iter_scan repf t v w'
                 end
    end.

  Definition update_coset_table (ct: CosetEnum) (tbl: CosetTable): CosetEnum :=
    Build_CosetEnum (num_coset_upper_bound ct) (num_coset ct) (coset_map ct) tbl.

  Fixpoint scan_and_fill_loop (a f_init: positive) (w: list positive)
           (ct: CosetEnum) (steps: nat): CosetEnum :=
    match steps with
    | O => ct
    | S n => let (f, new_w) := iter_scan id (coset_table ct) f_init w in
             match new_w with
             | nil => if f =? a
                      then ct
                      else coincidence f a ct
             | xi :: _  => let (b, w2) := iter_scan negRep (coset_table ct)
                                                    a (rev new_w) in
                           match w2 with
                           | nil => coincidence f b ct
                           | xj :: nil =>
                             update_coset_table
                               ct
                               (table_add b (negRep xi) f
                                          (table_add f xi b (coset_table ct)))
                           | _ => let new_ct := define_new_coset ct f xi in
                                  scan_and_fill_loop a f new_w new_ct n
                    end
             end
    end.

  Definition max_steps (ct: CosetEnum): nat :=
    Pos.to_nat (num_coset_upper_bound ct) - Pos.to_nat (num_coset ct).

  Definition is_live (ct: CosetEnum) (a: positive) :=
    match PM.find a (coset_map ct) with
    | None => false
    | Some p => p =? a
    end.

  Definition scan_and_fill (a: positive) (ct: CosetEnum) (w: list positive) :=
    if is_live ct a
    then scan_and_fill_loop a a w ct (max_steps ct)
    else ct.

  Definition define_loop (a: positive) (ct: CosetEnum) (x: positive) : CosetEnum :=
    match table_find a x (coset_table ct) with
    | None => define_new_coset ct a x
    | _ => ct
    end.

  Fixpoint cer_loop (a: positive) (ct: CosetEnum) (group_rep: list (list positive))
           (steps: nat): CosetEnum :=
    match steps with
    | O => ct
    | S n => let ct2 := if is_live ct a
                        then let ct1 := fold_left (scan_and_fill a) group_rep ct in
                             if is_live ct1 a
                             then fold_left (define_loop a) all_gen_reps ct1
                             else ct1
                        else ct in
             cer_loop (Pos.succ a) ct2 group_rep n
    end.

  Definition coset_enumration_r (group_rep sub_grp: list (list positive))
             (upper_bound: positive): CosetEnum :=
    let ct := fold_left (scan_and_fill 1) sub_grp (init_coset_table upper_bound) in
    cer_loop 1 ct group_rep (Pos.to_nat upper_bound).

  Definition replace_loop (a r: positive) (tbl: CosetTable) (x: positive) :=
    match table_find a x tbl with
    | None => tbl
    | Some bb => let b := if bb =? a then r else bb in
                 table_add b (negRep x) r (table_add r x b tbl)
    end.

  Definition compress_loop (tbl: CosetTable) (live_pair: positive * positive) :=
    let (a, r) := live_pair in
    if a =? r
    then tbl
    else fold_left (replace_loop a r) all_gen_reps tbl.

  Definition compress (ct: CosetEnum) :=
    let live_gens := filter (is_live ct) (gen_pos_list (num_coset ct)) in
    let num_live_gens := Pos.of_nat (length live_gens) in
    let new_live_gens := gen_pos_list num_live_gens in
    let live_pairs := combine live_gens new_live_gens in
    let new_table := fold_left compress_loop live_pairs (coset_table ct)in
    let new_cm := fold_left (fun x y => PM.add y y x) new_live_gens (PM.empty _) in
    Build_CosetEnum (num_coset_upper_bound ct) num_live_gens new_cm new_table.

  Definition generator_permutations (ct: CosetEnum) :=
    map (fun x => map (fun a => match table_find a x (coset_table ct) with
                                | None => xH | Some p => p end)
                      (gen_pos_list (num_coset ct))) (gen_pos_list fg_size).

  Definition swap_single (b r x: positive) (tbl: CosetTable) (a: positive) :=
    match table_find a x tbl with
    | None => tbl
    | Some p => if p =? b
                then table_add a x r tbl
                else if p =? r
                     then table_add a x b tbl
                     else tbl
    end.

  Definition switch_loop (b r: positive) (ol: list positive)
             (tbl: CosetTable) (x: positive) :=
    let z := table_find r x tbl in
    let tbl1 := match table_find b x tbl with
                | None => table_remove r x tbl
                | Some p => table_add r x p tbl
                end in
    let tbl2 := match z with
                | None => table_remove b x tbl1
                | Some p => table_add b x p tbl1
                end in
    fold_left (swap_single b r x) ol tbl2.

  Definition switch (tbl: CosetTable) (b r: positive) (ol: list positive) :=
    fold_left (switch_loop b r ol) all_gen_reps tbl.

  Fixpoint standardize_loop (num: positive) (ol tbl_keys: list positive)
             (r: positive) (tbl: CosetTable) :=
    if r =? num
    then tbl
    else match tbl_keys with
         | nil => tbl
         | tk :: rest_tks =>
           match PM.find tk tbl with
           | None => standardize_loop num ol rest_tks r tbl
           | Some b => if r <=? b
                       then let new_tbl := if r <? b
                                           then switch tbl b r ol
                                           else tbl in
                            standardize_loop num ol rest_tks (Pos.succ r) new_tbl
                       else standardize_loop num ol rest_tks r tbl
           end
         end.

  Definition standardize (ct: CosetEnum): CosetEnum :=
    let omega_list := gen_pos_list (num_coset ct) in
    let tbl_keys := flat_map (fun a => (map (tableKey a) all_gen_reps)) omega_list in
    let new_tbl := standardize_loop (num_coset ct)
                                    omega_list tbl_keys 2 (coset_table ct) in
    update_coset_table ct new_tbl.

End TODD_COXETER_ALGORITHM.
