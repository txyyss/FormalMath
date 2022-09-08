Require Import Coq.Arith.Arith_base.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.

Lemma lt_plus_S_l: forall (n m: nat), n < n + S m.
Proof. lia. Qed.

Lemma lt_exists_S_diff: forall (n m: nat), n < m -> exists k, m = n + S k.
Proof. intros. exists (m - S n). lia. Qed.

Ltac decomp_lt_subst' H :=
  match type of H with
  | ?i < ?n =>
    apply lt_exists_S_diff in H; let k := fresh "k" in let ph := fresh "H" in
                                                       destruct H as [k ph]; subst n
  end.

Ltac decomp_lt_subst := match goal with | [H: ?i < ?n |- _ ] => decomp_lt_subst' H end.

Lemma S_plus_neq: forall i m, m + S i <> m.
Proof. lia. Qed.

Lemma neq_nSl_nSm: forall l n m, l <> m -> n + S l <> n + S m.
Proof. lia. Qed.

Lemma subsub_eq: forall m n, n <= m -> m - (m - n) = n.
Proof. lia. Qed.

Lemma lt_sub_1_sub_lt: forall m n, m < n -> n - 1 - m < n.
Proof. lia. Qed.

Lemma lt_sub1_sub1_sub_eq:  forall i n, i < n -> n - 1 - (n - 1 - i) = i.
Proof. lia. Qed.

Lemma sub_lt_mono_l: forall n m p : nat, n < m <= p -> p - m < p - n.
Proof. lia. Qed.

Lemma ltlt_sub1_lt: forall i j m, i < j < m -> m - 1 - j < m - 1 - i < m.
Proof. lia. Qed.

(** The following definition of sigT_relation and related properties
    come from Qinxiang Cao *)

Inductive sigT_relation {I: Type} {A: I -> Type}
          (RA: forall i, relation (A i)): relation (sigT A) :=
| sigT_relation_intro i a b:
  RA i a b -> sigT_relation RA (existT _ i a) (existT _ i b).

Lemma path_sigT {I: Type} {A: I -> Type} (x y: sigT A) (H: x = y):
  {p: projT1 x = projT1 y & eq_rect _ A (projT2 x) _ p = projT2 y}.
Proof. exists (f_equal _ H). destruct H. easy. Qed.

Lemma path_sigT_relation {I: Type} {A: I -> Type}
      (RA: forall i, relation (A i)) (x y: sigT A):
  sigT_relation RA x y <->
  {p: projT1 x = projT1 y & RA _ (eq_rect _ A (projT2 x) _ p) (projT2 y) }.
Proof.
  split; intros.
  - inversion H. simpl in *. exists eq_refl. now simpl.
  - destruct x, y, H. simpl in *. subst. simpl in *. now constructor.
Qed.

#[export] Instance sigT_relation_reflexive {I: Type} {A: I -> Type}
 (RA: forall i, relation (A i)) {_: forall i, Reflexive (RA i)}:
  Reflexive (sigT_relation RA).
Proof. repeat intro. destruct x. constructor. apply H. Qed.

#[export] Instance sigT_relation_symmetric {I: Type} {A: I -> Type}
 (RA: forall i, relation (A i)) {_: forall i, Symmetric (RA i)}:
  Symmetric (sigT_relation RA).
Proof. repeat intro. inversion H0. subst. constructor. now apply H. Qed.

#[export] Instance sigT_relation_transitive {I: Type} {A: I -> Type}
 (RA: forall i, relation (A i)) {_: forall i, Transitive (RA i)}:
  Transitive (sigT_relation RA).
Proof.
  repeat intro. inversion H0; inversion H1. subst. inversion_sigma_on H6. subst i0.
  simpl in *. subst. econstructor. eapply H; eassumption.
Qed.
