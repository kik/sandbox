Require Import Arith.
Require Import Omega.
Require Import List.

Fixpoint In_n {A} n x (v: list A) :=
match v, n with
| nil, _ => False
| y::ys, O => x = y
| y::ys, S m => In_n m x ys
end.

Lemma In_n_exists: forall {A} k (vec: list A),
  k < length vec -> exists v, In_n k v vec.
Proof.
  induction k.
  intros.
  destruct vec.
  inversion H.
  exists a.
  simpl. auto.
  intros.
  destruct vec.
  inversion H.
  simpl in H.
  assert (k < length (vec)) by omega.
  destruct (IHk vec H0) as [v ?].
  exists v.
  simpl. auto.
Qed.

Lemma In_n_unique: forall {A} k (vec: list A) v v',
   In_n k v vec -> In_n k v' vec -> v = v'.
Proof.
   induction k.
   intros.
   destruct vec.
   contradiction.
   unfold In_n in * |-.
   congruence.
   intros.
   destruct vec.
   contradiction.
   simpl in * |-.
   apply IHk with vec; auto.
Qed.

Lemma take_max: forall m (P: nat -> nat -> Prop),
  (forall k r r', r <= r' -> P k r -> P k r') ->
  (forall k, k < m -> exists r, P k r) ->
  exists r, forall k, k < m -> P k r.
Proof.
  intros.
  induction m.
  exists 0.
  intros.
  inversion H1.
  destruct IHm as [r0 ?].
  intros.
  apply H0.
  omega.
  destruct (H0 m) as [r1 ?].
  omega.
  exists (r0 + r1).
  intros.
  destruct (eq_nat_dec k m).
  apply H with r1. omega. rewrite e. auto.
  apply H with r0. omega. apply H1.
  omega.
Qed.
