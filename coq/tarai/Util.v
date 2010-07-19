Require Import Arith.
Require Import Omega.
Require Import List.

Inductive In_n {A: Type} : nat -> A -> list A -> Prop :=
| In_n_O x xs: In_n O x (x::xs)
| In_n_S k y x xs: In_n k y xs -> In_n (S k) y (x::xs).

Hint Constructors In_n: tarai.

Lemma In_n_exists: forall {A} k (vec: list A),
  k < length vec -> exists v, In_n k v vec.
Proof.
  induction k.
  intros.
  destruct vec.
  inversion H.
  exists a.
  auto with tarai.
  intros.
  destruct vec.
  inversion H.
  destruct (IHk vec).
  auto with arith.
  exists x.
  auto with tarai.
Qed.

Lemma In_n_unique: forall {A} k (vec: list A) v v',
   In_n k v vec -> In_n k v' vec -> v = v'.
Proof.
   intros.
   induction H; inversion H0; auto.
Qed.

Lemma In_n_intro: forall {A} k x (vec: list A),
  k < length vec ->
  (forall y, In_n k y vec -> x = y) ->
  In_n k x vec.
Proof.
  intros.
  destruct (In_n_exists k vec); auto.
  rewrite (H0 x0); auto.
Qed.

Hint Resolve @In_n_intro: tarai.

Lemma In_n_O_eq: forall {A} {vec: list A} {x y},
  In_n O x (y::vec) -> x = y.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Hint Resolve @In_n_O_eq: tarai.

Lemma In_n_S_inv: forall {A} k (vec: list A) x y,
  In_n (S k) x (y::vec) -> In_n k x vec.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Hint Resolve @In_n_S_inv: tarai.

Lemma In_n_length: forall {A} k (vec: list A) v,
  In_n k v vec -> k < length vec.
Proof.
  intros.
  induction H; simpl; auto with arith.
Qed.

Lemma In_n_map_eq: forall {A B} (f: A->B) k (vec: list A) v v',
  In_n k v vec -> In_n k v' (map f vec) -> f v = v'.
Proof.
  intros.
  induction H; inversion H0; auto.
Qed.

Lemma In_n_map: forall {A B} (f: A->B) k (vec: list A) v,
  In_n k v vec -> In_n k (f v) (map f vec).
Proof.
  intros.
  apply In_n_intro.
  rewrite map_length.
  apply In_n_length with v. auto.
  intros.
  apply In_n_map_eq with k vec; auto.
Qed.

Lemma In_n_unmap:  forall {A B} (f: A->B) k (vec: list A) v,
  In_n k v (map f vec) -> exists v', f v' = v /\ In_n k v' vec.
Proof.
  intros.
  destruct (In_n_exists k vec) as [v' ?].
  apply In_n_length in H.
  rewrite map_length in H.
  auto.
  exists v'.
  constructor; auto.
  apply In_n_map_eq with k vec; auto.
Qed.

Lemma In_n_app: forall {A} (v w: list A) k x,
  In_n k x v -> In_n k x (v++w).
Proof.
  intros.
  induction H; rewrite <- app_comm_cons; auto with tarai.
Qed.

Lemma In_n_unapp: forall {A} (v w: list A) k x,
  In_n k x (v ++ w) -> k < length v -> In_n k x v.
Proof.
  induction v.
  intros.
  inversion H0.
  intros.
  destruct k.
  inversion H.
  auto with tarai.
  constructor.
  inversion H.
  apply IHv with w; auto with tarai arith.
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
