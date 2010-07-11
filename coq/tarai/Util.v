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

Lemma In_n_map: forall {A B} (f: A->B) k (vec: list A) v v',
  In_n k v vec -> In_n k v' (map f vec) -> f v = v'.
Proof.
  induction k.
  intros.
  destruct vec.
  inversion H.
  simpl in * |-.
  congruence.
  intros.
  destruct vec.
  inversion H.
  simpl in * |-.
  apply IHk with vec; auto.
Qed.

Lemma In_n_map_2: forall {A B} (f: A->B) k (vec: list A) v,
  In_n k v vec -> In_n k (f v) (map f vec).
Proof.
  induction k.
  intros.
  destruct vec.
  inversion H.
  simpl in * |-.
  congruence.
  intros.
  destruct vec.
  inversion H.
  simpl in * |- *.
  auto.
Qed.

Lemma In_n_firstn_1: forall {A} n k (vec: list A) v,
  In_n k v vec -> k < n -> In_n k v (firstn n vec).
Proof.
  induction n.
  intros.
  inversion H0.
  destruct vec.
  destruct k; contradiction.
  destruct k; simpl.
  auto.
  intros.
  apply IHn; auto with arith.
Qed.

Lemma In_n_firstn_2: forall {A} n k (vec: list A) v,
  In_n k v (firstn n vec) -> In_n k v vec.
Proof.
  induction n.
  simpl.
  intros.
  destruct k; contradiction.
  destruct vec; simpl.
  auto.
  destruct k; simpl.
  auto.
  auto.
Qed.

Lemma In_n_length: forall {A} k (vec: list A) v,
  In_n k v vec -> length vec > k.
Proof.
  induction k.
  intros.
  destruct vec.
  inversion H.
  simpl. omega.
  intros.
  destruct vec.
  inversion H.
  simpl in * |- *.
  apply gt_n_S.
  apply IHk with v.
  auto.
Qed.

Lemma firstn_firstn: forall {A} n m (vec: list A), n <= m ->
  firstn n vec = firstn n (firstn m vec).
Proof.
  induction n.
  auto.
  destruct m.
  intros.
  apply False_ind. omega.
  destruct vec.
  auto.
  intros.
  simpl.
  rewrite (IHn m).
  auto.
  auto with arith.
Qed.

Lemma In_n_split: forall {A} k (vec: list A) v,
  In_n k v vec -> firstn k vec ++ v :: skipn (S k) vec = vec.
Proof.
  intros.
  assert (forall k (vec: list A) v, In_n k v vec -> firstn k vec ++ v :: nil = firstn (S k) vec).
  induction k0.
  destruct vec0.
  contradiction.
  simpl in * |- *.
  congruence.
  destruct vec0.
  simpl. contradiction.
  simpl.
  intros.
  rewrite (IHk0 vec0 v0 H0).
  auto.
  replace (firstn k vec ++ v::skipn (S k) vec) with ((firstn k vec ++ v::nil) ++ skipn (S k) vec).
  rewrite (H0 k vec v); auto.
  apply firstn_skipn.
  rewrite <- ass_app.
  rewrite <- app_comm_cons.
  auto.
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
