Require Import ZArith.
Require Import List.
Require Import Tarai_Base.
Require Import Denotation.
Require Import Util.

Open Scope Z_scope.

Inductive Le : dZ -> dZ -> Prop :=
| Le_ x y: x <= y -> Le (V x) (V y).

Inductive Tarai_X (k: nat) : VdZ -> Prop :=
| TX head x tail
  (Hmax: forall y, In y head -> Le y (V x))
  (Hlen: length head = k):
  Tarai_X k (head ++ (V x)::tail).

Inductive Tarai_Y (n: nat) (k: nat) : VdZ -> Prop :=
| TY head x tail v
  (Hterm: forall t, VdZ_le t tail -> ntarai n (head++(V x)::t) = V v)
  (Hle: v <= x)
  (Hlen: length head = k):
  Tarai_Y n k (head ++ (V x)::tail).

Section X_functions.
Lemma sigma_X: forall k v, Tarai_X k v -> Tarai_X k (sigma v).
Proof.
  intros.
  destruct H.
  destruct head.
  simpl.
  apply (TX k nil (x - 1) tail).
  intros.
  inversion H.
  auto.
  simpl.
  apply (TX k (dZ_dec d::head) x tail).
  intros.
  simpl in H.
  destruct H.
  assert (Le d (V x)).
  apply Hmax.
  simpl. auto.
  rewrite <- H.
  destruct d.
  inversion H0.
  simpl.
  constructor.
  omega.
  inversion H0.
  apply Hmax.
  simpl. auto.
  simpl in * |- *.
  auto.
Qed.
  
Lemma tau_X: forall k v, Tarai_X (S k) v -> Tarai_X k (tau v).
Proof.
  intros.
  inversion H.
  destruct head.
  simpl in Hlen.
  congruence.
  simpl.
  replace ((head ++ V x :: tail) ++ d :: nil) with (head ++ V x :: (tail ++ d::nil)).
  apply (TX k head x (tail ++ d::nil)).
  intros.
  apply Hmax.
  simpl. auto.
  simpl in Hlen.
  congruence.
  apply (ass_app head (V x::tail) (d::nil)).
Qed.

Lemma ntarai_make_aux_X: forall n m k w v,
  In_n k v (ntarai_make_aux w n) ->
  Tarai_X (m+k)%nat w -> Tarai_X m v.
Proof.
  induction n.
  simpl.
  intros.
  destruct k; contradiction.
  simpl.
  intros.
  destruct k.
  simpl in H.
  rewrite H.
  apply sigma_X.
  replace m with (m + 0)%nat by omega.
  auto.
  simpl in H.
  apply IHn with k (tau w); auto.
  apply tau_X.
  replace (S (m + k)) with (m + S k)%nat by auto.
  auto.
Qed.

Lemma ntarai_make_X: forall n k w v,
  In_n k v (ntarai_make w) ->
  Tarai_X (n+k)%nat w -> Tarai_X n v.
Proof.
  unfold ntarai_make.
  intros.
  apply ntarai_make_aux_X with (length w) k w; auto.
Qed.
End X_functions.

Section Length.
  Open Scope nat_scope.

  Lemma tau_length: forall w,
    length (tau w) = length w.
  Proof.
    destruct w.
    auto.
    simpl.
    rewrite (app_length w (d::nil)).
    simpl.
    omega.
  Qed.

  Lemma ntarai_make_length: forall w,
    length (ntarai_make w) = length w.
  Proof.
    assert (forall n w, length (ntarai_make_aux w n) = n).
    induction n.
    auto.
    simpl.
    intros.
    auto.
    unfold ntarai_make.
    intros.
    auto.
  Qed.

  Lemma X_length: forall k w, Tarai_X k w -> k < length w.
  Proof.
    intros.
    destruct H.
    rewrite (app_length).
    simpl.
    omega.
  Qed.
End Length.

Lemma Y_indep: forall r r' k v, (r <= r')%nat ->
  Tarai_Y r k v -> Tarai_Y r' k v.
Proof.
  intros.
  inversion H0.
  apply (TY r' k head x tail v0); auto.
  intros.
  specialize (Hterm t H2).
  specialize (ntarai_continuous_n r r' (head++V x::t) H).
  intros.
  rewrite Hterm in H3.
  inversion H3.
  auto.
Qed.

Section X_Y.
  Open Scope nat_scope.
  Parameter n: nat.
  Parameter IHn: forall m,
    m < n -> forall v : VdZ, Tarai_X (S m) v ->
    exists n : nat, Tarai_Y n (S m) v.

  Lemma ntarai_make_aux_Y: forall n' m k w v,
    m < n ->
    In_n k v (ntarai_make_aux w n') ->
    Tarai_X (m+k+1) w ->
    exists r,
    Tarai_Y r (S m) v.
  Proof.
    intros.
    apply IHn.
    auto.
    apply ntarai_make_aux_X with n' k w.
    auto.
    replace (S m + k) with (m + k + 1) by omega.
    auto.
  Qed.

  Lemma ntarai_make_Y_aux: forall k w v,
    1 <= k < n ->
    Tarai_X n w ->
    In_n k v (ntarai_make w) ->
    exists r,
    Tarai_Y r (n - k) v.
  Proof.
    intros.
    replace (n - k) with (S (n - k - 1)) by omega.
    apply ntarai_make_aux_Y with (length w) k w.
    omega.
    auto.
    replace (n - k - 1 + k + 1) with n by omega.
    auto.
  Qed.

  Lemma ntarai_make_Y: forall w,
   Tarai_X n w ->
   exists r, forall k v,
      1 <= k < n ->
      In_n k v (ntarai_make w) ->
     Tarai_Y r (n - k) v.
  Proof.
     intros.
     generalize (X_length n w H).
     intros.
     generalize (take_max n (fun k r => k < 1 \/ forall v, In_n k v (ntarai_make w) -> Tarai_Y r (n - k) v)).
     intros.
     destruct H1.
     intros.
     destruct H2; auto.
     right.
     intros.
     apply Y_indep with r; auto.
     destruct k.
     exists 0.
     left; auto.
     intros.
     destruct (In_n_exists (S k) (ntarai_make w)) as [v ?].
     rewrite (ntarai_make_length w).
     omega.
     destruct (ntarai_make_Y_aux (S k) w v) as [r ?]; auto.
     omega.
     exists r.
     right.
     intros.
     rewrite (In_n_unique (S k) (ntarai_make w) v0 v); auto.
     exists x.
     intros.
     destruct (H1 k).
     omega.
     apply False_ind. omega.
     auto.
  Qed.

  Parameter x1: dZ.
  Lemma X_Y_0: exists n1 : nat,
    Tarai_Y n1 (S n) ((V (x1 + 1) :: V x1 :: head) ++ V x :: tail).

  
v : VdZ
H0 : Tarai_X (S n) v
x0 : Z
x1 : Z
head : list dZ
x : Z
tail : list (den Z)
Hmax : forall y : dZ, In y (V x0 :: V x1 :: head) -> Le y (V x)
Hlen : length (V x0 :: V x1 :: head) = S n
H1 : (V x0 :: V x1 :: head) ++ V x :: tail = v
n0 : ~ x0 <= x1
m : nat
IHm : exists n0 : nat,
        Tarai_Y n0 (S n)
          ((V (x1 + 1 + Z_of_nat m) :: V x1 :: head) ++ V x :: tail)
______________________________________(1/1)
exists n1 : nat,
  Tarai_Y n1 (S n)
    ((V (x1 + 1 + Z_of_nat (S m)) :: V x1 :: head) ++ V x :: tail)


Lemma X_impl_Y: forall k v,
  Tarai_X (S k) v -> exists n, Tarai_Y n (S k) v.
Proof.
  intro k. pattern k.
  apply lt_wf_ind.
  intros.
  inversion H0.
  destruct head as [|x0].
  inversion Hlen.
  destruct x0 as [x0|].
  destruct head as [|x1].
  inversion Hlen.
  exists 1%nat.
  apply (TY 1 1 (V x0:: nil) x tail x).
  intros.
  assert (Le (V x0) (V x)).
  apply Hmax.
  red.
  auto.
  inversion H4.
  unfold ntarai.
  simpl.
  destruct (Z_le_dec x0 x); [auto|contradiction].
  omega.
  simpl.
  auto.
  destruct x1 as [x1|].
  destruct (Z_le_dec x0 x1).
  exists 1%nat.
  apply (TY 1 (S n) (V x0::V x1::head) x tail x1).
  intros.
  unfold ntarai.
  simpl.
  destruct (Z_le_dec x0 x1); [auto|contradiction].
  assert (Le (V x1) (V x)).
  apply Hmax.
  simpl.
  auto.
  inversion H2.
  auto.
  auto.

  assert (exists m : nat, x0 - x1 - 1 = Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H2 as [m ?].
  replace x0 with (x1 + 1 + Z_of_nat m) by omega.
  clear H2.

  induction m.
  simpl. replace (x1 + 1 + 0) with (x1 + 1) by omega.
  Focus 2.
  destruct n.
  apply False_ind. omega.

Lemma ntarai_map_X: forall n f v,
  Tarai_X (S n) v ->
  (forall k v, k < n -> Tarai_X k v -> exists r, Tarai_Y r k v) ->
  Tarai_X n (map f (ntarai_make v)).
