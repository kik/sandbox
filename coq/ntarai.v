Require Import ZArith.

Open Scope Z_scope.

Inductive denote (A: Type) : Type :=
| V : A -> denote A
| B : denote A.

Implicit Arguments V [A].
Implicit Arguments B [A].

Definition Z' := denote Z.

Fixpoint Yn {A: Type} n (init: A) (recur: A -> A) : A :=
match n with
| O => init
| S n' => recur (Yn n' init recur)
end.

Definition minus_1 (x: Z') : Z' :=
match x with
| V x => V (x - 1)
| B => B
end.

Definition ntarai5_init (a b c d e: Z') : Z' := B.
Definition ntarai5_rec f (a b c d e: Z') : Z' :=
match a, b with
| V av, V bv =>
  if Z_le_dec av bv then b else
  f (f (minus_1 a) b c d e)
    (f (minus_1 b) c d e a)
    (f (minus_1 c) d e a b)
    (f (minus_1 d) e a b c)
    (f (minus_1 e) a b c d)
| _, _ => B 
end.

Definition ntarai5 n := Yn n ntarai5_init  ntarai5_rec.

Inductive Tarai_value:
     nat -> Z' -> Z' -> Z' -> Z' -> Z' -> Z' -> Prop :=
| Tarai_value_le n a b c d e
     (Hle: a <= b):
     Tarai_value (S n) (V a) (V b) c d e (V b)
| Tarai_value_gt n a b c d e v1 v2 v3 v4 v5 vr
     (Hnle: ~a <= b)
     (Hv1: Tarai_value n (minus_1 (V a)) (V b) c d e v1)
     (Hv2: Tarai_value n (minus_1 (V b)) c d e (V a) v2)
     (Hv3: Tarai_value n (minus_1 c) d e (V a) (V b) v3)
     (Hv4: Tarai_value n (minus_1 d) e (V a) (V b) c v4)
     (Hv5: Tarai_value n (minus_1 e) (V a) (V b) c d v5)
     (Hvr: Tarai_value n v1 v2 v3 v4 v5 vr):
     Tarai_value (S n) (V a) (V b) c d e vr
| Tarai_value_none_1 a b c d e:
     Tarai_value O a b c d e B
| Tarai_value_none_2 n b c d e:
     Tarai_value n B b c d e B
| Tarai_value_none_3 n a c d e:
     Tarai_value n a B c d e B.

Lemma lem_step_l: forall n a b c d e v,
   (if Z_le_dec a b then V b else
    (ntarai5 n (ntarai5 n (V (a - 1)) (V b) c d e)
                  (ntarai5 n (V (b - 1)) c d e (V a))
                  (ntarai5 n (minus_1 c) d e (V a) (V b))
                  (ntarai5 n (minus_1 d) e (V a) (V b) c)
                  (ntarai5 n (minus_1 e) (V a) (V b) c d))) = v ->
   ntarai5 (S n) (V a) (V b) c d e = v.
Proof.
  intros.
  exact H.
Qed.

Lemma lem_step_r: forall n a b c d e v,
   v =
   (if Z_le_dec a b then V b else
    (ntarai5 n (ntarai5 n (V (a - 1)) (V b) c d e)
                  (ntarai5 n (V (b - 1)) c d e (V a))
                  (ntarai5 n (minus_1 c) d e (V a) (V b))
                  (ntarai5 n (minus_1 d) e (V a) (V b) c)
                  (ntarai5 n (minus_1 e) (V a) (V b) c d))) ->
   v = ntarai5 (S n) (V a) (V b) c d e.
Proof.
  intros.
  exact H.
Qed.

Lemma Tarai_value_l: forall n a b c d e v,
  Tarai_value n a b c d e v -> ntarai5 n a b c d e = v.
Proof.
  intros.
  induction H.
  apply lem_step_l.
  destruct (Z_le_dec a b); [auto|contradiction].
  apply lem_step_l.
  destruct (Z_le_dec a b); [contradiction|].
  simpl in * |-.
  congruence.
  auto.
  destruct n; auto.
  destruct n; destruct a; auto.
Qed.

Lemma Tarai_value_r: forall n a b c d e v,
  ntarai5 n a b c d e = v -> Tarai_value n a b c d e v.
Proof.
  induction n.
  unfold ntarai5. simpl. unfold ntarai5_init.
  intros.
  rewrite <- H.
  constructor.
  intros.
  destruct a as [a|].
  destruct b as [b|].
  destruct (Z_le_dec a b).
  unfold ntarai5 in H.
  simpl in H.
  destruct (Z_le_dec a b); [auto|contradiction].
  rewrite <- H.
  apply Tarai_value_le. auto.
  eapply Tarai_value_gt.
  auto.
  apply IHn. reflexivity.
  apply IHn. reflexivity.
  apply IHn. reflexivity.
  apply IHn. reflexivity.
  apply IHn. reflexivity.
  apply IHn.
  unfold ntarai5 in H. simpl in H.
  destruct (Z_le_dec a b); [contradiction|].
  exact H.
  unfold ntarai5 in H. simpl in H. rewrite <- H.
  constructor.
  unfold ntarai5 in H. simpl in H. rewrite <- H.
  constructor.
Qed.

Definition Z'_le (x y: Z') := x = y \/ x = B.
Definition Z5'_le (a b c d e a' b' c' d' e': Z') :=
  Z'_le a a' /\  Z'_le b b' /\  Z'_le c c' /\  Z'_le d d' /\  Z'_le e e' .

Lemma lem_contin: forall n a b c d e v a' b' c' d' e' v',
  Z5'_le a b c d e a' b' c' d' e' ->
  Tarai_value n a b c d e v ->
  Tarai_value n a' b' c' d' e' v' -> Z'_le v v'.
Proof.
  induction n.
  intros. inversion H0.
    right. auto.
    right. auto.
    right. auto.
  intros.
  destruct H as [Ha[Hb[Hc[Hd He]]]].
  destruct a as [a|].
  destruct b as [b|].
  destruct Ha as [Ha|?]; [|congruence].
  destruct Hb as [Hb|?]; [|congruence].
  rewrite <- Ha in H1.
  rewrite <- Hb in H1.
  inversion H0; inversion H1; try contradiction.
  left. auto.
  apply (IHn v1 v2 v3 v4 v5 v v0 v6 v7 v8 v9 v'); auto.
  red.
  assert (forall x, Z'_le x x). left. auto.
  assert (forall x y, Z'_le x y -> Z'_le (minus_1 x) (minus_1 y)).
    intros.
    destruct H16.
    rewrite H16.
    auto.
    rewrite H16.
    right.
    auto.
  constructor.
  apply (IHn (minus_1 (V a)) (V b) c d e v1
                  (minus_1 (V a)) (V b) c' d' e' v0); auto.
  red. auto.
  constructor.
  apply (IHn (minus_1 (V b)) c d e (V a) v2
                  (minus_1 (V b)) c' d' e' (V a) v6); auto.
  red. auto.
  constructor.
  apply (IHn (minus_1 c) d e (V a) (V b) v3
                  (minus_1 c') d' e' (V a) (V b) v7); auto.
  red. auto.
  constructor.
  apply (IHn (minus_1 d) e (V a) (V b) c v4
                  (minus_1 d') e' (V a) (V b) c' v8); auto.
  red. auto.
  apply (IHn (minus_1 e) (V a) (V b) c d v5
                  (minus_1 e') (V a) (V b) c' d' v9); auto.
  red. auto.

  inversion H0. right. auto.
  inversion H0. right. auto.
  right. auto.
Qed.  

Inductive Tarai_Y (n: nat):
     Z' -> Z' -> Z' -> Z' -> Z' -> Z -> Prop :=
| Tarai_Y_2 a b v
     (Hterm: ntarai5 n (V a) (V b) B B B = (V v))
     (Hle: v <= b):
     Tarai_Y n (V a) (V b) B B B v
| Tarai_Y_3 a b c v
     (Hterm: ntarai5 n (V a) (V b) (V c) B B = (V v))
     (Hle: v <= c):
     Tarai_Y n (V a) (V b) (V c) B B v
| Tarai_Y_4 a b c d v
     (Hterm: ntarai5 n (V a) (V b) (V c) (V d) B = (V v))
     (Hle: v <= d):
     Tarai_Y n (V a) (V b) (V c) (V d) B v.
(*
| Tarai_Y_1n a b c d e v:
     Tarai_Y n B b c d e v -> Tarai_Y n a b c d e v
| Tarai_Y_2n a b c d e v:
     Tarai_Y n a B c d e v -> Tarai_Y n a b c d e v
| Tarai_Y_3n a b c d e v:
     Tarai_Y n a b B d e v -> Tarai_Y n a b c d e v
| Tarai_Y_4n a b c d e v:
     Tarai_Y n a b c B e v -> Tarai_Y n a b c d e v
| Tarai_Y_5n a b c d e v:
     Tarai_Y n a b c d B v -> Tarai_Y n a b c d e v.*)


Proof.
  induction n.
  intros.
  destruct H as [?|[?|[?|[?|?]]]]; inversion H.
  intros.
  generalize (IHn (minus_1 a) b c d e).
  generalize (IHn (minus_1 b) c d e a).
  generalize (IHn (minus_1 c) d e a b).
  generalize (IHn (minus_1 d) e a b c).
  generalize (IHn (minus_1 e) a b c d).
  generalize (IHn (ntarai5 n (minus_1 a) b c d e)
                       (ntarai5 n (minus_1 b) c d e a)
                       (ntarai5 n (minus_1 c) d e a b)
                       (ntarai5 n (minus_1 d) e a b c)
                       (ntarai5 n (minus_1 e) a b c d)).
  intros.
  destruct a as [a|]; destruct b as [b|].
  destruct H as [?|[?|[?|[?|?]]]]; try inversion H.
     apply lem_step_l.
     apply lem_step_r.
     simpl in H5.
     destruct (ntarai5 n (V (a - 1)) (V b) B d e) as [v0|].
     rewrite (H5 v0); auto. clear H5.
     simpl in H4.
     destruct (ntarai5 n (V (b - 1)) B d e (V a)) as [v1|].
     rewrite (H4 v1); auto. clear H4.

  destruct c as [c|]; destruct d as [d|]; destruct e as [e|].
  intros.
  destruct H as [?|[?|[?|[?|?]]]]; try inversion H.

    destruct a as [a|]; destruct b as [b|];
    try inversion H;
    apply lem_step_l;
    apply lem_step_r.
*)

Lemma lem_1n: forall n a b c d e v,
  ntarai5 n a B B B B = V v -> ntarai5 n a b c d e = V v.
Proof.
  intros.
  unfold ntarai5 in H.
  destruct n; destruct a; inversion H.
Qed.

Lemma lem_2n: forall n a b c d e v,
  ntarai5 n a b B B B = V v -> ntarai5 n a b c d e = V v.
Proof.
  intros.
  destruct b.
  unfold ntarai5 in H.
  destruct n.
  inversion H.
  destruct a; inversion H.
Qed.

Lemma lem_3n: forall n a b c d e v,
  ntarai5 n a b B d e = V v -> ntarai5 n a b c d e = V v.
Proof.
  induction n.
    intros.
    inversion H.

    intros.
    destruct a; destruct b; try inversion H.
    apply lem_step_l.
    apply lem_step_r.
    rewrite IHn


Lemma lem_1: forall a b, a <= b ->
   exists n, exists v, Tarai_Y n (V a) (V b) B B B v.
Proof.
   intros.
   exists 1%nat. exists b.
   constructor 1.
   apply lem_step.
   destruct (Z_le_dec a b).
   auto. contradiction.
   omega.
Qed.

Lemma lem_2: forall a b c, a <= c -> b <= c ->
   exists n, exists v, Tarai_Y n (V a) (V b) (V c) B B v.
Proof.
   intros.
   destruct (Z_le_dec a b).
   destruct (lem_1 a b) as [n [v ?]]; auto.
   inversion H1.
   auto using lem_1.
   assert (exists m : nat, a - b - 1 = Z_of_nat m). 
   apply Z_of_nat_complete.
   omega. 
   destruct H1 as [m ?].
   replace a with (b + 1 + Z_of_nat m) by omega.
   induction m.
   exists 2%nat.
   exists c.
   simpl.
   replace (b + 1 + 0) with (b + 1) by omega.
   apply Tarai_Y_4n.
   apply Tarai_Y_5n.
   apply Tarai_Y_3.
   apply lem_step.
   replace (b + 1 - 1) with b by omega.
   destruct (lem_1 b b B B B) as [n0 [v ?]]. omega.
   unfold ntarai5.
   simpl.
   destruct (Z_le_dec (b + 1 + 0) b).
   apply False_ind. omega.

Inductive Tarai_value:
     nat -> Z' -> Z' -> Z' -> Z' -> Z' -> Z -> Prop :=
| Tarai_1 n a b
     (Hmax1: a <= b):
     Tarai_value (S n) (V a) (V b) B B B b
| Tarai_2 n a b c v1 v2 v3 vr
     (Hmax1: a <= c)
     (Hmax2: b <= c)
     (Hrec1: Tarai_value n (V (a-1)) (V b) (V c) B B v1)
     (Hrec2: Tarai_value n (V (b-1)) (V c) B B (V a) v2)
     (Hrec3: Tarai_value n (V (c-1)) B B (V a) (V b) v3)
     (Hrec:  Tarai_value n (V v1) (V v2) (V v3) B B vr):
     Tarai_value (S n) (V a) (V b) (V c) B B vr
| Tarai_3 n a b c d v1 v2 v3 v4 vr (Hgt: a > b)
     (Hmax1: a <= d)
     (Hmax2: b <= d)
     (Hmax3: c <= d)
     (Hrec1: Tarai_value n (V (a-1)) (V b) (V c) (V d) B v1)
     (Hrec2: Tarai_value n (V (b-1)) (V c) (V d) B (V a) v2)
     (Hrec3: Tarai_value n (V (c-1)) (V d) B (V a) (V b) v3)
     (Hrec4: Tarai_value n (V (d-1)) B (V a) (V b) (V c) v4)
     (Hrec:  Tarai_value n (V v1) (V v2) (V v3) (V v4) B vr):
     Tarai_value (S n) (V a) (V b) (V c) (V d) B vr.

Lemma Tarai_1_term: forall n a b v, Tarai_value n (V a) (V b) B B B v ->
  ntarai5 n (V a) (V b) B B B = V v.
Proof.
  intros.
  inversion H.
  unfold ntarai5, Yn, ntarai5_rec.
  destruct (Z_le_dec a v).
  auto.
  cut False. intro. contradiction.
  omega.
Qed.

Lemma lem_safficiency:
  forall n a b c v, Tarai_value n a b c v -> ntarai3 n (V a) (V b) (V c) = V v.
Proof.
  intros.
  induction H.
    destruct n;
    simpl;
    destruct (Z_le_dec a b); auto; try contradiction.

    simpl.
    rewrite IHTarai_value1.
    rewrite IHTarai_value2.
    destruct (Z_le_dec a b).
    absurd (a > b); omega.
    destruct n; simpl; destruct (Z_le_dec v1 v2); auto; contradiction.

    simpl.    
    rewrite IHTarai_value1.
    rewrite IHTarai_value2.
    rewrite IHTarai_value3.
    rewrite IHTarai_value4.
    destruct (Z_le_dec a b); auto; contradiction.
Qed.

Lemma lem_necessity:
  forall n a b c v, ntarai3 n (V a) (V b) (V c) = V v -> Tarai_value n a b c v.
Proof.
  induction n.
  intros.
  simpl in H.
  destruct (Z_le_dec a b).
  inversion H.
  apply Tarai_a_le_b.
  congruence.
  inversion H.
  simpl.
  intros.
  destruct (Z_le_dec a b).
  inversion H.
  apply Tarai_a_le_b.
  congruence.
  generalize (IHn (a - 1) b c).
  generalize (IHn (b - 1) c a).
  generalize (IHn (c - 1) a b).
  intros.
  destruct n.
  destruct (ntarai3 0 (V (a - 1)) (V b) (V c)) as [v1|]; [| inversion H].
  destruct (ntarai3 0 (V (b - 1)) (V c) (V a)) as [v2|]; [| inversion H].
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply Tarai_a_gt_b_1 with v1; auto.
  omega.
  congruence.
  inversion H.
  destruct (ntarai3 (S n) (V (a - 1)) (V b) (V c)) as [v1|]; [| inversion H].
  destruct (ntarai3 (S n) (V (b - 1)) (V c) (V a)) as [v2|]; [| inversion H].
  destruct (ntarai3 (S n) (V (c - 1)) (V a) (V b)) as [v3|].
  generalize (IHn v1 v2 v3 v H).
  intro.
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply Tarai_a_gt_b_1 with v1; auto.
  omega.
  congruence.
  apply Tarai_a_gt_b_2 with v1 v2 v3; auto.
  omega.
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply Tarai_a_gt_b_1 with v1; auto.
  omega. congruence.
  inversion H.
Qed.

Lemma lem_n_indep : forall n m a b c v,
    Tarai_value n a b c v -> Tarai_value (n + m) a b c v.
Proof.
  induction n.
  intros.
  inversion H.
  apply Tarai_a_le_b; auto.
  intros.
  inversion H.
     apply Tarai_a_le_b; auto.
     replace (S n + m)%nat with (S (n + m)) by auto.
     apply Tarai_a_gt_b_1 with v1; auto.
     replace (S n + m)%nat with (S (n + m)) by auto.
     apply Tarai_a_gt_b_2 with v1 v2 v3; auto.
Qed.

Lemma lem1_a_gt_b_le_c : forall b c m, b <= c ->
  exists n, Tarai_value n (b + Z_of_nat(S m)) b c c.
Proof.
  induction m. 
  intros.
  exists 1%nat.
  replace (Z_of_nat 1) with 1 by auto.

  apply Tarai_a_gt_b_1 with b; auto.
  omega.
  apply Tarai_a_le_b; omega.
  apply Tarai_a_le_b; omega.

  intros.
  destruct (IHm H) as [n' Hn'].
  exists (S n').

  apply Tarai_a_gt_b_1 with c; auto.
  rewrite inj_S. omega.
  omega.
  rewrite inj_S.
  replace (b + Zsucc (Z_of_nat (S m)) - 1) with (b + Z_of_nat (S m)) by omega.
  auto.

  apply Tarai_a_le_b; omega.
Qed. 

Lemma lem_a_gt_b_le_c : forall a b c,  a > b -> b <= c -> 
  exists n : nat, Tarai_value n a b c c.
Proof.
  intros. 

  assert (exists m : nat, a-1-b=Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H1 as [m ?]. 

  replace a with (b + Zsucc (Z_of_nat m)) by omega.
  rewrite <- inj_S.
  auto using lem1_a_gt_b_le_c. 
Qed. 

Lemma lem1_a_gt_b_gt_c : forall b c,  b > c -> forall m,
  exists n, Tarai_value n (b + Z_of_nat (S m)) b c (b + Z_of_nat (S m)).
Proof.
  induction m.
  replace (Z_of_nat 1) with 1 by auto.
  destruct (Z_le_dec (b - 1) c).

  destruct (lem_a_gt_b_le_c b c (b+1)) as [n0 ?]; try omega.
  exists (S n0).

  apply Tarai_a_gt_b_2 with b c (b + 1); auto.
  omega.
  apply Tarai_a_le_b; omega.
  apply Tarai_a_le_b; omega.
  apply Tarai_a_le_b; omega.

  destruct (lem_a_gt_b_le_c (b - 1) c (b + 1)) as [n0 ?]; try omega.
  exists (S n0).
  apply Tarai_a_gt_b_1 with b; auto; try omega.
  apply Tarai_a_le_b; omega.

  destruct IHm as [n0 ?].

  rewrite inj_S.
  replace (b + Zsucc (Z_of_nat (S m))) with (b + Z_of_nat (S m) + 1) by omega.

  destruct (Z_le_dec (b - 1) c).
  destruct (lem_a_gt_b_le_c (b + Z_of_nat (S m)) c (b + Z_of_nat (S m) + 1)) as [n1 ?]; try omega.

  exists (S (n0 + n1)).
  apply Tarai_a_gt_b_2 with (b + Z_of_nat (S m)) c  (b + Z_of_nat (S m) + 1); auto; try omega.
  apply lem_n_indep.
  replace (b + Z_of_nat (S m) + 1 - 1) with (b + Z_of_nat (S m)) by omega.
  auto.
  apply Tarai_a_le_b; auto.
  apply Tarai_a_le_b; omega.
  replace (n0 + n1)%nat with (n1 + n0)%nat by omega.
  apply lem_n_indep.
  auto.

  destruct (lem_a_gt_b_le_c (b - 1) c (b + Z_of_nat (S m) + 1)) as [n1 ?]; try omega.
  exists (S (n0 + n1)).
  apply Tarai_a_gt_b_1 with (b + Z_of_nat (S m)); auto; try omega.
  apply lem_n_indep.
  replace (b + Z_of_nat (S m) + 1 - 1) with (b + Z_of_nat (S m)) by omega.
  auto.
  replace (n0 + n1)%nat with (n1 + n0)%nat by omega.
  auto using lem_n_indep.
Qed. 

Lemma lem_a_gt_b_gt_c : forall a b c, a > b -> b > c -> 
   exists n , Tarai_value n a b c a.
Proof. 
  intros. 
  assert (exists d: nat, a - 1 - b = Z_of_nat d). 
  apply Z_of_nat_complete. 
  omega. 

  destruct H1 as [m]. 
  replace a with (b + Z_of_nat (S m)).
  apply lem1_a_gt_b_gt_c; auto.
  rewrite inj_S.
  omega. 
Qed. 

Theorem tarai3_terminates : forall a b c,
  exists n, exists v, Tarai_value n a b c v. 
Proof.
  intros.
  assert (a <= b \/ a > b /\ b <= c \/ a > b /\ b > c) by omega.
  destruct H as [?|[?|?]].
 
 exists 0%nat. exists b.
  apply Tarai_a_le_b; auto.

  destruct (lem_a_gt_b_le_c a b c) as [n0 ?]; try tauto.
  exists n0. exists c. auto.

  destruct (lem_a_gt_b_gt_c a b c) as [n0 ?]; try tauto.
  exists n0. exists a. auto.
Qed.
