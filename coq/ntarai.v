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

Lemma make_value: forall n a b c d e, exists v,
  Tarai_value n a b c d e v.
Proof.
  intros.
  exists (ntarai5 n a b c d e).
  apply Tarai_value_r.
  auto.
Qed.

Definition Z'_le (x y: Z') := x = y \/ x = B.
Definition Z5'_le (a b c d e a' b' c' d' e': Z') :=
  Z'_le a a' /\  Z'_le b b' /\  Z'_le c c' /\  Z'_le d d' /\  Z'_le e e' .

Lemma lem_Z'_le_refl: forall a, Z'_le a a.
Proof.
  left. auto.
Qed.

Lemma lem_Z'_le_B: forall a, Z'_le B a.
Proof.
  right. auto.
Qed.

Lemma lem_Z'_le_trans: forall a b c, Z'_le a b -> Z'_le b c -> Z'_le a c.
Proof.
  intros.
  destruct H.
  congruence.
  rewrite H.
  apply lem_Z'_le_B.
Qed.

Lemma lem_Z'_le_minus_1: forall a b, Z'_le a b -> Z'_le (minus_1 a) (minus_1 b).
Proof.
  intros.
  destruct H.
  rewrite H.
  apply lem_Z'_le_refl.
  rewrite H.
  apply lem_Z'_le_B.
Qed.

Hint Resolve lem_Z'_le_refl: tarai.
Hint Resolve lem_Z'_le_B: tarai.
Hint Resolve lem_Z'_le_minus_1: tarai.

Lemma lem_Z5'_ind: forall a b c d e a' b' c' d' e',
  Z'_le a a' ->
  Z'_le b b' ->
  Z'_le c c' ->
  Z'_le d d' ->
  Z'_le e e' -> Z5'_le a b c d e a' b' c' d' e'.
Proof.
  intros. red. auto.
Qed.

Hint Resolve lem_Z5'_ind: tarai.

Lemma Z'_le_eq: forall a b, Z'_le (V a) b -> V a = b.
Proof.
  intros.
  destruct H.
  auto.
  congruence.
Qed.

Lemma lem_contin_Z5': forall n a b c d e v a' b' c' d' e' v',
  Z5'_le a b c d e a' b' c' d' e' ->
  Tarai_value n a b c d e v ->
  Tarai_value n a' b' c' d' e' v' -> Z'_le v v'.
Proof.
  induction n.
  intros.
  inversion H0; auto with tarai.
  intros.
  destruct H as [Ha[Hb[Hc[Hd He]]]].
  destruct a as [a|].
  destruct b as [b|].
  rewrite <- (Z'_le_eq a a') in H1 by auto.
  rewrite <- (Z'_le_eq b b') in H1 by auto.
  inversion H0; inversion H1; try contradiction.
  auto with tarai.
  apply (IHn v1 v2 v3 v4 v5 v v0 v6 v7 v8 v9 v'); auto.
  constructor.
  apply (IHn (minus_1 (V a)) (V b) c d e v1
                  (minus_1 (V a)) (V b) c' d' e' v0); auto 10 with tarai.
  constructor.
  apply (IHn (minus_1 (V b)) c d e (V a) v2
                  (minus_1 (V b)) c' d' e' (V a) v6); auto 10 with tarai.
  constructor.
  apply (IHn (minus_1 c) d e (V a) (V b) v3
                  (minus_1 c') d' e' (V a) (V b) v7); auto 10 with tarai.
  constructor.
  apply (IHn (minus_1 d) e (V a) (V b) c v4
                  (minus_1 d') e' (V a) (V b) c' v8); auto 10 with tarai.
  apply (IHn (minus_1 e) (V a) (V b) c d v5
                  (minus_1 e') (V a) (V b) c' d' v9); auto 10 with tarai.
  inversion H0. auto with tarai.
  inversion H0. auto with tarai.
  auto with tarai.
Qed.

Lemma lem_contin_nat: forall n n' a b c d e v v',
  (n <= n')%nat ->
  Tarai_value n a b c d e v ->
  Tarai_value n' a b c d e v' -> Z'_le v v'.
Proof.
  assert (forall n m a b c d e v v',
               Tarai_value n a b c d e v ->
               Tarai_value (n+m)%nat a b c d e v' -> Z'_le v v').
  induction n.
  simpl.
  intros.
  inversion H; auto with tarai.

  simpl.
  intros.
  destruct a as [a|]; destruct b as [b|];
    inversion H; auto with tarai.
    inversion H0; try contradiction; auto with tarai.

    inversion H0; try contradiction; auto with tarai.
    destruct (make_value n v0 v6 v7 v8 v9) as [v'' ?].
    destruct (lem_contin_Z5' n v1 v2 v3 v4 v5 v
                                        v0 v6 v7 v8 v9 v''); auto.
    apply lem_Z5'_ind.
    apply (IHn m _ _ _ _ _ _ _ Hv1 Hv0).
    apply (IHn m _ _ _ _ _ _ _ Hv2 Hv6).
    apply (IHn m _ _ _ _ _ _ _ Hv3 Hv7).
    apply (IHn m _ _ _ _ _ _ _ Hv4 Hv8).
    apply (IHn m _ _ _ _ _ _ _ Hv5 Hv9).
    apply IHn with m v0 v6 v7 v8 v9; auto.
    congruence.
    rewrite H16.
    auto with tarai.

  intros.
  apply H with n (n' - n)%nat a b c d e.
  auto.
  replace (n + (n' - n))%nat with n' by omega.
  auto.
Qed.

Definition P_le n a b c d e n' a' b' c' d' e' :=
  (n <= n')%nat /\ Z5'_le a b c d e a' b' c' d' e'.

Hint Unfold P_le: tarai.

Theorem lem_contin: forall n a b c d e v n' a' b' c' d' e' v',
  P_le n a b c d e n' a' b' c' d' e' ->
  Tarai_value n a b c d e v ->
  Tarai_value n' a' b' c' d' e' v' -> Z'_le v v'.
Proof.
  intros.
  destruct (make_value n a' b' c' d' e') as [v'' ?].
  apply lem_Z'_le_trans with v''.
  apply lem_contin_Z5' with n a b c d e a' b' c' d' e'; auto.
  red in H. tauto.
  apply lem_contin_nat with n n' a' b' c' d' e'; auto.
  red in H. tauto.
Qed.

Theorem lem_contin_v: forall n a b c d e v n' a' b' c' d' e',
  P_le n a b c d e n' a' b' c' d' e' ->
  Tarai_value n a b c d e (V v) ->
  Tarai_value n' a' b' c' d' e' (V v).
Proof.
  intros.
  destruct (make_value n' a' b' c' d' e') as [v' ?].
  destruct (lem_contin n a b c d e (V v) n' a' b' c' d' e' v'); auto.
  congruence.
  congruence.
Qed.

Lemma lem_contin_n: forall n n' a b c d e v, (n <= n')%nat ->
  Tarai_value n a b c d e (V v) -> Tarai_value n' a b c d e (V v).
Proof.
  intros.
  apply lem_contin_v with n a b c d e; auto with tarai.
Qed.

Lemma lem_contin_1: forall n a b c d e v,
  Tarai_value n B b c d e (V v) -> Tarai_value n a b c d e (V v).
Proof.
  intros.
  apply lem_contin_v with n B b c d e; auto with tarai.
Qed.

Lemma lem_contin_2: forall n a b c d e v,
  Tarai_value n a B c d e (V v) -> Tarai_value n a b c d e (V v).
Proof.
  intros.
  apply lem_contin_v with n a B c d e; auto with tarai.
Qed.

Lemma lem_contin_3: forall n a b c d e v,
  Tarai_value n a b B d e (V v) -> Tarai_value n a b c d e (V v).
Proof.
  intros.
  apply lem_contin_v with n a b B d e; auto with tarai.
Qed.

Lemma lem_contin_4: forall n a b c d e v,
  Tarai_value n a b c B e (V v) -> Tarai_value n a b c d e (V v).
Proof.
  intros.
  apply lem_contin_v with n a b c B e; auto with tarai.
Qed.

Lemma lem_contin_5: forall n a b c d e v,
  Tarai_value n a b c d B (V v) -> Tarai_value n a b c d e (V v).
Proof.
  intros.
  apply lem_contin_v with n a b c d B; auto with tarai.
Qed.

Hint Resolve lem_contin_n: tarai.
Hint Resolve lem_contin_1: tarai.
Hint Resolve lem_contin_2: tarai.
Hint Resolve lem_contin_3: tarai.
Hint Resolve lem_contin_4: tarai.
Hint Resolve lem_contin_5: tarai.

Inductive Tarai_Y (n: nat):
     Z' -> Z' -> Z' -> Z' -> Z' -> Z -> Prop :=
| Tarai_Y_2 a b v
     (Hterm: Tarai_value n (V a) (V b) B B B (V v))
     (Hle: v <= b):
     Tarai_Y n (V a) (V b) B B B v
| Tarai_Y_3 a b c v
     (Hterm: Tarai_value n (V a) (V b) (V c) B B (V v))
     (Hle: v <= c):
     Tarai_Y n (V a) (V b) (V c) B B v
| Tarai_Y_4 a b c d v
     (Hterm: Tarai_value n (V a) (V b) (V c) (V d) B (V v))
     (Hle: v <= d):
     Tarai_Y n (V a) (V b) (V c) (V d) B v
| Tarai_Y_5 a b c d e v
     (Hterm: Tarai_value n (V a) (V b) (V c) (V d) (V e) (V v))
     (Hle: v <= e):
     Tarai_Y n (V a) (V b) (V c) (V d) (V e) v.

Lemma Y_value: forall n a b c d e v, Tarai_Y n a b c d e v -> Tarai_value n a b c d e (V v).
Proof.
  intros.
  inversion H; auto.
Qed.

Lemma lem_1: forall a b, a <= b ->
   exists n, exists v, Tarai_Y n (V a) (V b) B B B v.
Proof.
   intros.
   exists 1%nat. exists b.
   apply Tarai_Y_2; auto with zarith.
   constructor.
   auto.
Qed.

Lemma lem_1_eq: forall a b, a <= b ->
   exists n, Tarai_Y n (V a) (V b) B B B b.
Proof.
   intros.
   exists 1%nat.
   apply Tarai_Y_2; auto with zarith.
   constructor.
   auto.
Qed.

Lemma lem_2: forall a b c, a <= c -> b <= c ->
   exists n, exists v, Tarai_Y n (V a) (V b) (V c) B B v.
Proof.
   intros.
   destruct (Z_le_dec a b).
   destruct (lem_1 a b) as [n [v ?]]; auto.
   inversion H1.
   exists n. exists v.
   constructor.
   apply lem_contin_3.
   auto with tarai.
   omega.

   destruct (lem_1_eq (b - 1) c) as [n1 Hv2]. omega.

   assert (exists m : nat, a - b - 1 = Z_of_nat m). 
   apply Z_of_nat_complete.
   omega. 
   destruct H1 as [m ?].
   replace a with (b + 1 + Z_of_nat m) by omega.
   clear H1.
   induction m.
     destruct (lem_1 b b) as [n0 [v1 Hv1]]. omega.
     inversion Hv1. inversion Hv2.
     destruct (lem_1 v1 c) as [n2 [vr Hvr]].
     omega.
     inversion Hvr.
     destruct (make_value (n0+n1+n2)%nat (V (c - 1)) B B (V (b + 1)) (V b)) as [v3 Hv3].
     destruct (make_value (n0+n1+n2)%nat B B (V (b + 1)) (V b) (V c)) as [v4 Hv4].
     destruct (make_value (n0+n1+n2)%nat B (V (b + 1)) (V b) (V c) B) as [v5 Hv5].
     exists (S (n0 + n1 + n2))%nat. exists vr.
     simpl. replace (b + 1 + 0) with (b + 1) by omega.
     constructor; auto.
     apply Tarai_value_gt with (V v1) (V c) v3 v4 v5; simpl; auto.
     omega.
     replace (b + 1 - 1) with b by omega.
     apply lem_contin_n with n0; [omega|]. apply lem_contin_3. auto with tarai.
     apply lem_contin_n with n1; [omega|]. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n2; [omega|].
     apply lem_contin_3.
     apply lem_contin_4.
     apply lem_contin_5.
     auto with tarai.

     destruct IHm as [n0 [v1 Hv1]].
     inversion Hv1. inversion Hv2.
     destruct (lem_1 v1 c) as [n2 [vr Hvr]].
     omega.
     inversion Hvr.
     rewrite inj_S.
     replace (b + 1 + Zsucc (Z_of_nat m)) with (b + 2 + Z_of_nat m) by omega.
     destruct (make_value (n0+n1+n2)%nat (V (c - 1)) B B (V (b + 2 + Z_of_nat m)) (V b)) as [v3 Hv3].
     destruct (make_value (n0+n1+n2)%nat B B (V (b + 2 + Z_of_nat m)) (V b) (V c)) as [v4 Hv4].
     destruct (make_value (n0+n1+n2)%nat B (V (b + 2 + Z_of_nat m)) (V b) (V c) B) as [v5 Hv5].
     exists (S (n0 + n1 + n2))%nat. exists vr.
     constructor; auto.
     apply Tarai_value_gt with (V v1) (V c) v3 v4 v5; simpl; auto.
     omega.
     replace (b + 2 + Z_of_nat m - 1) with (b +1 + Z_of_nat m) by omega.
     apply lem_contin_n with n0; [omega|]. auto.
     apply lem_contin_n with n1; [omega|]. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n2; [omega|].
     apply lem_contin_3.
     apply lem_contin_4.
     apply lem_contin_5.
     auto with tarai.
Qed.


Lemma lem_3: forall a b c d, a <= d -> b <= d -> c <= d ->
   exists n, exists v, Tarai_Y n (V a) (V b) (V c) (V d) B v.
Proof.
   intros.
   destruct (Z_le_dec a b).
   destruct (lem_1 a b) as [n [v ?]]; auto.
   inversion H2.
   exists n. exists v.
   constructor.
   apply lem_contin_3. apply lem_contin_4.
   auto with tarai.
   omega.

   destruct (lem_1_eq (c - 1) d) as [n2 Hv3]. omega.

   assert (exists m : nat, a - b - 1 = Z_of_nat m). 
   apply Z_of_nat_complete.
   omega. 
   destruct H2 as [m ?].
   replace a with (b + 1 + Z_of_nat m) by omega.
   clear H2.
   induction m.
     destruct (lem_1 b b) as [n0 [v1 Hv1]]. omega.
     destruct (lem_2 (b - 1) c d) as [n1 [v2 Hv2]]. omega. omega.
     inversion Hv1. inversion Hv2. inversion Hv3.
     destruct (lem_2 v1 v2 d) as [n3 [vr Hvr]].
     omega. omega.
     destruct (make_value (n0+n1+n2+n3)%nat (V (d - 1)) B (V (b + 1)) (V b) (V c)) as [v4 Hv4].
     destruct (make_value (n0+n1+n2+n3)%nat B (V (b + 1)) (V b) (V c) (V d)) as [v5 Hv5].
     inversion Hvr.
     exists (S (n0 + n1 + n2 + n3))%nat. exists vr.
     simpl. replace (b + 1 + 0) with (b + 1) by omega.
     constructor; auto.
     apply Tarai_value_gt with (V v1) (V v2) (V d) v4 v5; simpl; auto.
     omega.
     replace (b + 1 - 1) with b by omega.
     apply lem_contin_n with n0; [omega|].
     apply lem_contin_3. apply lem_contin_4. auto with tarai.
     apply lem_contin_n with n1; [omega|].
     apply lem_contin_5.  auto with tarai.
     apply lem_contin_n with n2; [omega|].
     apply lem_contin_4. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n3; [omega|].
     apply lem_contin_4. apply lem_contin_5. auto with tarai.

     destruct IHm as [n0 [v1 Hv1]].
     destruct (lem_2 (b - 1) c d) as [n1 [v2 Hv2]]. omega. omega.
     inversion Hv1. inversion Hv2. inversion Hv3.
     destruct (lem_2 v1 v2 d) as [n3 [vr Hvr]].
     omega. omega.
     destruct (make_value (n0+n1+n2+n3)%nat (V (d - 1)) B (V (b + 2 + Z_of_nat m)) (V b) (V c)) as [v4 Hv4].
     destruct (make_value (n0+n1+n2+n3)%nat B (V (b + 2 + Z_of_nat m)) (V b) (V c) (V d)) as [v5 Hv5].
     inversion Hvr.
     rewrite inj_S.
     replace (b + 1 + Zsucc (Z_of_nat m)) with (b + 2 + Z_of_nat m) by omega.
     exists (S (n0 + n1 + n2 + n3))%nat. exists vr.
     constructor; auto.
     apply Tarai_value_gt with (V v1) (V v2) (V d) v4 v5; simpl; auto.
     omega.
     replace (b + 2 + Z_of_nat m - 1) with (b +1 + Z_of_nat m) by omega.
     apply lem_contin_n with n0; [omega|]. auto.
     apply lem_contin_n with n1; [omega|].
     apply lem_contin_5.  auto with tarai.
     apply lem_contin_n with n2; [omega|].
     apply lem_contin_4. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n3; [omega|].
     apply lem_contin_4. apply lem_contin_5. auto with tarai.
Qed.

Lemma lem_4: forall a b c d e, a <= e -> b <= e -> c <= e -> d <= e ->
   exists n, exists v, Tarai_Y n (V a) (V b) (V c) (V d) (V e) v.
Proof.
   intros.
   destruct (Z_le_dec a b).
   destruct (lem_1 a b) as [n [v ?]]; auto.
   inversion H3.
   exists n. exists v.
   constructor.
   apply lem_contin_3. apply lem_contin_4. apply lem_contin_5.
   auto with tarai.
   omega.

   destruct (lem_1_eq (d - 1) e) as [n3 Hv4]. omega.

   assert (exists m : nat, a - b - 1 = Z_of_nat m). 
   apply Z_of_nat_complete.
   omega. 
   destruct H3 as [m ?].
   replace a with (b + 1 + Z_of_nat m) by omega.
   clear H3.
   induction m.
     destruct (lem_1 b b) as [n0 [v1 Hv1]]. omega.
     destruct (lem_3 (b - 1) c d e) as [n1 [v2 Hv2]]. omega. omega. omega.
     destruct (lem_2 (c - 1) d e) as [n2 [v3 Hv3]]. omega. omega.
     inversion Hv1. inversion Hv2. inversion Hv3. inversion Hv4.
     destruct (lem_3 v1 v2 v3 e) as [n4 [vr Hvr]].
     omega. omega. omega.
     destruct (make_value (n0+n1+n2+n3+n4)%nat (V (e - 1)) (V (b + 1)) (V b) (V c) (V d)) as [v6 Hv5].
     inversion Hvr.
     exists (S (n0 + n1 + n2 + n3 + n4))%nat. exists vr.
     simpl. replace (b + 1 + 0) with (b + 1) by omega.
     constructor; auto.
     apply Tarai_value_gt with (V v1) (V v2) (V v3) (V e) v6; simpl; auto.
     omega.
     replace (b + 1 - 1) with b by omega.
     apply lem_contin_n with n0; [omega|].
     apply lem_contin_3. apply lem_contin_4. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n1; [omega|].
     apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n2; [omega|].
     apply lem_contin_4. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n3; [omega|].
     apply lem_contin_3. apply lem_contin_4. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n4; [omega|].
     apply lem_contin_5. auto with tarai.

     destruct IHm as [n0 [v1 Hv1]].
     destruct (lem_3 (b - 1) c d e) as [n1 [v2 Hv2]]. omega. omega. omega.
     destruct (lem_2 (c - 1) d e) as [n2 [v3 Hv3]]. omega. omega.
     inversion Hv1. inversion Hv2. inversion Hv3. inversion Hv4.
     destruct (lem_3 v1 v2 v3 e) as [n4 [vr Hvr]].
     omega. omega. omega.
     destruct (make_value (n0+n1+n2+n3+n4)%nat (V (e - 1)) (V (b + 2 + Z_of_nat m)) (V b) (V c) (V d)) as [v6 Hv5].
     inversion Hvr.
     rewrite inj_S.
     replace (b + 1 + Zsucc (Z_of_nat m)) with (b + 2 + Z_of_nat m) by omega.
     exists (S (n0 + n1 + n2 + n3 + n4))%nat. exists vr.
     constructor; auto.
     apply Tarai_value_gt with (V v1) (V v2) (V v3) (V e) v6; simpl; auto.
     omega.
     replace (b + 2 + Z_of_nat m - 1) with (b +1 + Z_of_nat m) by omega.
     apply lem_contin_n with n0; [omega|auto].
     apply lem_contin_n with n1; [omega|].
     apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n2; [omega|].
     apply lem_contin_4. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n3; [omega|].
     apply lem_contin_3. apply lem_contin_4. apply lem_contin_5. auto with tarai.
     apply lem_contin_n with n4; [omega|].
     apply lem_contin_5. auto with tarai.
Qed.

Lemma lem_5: forall b c d e m, 
  exists n, exists v,
     Tarai_value n (V (b + Z_of_nat (S m))) (V b) (V c) (V d) (V e) (V v) /\
     (v <= b + Z_of_nat (S m) \/
      v <= c \/
      v <= d \/
      v <= e).
Proof.
  induction m.
    simpl.
    destruct (Z_le_dec (b + 1) c) as [Hac|Hac].
    destruct (lem_2 (b + 1) b c) as [n [v ?]].
    auto. omega.
    exists n. exists v.
    inversion H.
    constructor.
    apply lem_contin_4. apply lem_contin_5. auto with tarai.
    auto.

    destruct (Z_le_dec (b + 1) d) as [Had|Had].
    destruct (lem_3 (b + 1) b c d) as [n [v ?]].
    auto. omega. omega.
    exists n. exists v.
    inversion H.
    constructor.
    apply lem_contin_5. auto with tarai.
    auto.

    destruct (Z_le_dec (b + 1) e) as [Hae|Hae].
    destruct (lem_4 (b + 1) b c d e) as [n [v ?]].
    auto. omega. omega. omega.
    exists n. exists v.
    inversion H.
    constructor.
    auto with tarai.
    auto.

    destruct (lem_1 b b) as [n0 [v1 Hv1]]. omega.
    destruct (lem_4 (b - 1) c d e (b + 1)) as [n1 [v2 Hv2]]. omega. omega. omega. omega.
    destruct (lem_3 (c - 1) d e (b + 1)) as [n2 [v3 Hv3]]. omega. omega. omega.
    destruct (lem_2 (d - 1) e (b + 1)) as [n3 [v4 Hv4]]. omega. omega.
    destruct (lem_1_eq (e - 1) (b + 1)) as [n4 Hv5]. omega.
    inversion Hv1. inversion Hv2. inversion Hv3. inversion Hv4. inversion Hv5.
    destruct (lem_4 v1 v2 v3 v4 (b + 1)) as [n5 [vr Hvr]].
    omega. omega. omega. omega.
    inversion Hvr.
    exists (S (n0 + n1 + n2 + n3 + n4 + n5))%nat. exists vr.
    constructor.
    apply Tarai_value_gt with (V v1) (V v2) (V v3) (V v4) (V (b + 1)); simpl; auto.
    omega.
    replace (b + 1 - 1) with b by omega.
    apply lem_contin_n with n0; [omega|].
    apply lem_contin_3. apply lem_contin_4. apply lem_contin_5. auto with tarai.
    apply lem_contin_n with n1; [omega|]. auto.
    apply lem_contin_n with n2; [omega|].
    apply lem_contin_5. auto with tarai.
    apply lem_contin_n with n3; [omega|].
    apply lem_contin_4. apply lem_contin_5. auto with tarai.
    apply lem_contin_n with n4; [omega|].
    apply lem_contin_3. apply lem_contin_4. apply lem_contin_5. auto with tarai.
    apply lem_contin_n with n5; [omega|auto].
    auto.

    rewrite inj_S. rewrite inj_S in * |- *.
    replace (b + Zsucc (Zsucc (Z_of_nat m))) with (b + 2 + Z_of_nat m) by omega.
    replace (b + Zsucc (Z_of_nat m)) with (b + 1 + Z_of_nat m) in IHm by omega.

    destruct (Z_le_dec (b + 2 + Z_of_nat m) c) as [Hac|Hac].
    destruct (lem_2 (b + 2 + Z_of_nat m) b c) as [n [v ?]].
    auto. omega.
    exists n. exists v.
    inversion H.
    constructor.
    apply lem_contin_4. apply lem_contin_5. auto with tarai.
    auto.

    destruct (Z_le_dec (b + 2 + Z_of_nat m) d) as [Had|Had].
    destruct (lem_3 (b + 2 + Z_of_nat m) b c d) as [n [v ?]].
    auto. omega. omega.
    exists n. exists v.
    inversion H.
    constructor.
    apply lem_contin_5. auto with tarai.
    auto.

    destruct (Z_le_dec (b + 2 + Z_of_nat m) e) as [Hae|Hae].
    destruct (lem_4 (b + 2 + Z_of_nat m) b c d e) as [n [v ?]].
    auto. omega. omega. omega.
    exists n. exists v.
    inversion H.
    constructor.
    auto.
    auto.

    destruct IHm as [n0 [v1 [Hv1 ?]]].
    assert (v1 <= b + 1 + Z_of_nat m) by omega.
    clear H.
    destruct (lem_4 (b - 1) c d e (b + 2 + Z_of_nat m)) as [n1 [v2 Hv2]]. omega. omega. omega. omega.
    destruct (lem_3 (c - 1) d e (b + 2 + Z_of_nat m)) as [n2 [v3 Hv3]]. omega. omega. omega.
    destruct (lem_2 (d - 1) e (b + 2 + Z_of_nat m)) as [n3 [v4 Hv4]]. omega. omega.
    destruct (lem_1_eq (e - 1) (b + 2 + Z_of_nat m)) as [n4 Hv5]. omega.
    inversion Hv1.
    apply False_ind. omega.
    inversion Hv2. inversion Hv3. inversion Hv4. inversion Hv5.
    destruct (lem_4 v1 v2 v3 v4 (b + 2 + Z_of_nat m)) as [n5 [vr' Hvr']].
    omega. omega. omega. omega.
    inversion Hvr'.
    exists (S (n0 + n1 + n2 + n3 + n4 + n5))%nat. exists vr'.
    constructor.
    apply Tarai_value_gt with (V v1) (V v2) (V v3) (V v4) (V (b + 2 + Z_of_nat m)); simpl; auto.
    omega.
    replace (b + 2 + Z_of_nat m - 1) with (b + 1 + Z_of_nat m) by omega.
    apply lem_contin_n with n0; [omega|]. auto.
    apply lem_contin_n with n1; [omega|]. auto.
    apply lem_contin_n with n2; [omega|].
    apply lem_contin_5. auto.
    apply lem_contin_n with n3; [omega|].
    apply lem_contin_4. apply lem_contin_5. auto.
    apply lem_contin_n with n4; [omega|].
    apply lem_contin_3. apply lem_contin_4. apply lem_contin_5. auto.
    apply lem_contin_n with n5; [omega|]. auto.
    auto.
Qed.

Theorem tarai5_termination: forall a b c d e,
  exists n, exists v, Tarai_value n (V a) (V b) (V c) (V d) (V e) (V v).
Proof.
  intros.
  destruct (Z_le_dec a b).
  destruct (lem_1 a b) as [n [v ?]]; auto.
  inversion H.
  exists n. exists v.
  apply lem_contin_3. apply lem_contin_4. apply lem_contin_5.
  auto.

  assert (exists m : nat, a - b - 1 = Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H as [m ?].
  replace a with (b + Zsucc (Z_of_nat m)) by omega.
  rewrite <- inj_S.
  destruct (lem_5 b c d e m) as [n' [v ?]].
  exists n'. exists v.
  tauto.
Qed.
