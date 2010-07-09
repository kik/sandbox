Require Import ZArith.

Open Scope Z_scope.

Definition oZ := option Z.

Fixpoint Yn {A: Type} n (init: A) (recur: A -> A) : A :=
match n with
| O => init
| S n' => recur (Yn n' init recur)
end.

Definition minus_1 (x: oZ) :=
match x with
| Some x => Some (x - 1)
| None => None
end.

Definition ntarai5_init (a b c d e: oZ) : option Z := None.
Definition ntarai5_rec f (a b c d e: oZ) : option Z :=
match a, b with
| Some av, Some bv =>
  if Z_le_dec av bv then b else
  f (f (minus_1 a) b c d e)
    (f (minus_1 b) c d e a)
    (f (minus_1 c) d e a b)
    (f (minus_1 d) e a b c)
    (f (minus_1 e) a b c d)
| _, _ => None 
end.

Definition ntarai5 n := Yn n ntarai5_init  ntarai5_rec.

Inductive Tarai_value:
     nat -> oZ -> oZ -> oZ -> oZ -> oZ -> oZ -> Prop :=
| Tarai_value_le n a b c d e: a <= b ->
     Tarai_value (S n) (Some a) (Some b) c d e (Some b)
| Tarai_value_gt n a b c d e v1 v2 v3 v4 v5 vr: ~a <= b ->
     Tarai_value n (minus_1 (Some a)) (Some b) c d e v1 ->
     Tarai_value n (minus_1 (Some b)) c d e (Some a) v2 ->
     Tarai_value n (minus_1 c) d e (Some a) (Some b) v3 ->
     Tarai_value n (minus_1 d) e (Some a) (Some b) c v4 ->
     Tarai_value n (minus_1 e) (Some a) (Some b) c d v5 ->
     Tarai_value n v1 v2 v3 v4 v5 vr ->
     Tarai_value (S n) (Some a) (Some b) c d e vr
| Tarai_value_none_1 a b c d e:
     Tarai_value O a b c d e None
| Tarai_value_none_2 n b c d e:
     Tarai_value n None b c d e None
| Tarai_value_none_3 n a c d e:
     Tarai_value n a None c d e None.

Lemma lem_step_l: forall n a b c d e v,
   (if Z_le_dec a b then Some b else
    (ntarai5 n (ntarai5 n (Some (a - 1)) (Some b) c d e)
                  (ntarai5 n (Some (b - 1)) c d e (Some a))
                  (ntarai5 n (minus_1 c) d e (Some a) (Some b))
                  (ntarai5 n (minus_1 d) e (Some a) (Some b) c)
                  (ntarai5 n (minus_1 e) (Some a) (Some b) c d))) = v ->
   ntarai5 (S n) (Some a) (Some b) c d e = v.
Proof.
  intros.
  exact H.
Qed.

Lemma lem_step_r: forall n a b c d e v,
   v =
   (if Z_le_dec a b then Some b else
    (ntarai5 n (ntarai5 n (Some (a - 1)) (Some b) c d e)
                  (ntarai5 n (Some (b - 1)) c d e (Some a))
                  (ntarai5 n (minus_1 c) d e (Some a) (Some b))
                  (ntarai5 n (minus_1 d) e (Some a) (Some b) c)
                  (ntarai5 n (minus_1 e) (Some a) (Some b) c d))) ->
   v = ntarai5 (S n) (Some a) (Some b) c d e.
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
  apply IHn.
  reflexivity.
  apply IHn.
  reflexivity.
  apply IHn.
  reflexivity.
  apply IHn.
  reflexivity.
  apply IHn.
  reflexivity.
  apply IHn.
  unfold ntarai5 in H. simpl in H.
  destruct (Z_le_dec a b); [contradiction|].
  exact H.
  unfold ntarai5 in H. simpl in H. rewrite <- H.
  constructor.
  unfold ntarai5 in H. simpl in H. rewrite <- H.
  constructor.
Qed.

Definition c_le (a b c d e a' b' c' d' e': option Z) :=
  (a = a' \/ a = None) /\
  (b = b' \/ b = None) /\
  (c = c' \/ c = None) /\
  (d = d' \/ d = None) /\
  (e = e' \/ e = None).

Lemma lem_none: forall n a b c d e a' b' c' d' e' v,
  c_le a b c d e a' b' c' d' e' ->
  Tarai_value n a b c d e (Some v) ->
  Tarai_value n a' b' c' d' e' (Some v).
Proof.
  induction n.
  intros. inversion H0.

  intros.
  red in H.
  inversion H0.
  rewrite <- H3 in H.
  rewrite <- H4 in H.
  destruct H as [?[?[?[??]]]].
  destruct H; [|congruence].
  destruct H9; [|congruence].
  rewrite <- H.
  rewrite <- H9.
  rewrite H2.
  constructor.
  auto.
  

Inductive Tarai_Y (n: nat):
     oZ -> oZ -> oZ -> oZ -> oZ -> Z -> Prop :=
| Tarai_Y_2 a b v
     (Hterm: ntarai5 n (Some a) (Some b) None None None = (Some v))
     (Hle: v <= b):
     Tarai_Y n (Some a) (Some b) None None None v
| Tarai_Y_3 a b c v
     (Hterm: ntarai5 n (Some a) (Some b) (Some c) None None = (Some v))
     (Hle: v <= c):
     Tarai_Y n (Some a) (Some b) (Some c) None None v
| Tarai_Y_4 a b c d v
     (Hterm: ntarai5 n (Some a) (Some b) (Some c) (Some d) None = (Some v))
     (Hle: v <= d):
     Tarai_Y n (Some a) (Some b) (Some c) (Some d) None v.
(*
| Tarai_Y_1n a b c d e v:
     Tarai_Y n None b c d e v -> Tarai_Y n a b c d e v
| Tarai_Y_2n a b c d e v:
     Tarai_Y n a None c d e v -> Tarai_Y n a b c d e v
| Tarai_Y_3n a b c d e v:
     Tarai_Y n a b None d e v -> Tarai_Y n a b c d e v
| Tarai_Y_4n a b c d e v:
     Tarai_Y n a b c None e v -> Tarai_Y n a b c d e v
| Tarai_Y_5n a b c d e v:
     Tarai_Y n a b c d None v -> Tarai_Y n a b c d e v.*)


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
     destruct (ntarai5 n (Some (a - 1)) (Some b) None d e) as [v0|].
     rewrite (H5 v0); auto. clear H5.
     simpl in H4.
     destruct (ntarai5 n (Some (b - 1)) None d e (Some a)) as [v1|].
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
  ntarai5 n a None None None None = Some v -> ntarai5 n a b c d e = Some v.
Proof.
  intros.
  unfold ntarai5 in H.
  destruct n; destruct a; inversion H.
Qed.

Lemma lem_2n: forall n a b c d e v,
  ntarai5 n a b None None None = Some v -> ntarai5 n a b c d e = Some v.
Proof.
  intros.
  destruct b.
  unfold ntarai5 in H.
  destruct n.
  inversion H.
  destruct a; inversion H.
Qed.

Lemma lem_3n: forall n a b c d e v,
  ntarai5 n a b None d e = Some v -> ntarai5 n a b c d e = Some v.
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
   exists n, exists v, Tarai_Y n (Some a) (Some b) None None None v.
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
   exists n, exists v, Tarai_Y n (Some a) (Some b) (Some c) None None v.
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
   destruct (lem_1 b b None None None) as [n0 [v ?]]. omega.
   unfold ntarai5.
   simpl.
   destruct (Z_le_dec (b + 1 + 0) b).
   apply False_ind. omega.

Inductive Tarai_value:
     nat -> oZ -> oZ -> oZ -> oZ -> oZ -> Z -> Prop :=
| Tarai_1 n a b
     (Hmax1: a <= b):
     Tarai_value (S n) (Some a) (Some b) None None None b
| Tarai_2 n a b c v1 v2 v3 vr
     (Hmax1: a <= c)
     (Hmax2: b <= c)
     (Hrec1: Tarai_value n (Some (a-1)) (Some b) (Some c) None None v1)
     (Hrec2: Tarai_value n (Some (b-1)) (Some c) None None (Some a) v2)
     (Hrec3: Tarai_value n (Some (c-1)) None None (Some a) (Some b) v3)
     (Hrec:  Tarai_value n (Some v1) (Some v2) (Some v3) None None vr):
     Tarai_value (S n) (Some a) (Some b) (Some c) None None vr
| Tarai_3 n a b c d v1 v2 v3 v4 vr (Hgt: a > b)
     (Hmax1: a <= d)
     (Hmax2: b <= d)
     (Hmax3: c <= d)
     (Hrec1: Tarai_value n (Some (a-1)) (Some b) (Some c) (Some d) None v1)
     (Hrec2: Tarai_value n (Some (b-1)) (Some c) (Some d) None (Some a) v2)
     (Hrec3: Tarai_value n (Some (c-1)) (Some d) None (Some a) (Some b) v3)
     (Hrec4: Tarai_value n (Some (d-1)) None (Some a) (Some b) (Some c) v4)
     (Hrec:  Tarai_value n (Some v1) (Some v2) (Some v3) (Some v4) None vr):
     Tarai_value (S n) (Some a) (Some b) (Some c) (Some d) None vr.

Lemma Tarai_1_term: forall n a b v, Tarai_value n (Some a) (Some b) None None None v ->
  ntarai5 n (Some a) (Some b) None None None = Some v.
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
  forall n a b c v, Tarai_value n a b c v -> ntarai3 n (Some a) (Some b) (Some c) = Some v.
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
  forall n a b c v, ntarai3 n (Some a) (Some b) (Some c) = Some v -> Tarai_value n a b c v.
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
  destruct (ntarai3 0 (Some (a - 1)) (Some b) (Some c)) as [v1|]; [| inversion H].
  destruct (ntarai3 0 (Some (b - 1)) (Some c) (Some a)) as [v2|]; [| inversion H].
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply Tarai_a_gt_b_1 with v1; auto.
  omega.
  congruence.
  inversion H.
  destruct (ntarai3 (S n) (Some (a - 1)) (Some b) (Some c)) as [v1|]; [| inversion H].
  destruct (ntarai3 (S n) (Some (b - 1)) (Some c) (Some a)) as [v2|]; [| inversion H].
  destruct (ntarai3 (S n) (Some (c - 1)) (Some a) (Some b)) as [v3|].
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
