Require Import ZArith.

Open Scope Z_scope.

Fixpoint ntarai3 (n : nat) (a b c : option Z) :=
match a with 
| None => None
| Some av =>
  match b with 
  | None => None
  | Some bv => 
      if Z_le_dec av bv then b else
      match n with 
      | 0%nat => None
      | S np => 
          match c with 
          | None => None
          | Some cv => 
              (ntarai3 np 
                (ntarai3 np (Some (av-1)) b c)
                (ntarai3 np (Some (bv-1)) c a)
                (ntarai3 np (Some (cv-1)) a b))
          end 
      end
  end
end.

Definition ntarai3v (n : nat) (av bv cv : Z):=
ntarai3 n (Some av) (Some bv) (Some cv). 

Inductive Tarai_value:
     nat -> Z -> Z -> Z -> Z -> Prop :=
| Tarai_a_le_b n a b c (Hle: a <= b):
     Tarai_value n a b c b
| Tarai_a_gt_b_1 n a b c v1 v2
     (Hgt: a > b)
     (Hle2: v1 <= v2)
     (Hrec1: Tarai_value n (a-1) b c v1)
     (Hrec2: Tarai_value n (b-1) c a v2):
     Tarai_value (S n) a b c v2
| Tarai_a_gt_b_2 n a b c (v1 v2 v3 v4: Z)
     (Hgt: a > b)
     (Hle2: ~v1 <= v2)
     (Hrec1: Tarai_value n (a-1) b c v1)
     (Hrec2: Tarai_value n (b-1) c a v2)
     (Hrec3: Tarai_value n (c-1) a b v3)
     (Hrec4: Tarai_value n v1 v2 v3 v4):
    Tarai_value (S n) a b c v4.

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
