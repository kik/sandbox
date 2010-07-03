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
     nat -> option Z -> option Z -> option Z -> Z -> Prop :=
| Tarai_a_le_b n (av bv: Z) c (Hle: av <= bv):
     Tarai_value n (Some av) (Some bv) c bv
| Tarai_a_gt_b_1 n (av bv cv: Z) (v1 v2: Z)
     (Hgt: av > bv)
     (Hle2: v1 <= v2)
     (Hrec1: Tarai_value n (Some (av-1)) (Some bv) (Some cv) v1)
     (Hrec2: Tarai_value n (Some (bv-1)) (Some cv) (Some av) v2):
     Tarai_value (S n) (Some av) (Some bv) (Some cv) v2
| Tarai_a_gt_b_2 n (av bv cv: Z) (v1 v2 v3 v4: Z)
     (Hgt: av > bv)
     (Hle2: ~v1 <= v2)
     (Hrec1: Tarai_value n (Some (av-1)) (Some bv) (Some cv) v1)
     (Hrec2: Tarai_value n (Some (bv-1)) (Some cv) (Some av) v2)
     (Hrec3: Tarai_value n (Some (cv-1)) (Some av) (Some bv) v3)
     (Hrec4: Tarai_value n (Some v1)
                                   (Some v2)
                                   (Some v3) v4):
    Tarai_value (S n) (Some av) (Some bv) (Some cv) v4.

Lemma lem_safficiency:
  forall n a b c v, Tarai_value n a b c v -> ntarai3 n a b c = Some v.
Proof.
  intros.
  induction H.
    destruct n;
    simpl;
    destruct (Z_le_dec av bv); auto; try contradiction.

    simpl.
    rewrite IHTarai_value1.
    rewrite IHTarai_value2.
    destruct (Z_le_dec av bv).
    absurd (av > bv); omega.
    destruct n; simpl; destruct (Z_le_dec v1 v2); auto; contradiction.

    simpl.    
    rewrite IHTarai_value1.
    rewrite IHTarai_value2.
    rewrite IHTarai_value3.
    rewrite IHTarai_value4.
    destruct (Z_le_dec av bv); auto; contradiction.
Qed.

Lemma lem_necessity:
  forall n a b c v, ntarai3 n a b c = Some v -> Tarai_value n a b c v.
Proof.
  induction n.
  intros.
  simpl in H.
  destruct a as [av|]; [|congruence].
  destruct b as [bv|]; [|congruence].
  destruct (Z_le_dec av bv).
  inversion H.
  apply Tarai_a_le_b.
  congruence.
  inversion H.
  simpl.
  destruct a as [av|]; [|congruence].
  destruct b as [bv|]; [|congruence].
  destruct (Z_le_dec av bv).
  intros.
  inversion H.
  apply Tarai_a_le_b.
  congruence.
  destruct c as [cv|]; [|congruence].
  intros.
  generalize (IHn (Some (av - 1)) (Some bv) (Some cv)).
  generalize (IHn (Some (bv - 1)) (Some cv) (Some av)).
  generalize (IHn (Some (cv - 1)) (Some av) (Some bv)).
  intros.
  destruct n.
  destruct (ntarai3 0 (Some (av - 1)) (Some bv) (Some cv)) as [v1|]; [| inversion H].
  destruct (ntarai3 0 (Some (bv - 1)) (Some cv) (Some av)) as [v2|]; [| inversion H].
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply Tarai_a_gt_b_1 with v1; auto.
  omega.
  congruence.
  inversion H.
  destruct (ntarai3 (S n) (Some (av - 1)) (Some bv) (Some cv)) as [v1|]; [| inversion H].
  destruct (ntarai3 (S n) (Some (bv - 1)) (Some cv) (Some av)) as [v2|]; [| inversion H].
  destruct (ntarai3 (S n) (Some (cv - 1)) (Some av) (Some bv)) as [v3|].
  generalize (IHn (Some v1) (Some v2) (Some v3) v H).
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

Lemma lem1_a_gt_b_le_c : forall bv cv m, bv <= cv ->
  exists n, Tarai_value n (Some (bv + Z_of_nat(S m))) (Some bv) (Some cv) cv.
Proof.
  induction m. 
  intros.
  exists 1%nat.
  replace (Z_of_nat 1) with 1 by auto.

  apply Tarai_a_gt_b_1 with bv; auto.
  omega.
  apply Tarai_a_le_b; omega.
  apply Tarai_a_le_b; omega.

  intros.
  destruct (IHm H) as [n' Hn'].
  exists (S n').

  apply Tarai_a_gt_b_1 with cv; auto.
  rewrite inj_S. omega.
  omega.
  rewrite inj_S.
  replace (bv + Zsucc (Z_of_nat (S m)) - 1) with (bv + Z_of_nat (S m)) by omega.
  auto.

  apply Tarai_a_le_b; omega.
Qed. 

Lemma lem_a_gt_b_le_c : forall av bv cv,  av > bv -> bv <= cv -> 
  exists n : nat, Tarai_value n (Some av) (Some bv) (Some cv) cv.
Proof.
  intros. 

  assert (exists m : nat, av-1-bv=Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H1 as [m ?]. 

  replace av with (bv + Zsucc (Z_of_nat m)) by omega.
  rewrite <- inj_S.
  auto using lem1_a_gt_b_le_c. 
Qed. 

Lemma lem1_a_gt_b_gt_c : forall bv cv,  bv > cv -> forall m,
  exists n, Tarai_value n (Some (bv + Z_of_nat (S m))) (Some bv) (Some cv) (bv + Z_of_nat (S m)).
Proof.
  induction m.
  replace (Z_of_nat 1) with 1 by auto.
  destruct (Z_le_dec (bv - 1) cv).

  destruct (lem_a_gt_b_le_c bv cv (bv+1)) as [n0 ?]; try omega.
  exists (S n0).

  apply Tarai_a_gt_b_2 with bv cv (bv + 1); auto.
  omega.
  apply Tarai_a_le_b; omega.
  apply Tarai_a_le_b; omega.
  apply Tarai_a_le_b; omega.

  destruct (lem_a_gt_b_le_c (bv - 1) cv (bv + 1)) as [n0 ?]; try omega.
  exists (S n0).
  apply Tarai_a_gt_b_1 with bv; auto; try omega.
  apply Tarai_a_le_b; omega.

  destruct IHm as [n0 ?].

  rewrite inj_S.
  replace (bv + Zsucc (Z_of_nat (S m))) with (bv + Z_of_nat (S m) + 1) by omega.

  destruct (Z_le_dec (bv - 1) cv).
  destruct (lem_a_gt_b_le_c (bv + Z_of_nat (S m)) cv (bv + Z_of_nat (S m) + 1)) as [n1 ?]; try omega.

  exists (S (n0 + n1)).
  apply Tarai_a_gt_b_2 with (bv + Z_of_nat (S m)) cv  (bv + Z_of_nat (S m) + 1); auto; try omega.
  apply lem_n_indep.
  replace (bv + Z_of_nat (S m) + 1 - 1) with (bv + Z_of_nat (S m)) by omega.
  auto.
  apply Tarai_a_le_b; auto.
  apply Tarai_a_le_b; omega.
  replace (n0 + n1)%nat with (n1 + n0)%nat by omega.
  apply lem_n_indep.
  auto.

  destruct (lem_a_gt_b_le_c (bv - 1) cv (bv + Z_of_nat (S m) + 1)) as [n1 ?]; try omega.
  exists (S (n0 + n1)).
  apply Tarai_a_gt_b_1 with (bv + Z_of_nat (S m)); auto; try omega.
  apply lem_n_indep.
  replace (bv + Z_of_nat (S m) + 1 - 1) with (bv + Z_of_nat (S m)) by omega.
  auto.
  replace (n0 + n1)%nat with (n1 + n0)%nat by omega.
  auto using lem_n_indep.
Qed. 

Lemma lem_a_gt_b_gt_c : forall av bv cv, av > bv -> bv > cv -> 
   exists n , Tarai_value n (Some av) (Some bv) (Some cv) av.
Proof. 
  intros. 
  assert (exists d: nat, av - 1 - bv=Z_of_nat d). 
  apply Z_of_nat_complete. 
  omega. 

  destruct H1 as [m]. 
  replace av with (bv+Z_of_nat (S m)).
  apply lem1_a_gt_b_gt_c; auto.
  rewrite inj_S.
  omega. 
Qed. 

Theorem tarai3_terminates : forall av bv cv,
  exists n, exists v, Tarai_value n (Some av) (Some bv) (Some cv) v. 
Proof.
  intros.
  assert (av <= bv \/ av > bv /\ bv <= cv \/ av > bv /\ bv > cv) by omega.
  destruct H as [?|[?|?]].
 
 exists 0%nat. exists bv.
  apply Tarai_a_le_b; auto.

  destruct (lem_a_gt_b_le_c av bv cv) as [n0 ?]; try tauto.
  exists n0. exists cv. auto.

  destruct (lem_a_gt_b_gt_c av bv cv) as [n0 ?]; try tauto.
  exists n0. exists av. auto.
Qed.
