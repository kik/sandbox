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

Inductive Tarai_value (n: nat) (a b c: option Z) (v: Z) : Prop :=
| Tarai_a_le_b (av bv: Z)
     (Hle: av <= bv) (Hv: bv = v) (Ha: a = Some av) (Hb: b = Some bv): Tarai_value n a b c v
| Tarai_a_gt_b_1 (av bv cv: Z) (n': nat) (Hgt: av > bv)
     (Ha: a = Some av) (Hb: b = Some bv) (Hc: c = Some cv)
     (Hn: n = S n')
     (v1: Z)
     (Hle2: v1 <= v)
     (Hrec1: Tarai_value n' (Some (av-1)) b c v1)
     (Hrec2: Tarai_value n' (Some (bv-1)) c a v)
| Tarai_a_gt_b_2 (av bv cv: Z) (n': nat) (Hgt: av > bv)
     (Ha: a = Some av) (Hb: b = Some bv) (Hc: c = Some cv)
     (Hn: n = S n')
     (v1 v2 v3: Z)
     (Hle2: ~v1 <= v2)
     (Hrec1: Tarai_value n' (Some (av-1)) b c v1)
     (Hrec2: Tarai_value n' (Some (bv-1)) c a v2)
     (Hrec3: Tarai_value n' (Some (cv-1)) a b v3)
     (Hrec4: Tarai_value n' (Some v1)
                                   (Some v2)
                                   (Some v3) v): Tarai_value n a b c v.

Lemma lem_saficient:
  forall n a b c v, Tarai_value n a b c v -> ntarai3 n a b c = Some v.
Proof.
  intros.
  unfold ntarai3.
  induction H;
    destruct n;
    rewrite Ha;
    rewrite Hb;
    destruct (Z_le_dec av bv); try congruence; try contradiction.
  fold ntarai3 in * |- *.
  rewrite Hc.
  inversion Hn.
  rewrite <- Ha. rewrite <- Hb. rewrite <- Hc.
  rewrite (IHTarai_value1).
  rewrite (IHTarai_value2).
  destruct n'; simpl; destruct (Z_le_dec v1 v); auto; contradiction.
  fold ntarai3 in * |- *.
  rewrite Hc.
  congruence.
Qed.

Lemma lem_invert:
  forall n a b c v, ntarai3 n a b c = Some v -> Tarai_value n a b c v.
Proof.
  unfold ntarai3.
  induction n.
  intros.
  destruct a as [av|]; [|congruence].
  destruct b as [bv|]; [|congruence].
  destruct (Z_le_dec av bv).
  apply Tarai_a_le_b with av bv; auto. congruence.
  inversion H.  
  destruct a as [av|]; [|congruence].
  destruct b as [bv|]; [|congruence].
  destruct (Z_le_dec av bv).
  intros.
  apply Tarai_a_le_b with av bv; auto. congruence.
  intros.
  destruct c as [cv|]; [|congruence].
  fold ntarai3 in * |- *.
  generalize (Tarai_a_gt_b_1 (S n) (Some av) (Some bv) (Some cv) v av bv cv n).
  generalize (Tarai_a_gt_b_2 (S n) (Some av) (Some bv) (Some cv) v av bv cv n).
  generalize (IHn (Some (av - 1)) (Some bv) (Some cv)).
  generalize (IHn (Some (bv - 1)) (Some cv) (Some av)).
  generalize (IHn (Some (cv - 1)) (Some av) (Some bv)).
  intros.
  destruct n.
  destruct (ntarai3 0 (Some (av - 1)) (Some bv) (Some cv)) as [v1|].
  destruct (ntarai3 0 (Some (bv - 1)) (Some cv) (Some av)) as [v2|].
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply H4 with v1; auto.
  omega.
  congruence.
  congruence.
  inversion H.
  inversion H.
  destruct (ntarai3 (S n) (Some (av - 1)) (Some bv) (Some cv)) as [v1|].
  destruct (ntarai3 (S n) (Some (bv - 1)) (Some cv) (Some av)) as [v2|].
  destruct (ntarai3 (S n) (Some (cv - 1)) (Some av) (Some bv)) as [v3|].
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply H4 with v1; auto.
  omega.
  congruence.
  apply H3 with v1 v2 v3; auto.
  omega.
  apply IHn.
  simpl.
  destruct (Z_le_dec v1 v2).
  contradiction.
  auto.
  simpl in H.
  destruct (Z_le_dec v1 v2).
  apply H4 with v1; auto.
  omega.
  congruence.
  inversion H.
  inversion H.
  inversion H.
Qed.

Lemma lem_n_indep : forall n m a b c v,
    Tarai_value n a b c v -> Tarai_value (n + m) a b c v.
Proof.
  induction n.
  intros.
  destruct H.
     apply Tarai_a_le_b with av bv; auto.
     inversion Hn.
     inversion Hn.
  intros.
  destruct H.
     apply Tarai_a_le_b with av bv; auto.
     inversion Hn. rewrite <- H2 in * |- *.
     replace (S n + m)%nat with (S (n + m)) by auto.
     apply Tarai_a_gt_b_1 with av bv cv (n + m)%nat v1; auto.
     inversion Hn. rewrite <- H4 in * |- *.
     replace (S n + m)%nat with (S (n + m)) by auto.
     apply Tarai_a_gt_b_2 with av bv cv (n + m)%nat v1 v2 v3; auto.
Qed.

Lemma lem1_a_gt_b_le_c : forall bv cv m, bv <= cv ->
  exists n, Tarai_value n (Some (bv + Z_of_nat(S m))) (Some bv) (Some cv) cv.
Proof.
  induction m. 
  intros.
  exists 1%nat.
  replace (Z_of_nat 1) with 1 by auto.

  apply Tarai_a_gt_b_1 with (bv + 1) bv cv 0%nat bv; auto.
  omega.
  apply Tarai_a_le_b with (bv + 1 - 1) bv; auto.
  omega.
  apply Tarai_a_le_b with (bv - 1) cv; auto.
  omega.

  intros.
  destruct (IHm H) as [n' Hn'].
  exists (S n').

  apply Tarai_a_gt_b_1 with (bv + Z_of_nat (S (S m))) bv cv n' cv; auto.
  rewrite inj_S. omega.
  omega.
  rewrite inj_S.
  replace (bv + Zsucc (Z_of_nat (S m)) - 1) with (bv + Z_of_nat (S m)) by omega.
  auto.

  apply Tarai_a_le_b with (bv - 1) cv; auto.
  omega.
Qed. 

Lemma lem_a_gt_b_le_c : forall av bv cv,  av>bv -> bv<=cv -> 
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

Lemma lem1_a_gt_b_gt_c : forall bv cv,  bv > cv ->
  forall m,  exists n, Tarai_value n (Some (bv + Z_of_nat (S m))) (Some bv) (Some cv) (bv + Z_of_nat (S m)).
Proof.
  induction m.
  replace (Z_of_nat 1) with 1 by auto.
  destruct (Z_le_dec (bv - 1) cv).

  destruct (lem_a_gt_b_le_c bv cv (bv+1)) as [n0 ?]; try omega.
  exists (S n0).

  apply Tarai_a_gt_b_2 with (bv + 1) bv cv n0 bv cv (bv + 1); auto.
  omega.
  apply Tarai_a_le_b with (bv + 1 - 1) bv; auto; omega.
  apply Tarai_a_le_b with (bv - 1) cv; auto; omega.
  apply Tarai_a_le_b with (cv - 1) (bv + 1); auto; omega.

  destruct (lem_a_gt_b_le_c (bv - 1) cv (bv + 1)) as [n0 ?]; try omega.
  exists (S n0).
  apply Tarai_a_gt_b_1 with (bv + 1) bv cv n0 bv; auto; try omega.
  apply Tarai_a_le_b with (bv + 1 - 1) bv; auto; omega.

  destruct IHm as [n0 ?].

  rewrite inj_S.
  replace (bv + Zsucc (Z_of_nat (S m))) with (bv + Z_of_nat (S m) + 1) by omega.

  destruct (Z_le_dec (bv - 1) cv).
  destruct (lem_a_gt_b_le_c (bv + Z_of_nat (S m)) cv (bv + Z_of_nat (S m) + 1)) as [n1 ?]; try omega.

  exists (S (n0 + n1)).
  apply Tarai_a_gt_b_2 with (bv + Z_of_nat (S m) + 1) bv cv (n0 + n1)%nat
                                    (bv + Z_of_nat (S m)) cv  (bv + Z_of_nat (S m) + 1); auto.
  omega. omega.

  apply lem_n_indep.
  replace (bv + Z_of_nat (S m) + 1 - 1) with (bv + Z_of_nat (S m)) by omega.
  auto.
  apply Tarai_a_le_b with (bv - 1) cv; auto.
  apply Tarai_a_le_b with (cv -1) (bv + Z_of_nat (S m) + 1); auto.
  omega.

  replace (n0 + n1)%nat with (n1 + n0)%nat by omega.
  apply lem_n_indep.
  auto.

  destruct (lem_a_gt_b_le_c (bv - 1) cv (bv + Z_of_nat (S m) + 1)) as [n1 ?]; try omega.

  exists (S (n0 + n1)).
  apply Tarai_a_gt_b_1 with (bv + Z_of_nat (S m) + 1) bv cv (n0 + n1)%nat
                                    (bv + Z_of_nat (S m)); auto.
  omega. omega.
  apply lem_n_indep.
  replace (bv + Z_of_nat (S m) + 1 - 1) with (bv + Z_of_nat (S m)) by omega.
  auto.

  replace (n0 + n1)%nat with (n1 + n0)%nat by omega.
  apply lem_n_indep.
  auto.
Qed. 

Lemma lem_a_gt_b_gt_c : forall av bv cv, av>bv -> bv>cv -> 
   exists n ,  Tarai_value n (Some av) (Some bv) (Some cv) av.
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
  assert (forall x y, x <= y \/ x > y).
  intros. omega.
 
  destruct (H av bv).
  exists 0%nat. exists bv.
  apply Tarai_a_le_b with av bv; auto.

  destruct (H bv cv).
  generalize (lem_a_gt_b_le_c av bv cv H0 H1).
  intros [n0 ?].
  exists n0. exists cv. auto.

  generalize (lem_a_gt_b_gt_c av bv cv H0 H1).
  intros [n0 ?].
  exists n0. exists av. auto.
Qed.
