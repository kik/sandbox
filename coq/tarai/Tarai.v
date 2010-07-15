Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Tarai_Base.
Require Import Denotation.
Require Import Util.

Open Scope Z_scope.

Inductive Le : dZ -> dZ -> Prop :=
| LE x y: x <= y -> Le (V x) (V y).

Definition mapV := map (@V Z).
Definition mapB {A} : list A -> VdZ := map (fun _ => B).

Inductive Tarai_X (k: nat) (vec: VdZ) (x: Z): Prop :=
| TX
  (Hin: In_n k (V x) vec)
  (Hmax: forall i y, (i < k)%nat -> In_n i y vec -> Le y (V x)):
  Tarai_X k vec x.

Inductive Tarai_Y (r: nat) (k: nat) (vec: VdZ) (x: Z): Prop :=
| TY (v: Z)
  (Hterm: ntarai r vec = V v)
  (Hle: v <= x):
  Tarai_Y r k vec x.

Open Scope nat_scope.

(*
Lemma remove_V: forall v,
   (forall i y, In_n i y v -> y <> B) ->
   exists v', mapV v' = v.
Proof.
   induction v.
   exists nil.
   auto.
   intros.
   destruct IHv.
   intros.
   apply H with (S i).
   auto.
   assert (a <> B).
   apply H with 0.
   simpl. auto.
   destruct a; try congruence.
   exists (z::x).
   simpl.
   rewrite H0.
   auto.
Qed.

Lemma make_X: forall k x v,
   In_n k (V x) v ->
   (forall i y, i <= k -> In_n i y v -> Le y (V x)) ->
   Tarai_X k v x.
Proof.
   intros.
   generalize (In_n_length k v (V x) H).
   generalize (firstn_length k v).
   intros.
   rewrite (Min.min_l k (length v)) in H1; try omega.
   assert (forall i y, In_n i y (firstn k v) -> Le y (V x)).
   intros.
   assert (In_n i y v).
   apply (In_n_firstn_2 k i v y H3).
   generalize (In_n_length i (firstn k v) y H3).
   intros.
   apply H0 with i; auto.
   omega.
   destruct (remove_V (firstn k v)) as [v' ?].
   intros.
   destruct y; try congruence.
   specialize (H3 i B H4).
   inversion H3.
   generalize (In_n_split k v (V x) H).
   rewrite <- H4.
   intros.
   rewrite <- H5.
   apply (TX k v' x (skipn (S k) v)).
   intros.
   assert (Le (V y) (V x)).
   apply H3 with i.
   rewrite <- H4.
   apply In_n_map_2. auto.
   inversion H7. auto.
   rewrite <- H1.
   rewrite <- H4.
   unfold mapV.
   rewrite map_length.
   congruence.
Qed.
*)

Section X_functions.
  Open Scope Z_scope.
  Lemma sigma_X: forall k v x, Tarai_X (S k) v x -> Tarai_X (S k) (sigma v) x.
  Proof.
    intros.
    destruct H.
    destruct v. contradiction.
    constructor.
    auto.
    intros.
    destruct i.
    assert (Le d (V x)).
    apply Hmax with O; simpl; auto.
    destruct H1.
    simpl in H0. rewrite H0.
    constructor.  omega.
    apply Hmax with (S i); simpl in * |- *; auto.
  Qed.
  
  Lemma tau_X: forall k v x, Tarai_X (S k) v x -> Tarai_X k (tau v) x.
  Proof.
    intros.
    destruct H.
    destruct v.
    contradiction.
    simpl.
    simpl in Hin.
    constructor.
    apply In_n_app; auto.
    intros.
    apply Hmax with (S i).
    omega.
    simpl.
    apply In_n_app_2 with (d::nil); auto.
    apply In_n_length in Hin.
    apply lt_trans with k; auto.
  Qed.

  Lemma ntarai_make_aux_X: forall n m k w v x,
    In_n k v (ntarai_make_aux w n) ->
    Tarai_X (m+k+1)%nat w x -> Tarai_X (S m) v x.
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
    replace (S m) with (m + 0 + 1)%nat by omega.
    auto.
    simpl in H.
    apply IHn with k (tau w); auto.
    apply tau_X.
    replace (S (m + k + 1)) with (m + S k + 1)%nat by omega.
    auto.
  Qed.

  Lemma ntarai_make_X: forall n k w v x,
    In_n k v (ntarai_make w) ->
    Tarai_X (n+k+1)%nat w x -> Tarai_X (S n) v x.
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

  Lemma X_length: forall k w x, Tarai_X k w x -> k < length w.
  Proof.
    intros.
    destruct H.
    apply In_n_length with (V x).
    auto.
  Qed.
End Length.

Lemma Y_indep: forall r r' k v x, (r <= r')%nat ->
  Tarai_Y r k v x -> Tarai_Y r' k v x.
Proof.
  intros.
  destruct H0.
  apply TY with v0; auto.
  apply ntarai_continuous_nv with r; auto.
Qed.

Lemma Y_contin: forall n k v v' x,
  Tarai_Y n k v x -> VdZ_le v v' -> Tarai_Y n k v' x.
Proof.
  intros.
  generalize (ntarai_continuous n v v' H0).
  intros.
  destruct H.
  apply TY with v0; auto.
  rewrite Hterm in H1.
  inversion H1.
  auto.
Qed.

Section X_Y.
  Open Scope nat_scope.
  Variable nc: nat.
  Variable wc: VdZ.
  Variable xc: Z.
  Variable HX: Tarai_X (S nc) wc xc.
  Variable IHn: forall m,
    m < nc -> forall v x, Tarai_X (S m) v x ->
    exists n : nat, Tarai_Y n (S m) v x.
  Variable IHsigma: exists r, exists y, (y <= xc)%Z /\ ntarai r (sigma wc) = V y%Z.

  Lemma ntarai_make_aux_Y: forall n m k w v x,
    m < nc ->
    In_n k v (ntarai_make_aux w n) ->
    Tarai_X (m+k+1) w x ->
    exists r,
    Tarai_X (S m) v x /\ Tarai_Y r (S m) v x.
  Proof.
    intros.
    assert (Tarai_X (S m) v x).
    apply ntarai_make_aux_X with n k w; auto.
    destruct (IHn m H v x H2) as [r ?].
    exists r.
    auto.
  Qed.

  Lemma ntarai_make_Y_aux: forall k v,
    1 <= k <= nc ->
    In_n k v (ntarai_make wc) ->
    exists r,
    Tarai_X (S nc - k) v xc /\ Tarai_Y r (S nc - k) v xc.
  Proof.
    intros.
    replace (S nc - k) with (S (S nc - k - 1)) by omega.
    apply ntarai_make_aux_Y with (length wc) k wc.
    omega.
    auto.
    replace (S nc - k - 1 + k + 1) with (S nc) by omega.
    apply HX.
  Qed.

  Lemma ntarai_make_Y: exists r, forall k v,
      1 <= k <= nc ->
      In_n k v (ntarai_make wc) ->
     Tarai_X (S nc - k) v xc /\ Tarai_Y r (S nc - k) v xc.
  Proof.
     intros.
     generalize (X_length (S nc) wc xc HX).
     intros.
     generalize (take_max (S nc) (fun k r => k < 1 \/ forall v, In_n k v (ntarai_make wc) ->
                                       Tarai_X (S nc - k) v xc /\ Tarai_Y r (S nc - k) v xc)).
     intros.
     destruct H0.
     intros.
     destruct H1; auto.
     right.
     intros.
     constructor.
     destruct (H1 v); auto.
     apply Y_indep with r; auto.
     destruct (H1 v); auto.
     destruct k.
     exists 0.
     left; auto.
     intros.
     destruct (In_n_exists (S k) (ntarai_make wc)) as [v ?].
     rewrite (ntarai_make_length wc).
     omega.
     destruct (ntarai_make_Y_aux (S k) v) as [r ?]; auto.
     omega.
     exists r.
     right.
     intros.
     rewrite (In_n_unique (S k) (ntarai_make wc) v0 v); auto.
     exists x.
     intros.
     destruct (H0 k).
     omega.
     apply False_ind. omega.
     auto.
  Qed.

  Lemma ntarai_map_Y: exists r, forall r' k v,
      0 < nc ->
      k <= nc -> r <= r' ->
      In_n k v (map (ntarai r') (ntarai_make wc)) -> Le v  (V xc) /\ (k+1 = S nc -> v = (V xc)).
  Proof.
     intros.
     generalize (X_length (S nc) wc xc HX).
     intros.
     destruct ntarai_make_Y as [r ?]; auto.
     destruct IHsigma as [r0 ?].
     exists (r + r0 + 1).
     intros.
     destruct (In_n_exists k (ntarai_make wc)) as [v' ?].
     rewrite (ntarai_make_length wc).
     omega.
     destruct k.
        assert (ntarai r' v' = v).
        apply In_n_map with 0 (ntarai_make wc); auto.
        destruct H1.
        destruct H1.
        unfold ntarai_make in H6.
        replace (length wc) with (S (length wc - 1)) in H6 by omega.
        simpl in H6.
        constructor.
        rewrite <- H6 in H8.
        assert (r0 <= r') by omega.
        generalize (ntarai_continuous_n r0 r' v' H9).
        intro.
        rewrite H8 in H10.
        rewrite H7 in H10.
        inversion H10.
        constructor.
        omega.
        intro. apply False_ind. omega.
     assert (1 <= (S k) <=  nc) by omega.
     specialize (H0 (S k) v' H7 H6).
     destruct H0.
     assert (r <= r') by omega.
     generalize (Y_indep r r' (S nc - S k) v' xc H9 H8).
     intros.
     destruct H10.
     destruct (In_n_exists (S k) (map (ntarai r') (ntarai_make wc))) as [v'' ?].
     rewrite map_length.
     rewrite (ntarai_make_length wc).
     omega.
     generalize (In_n_map (ntarai r') (S k) (ntarai_make wc) v' v H6 H5).
     intros.
     rewrite Hterm in H11.
     rewrite <- H11.
     constructor. constructor.
     auto.
     intros.
     assert (S nc - S k = 1) by omega.
     rewrite H13 in * |- *.
     assert (ntarai 1 v' = V xc).
     inversion H0.
     destruct v' as [|x' ?].
     contradiction.
     destruct v' as [|x'' ?].
     contradiction.
     simpl in Hin.
     rewrite <- Hin.
     assert (Le x' (V xc)).
     apply Hmax with O; simpl; auto.
     inversion H14. 
     unfold ntarai. simpl.
     destruct (Z_le_dec x xc); [auto|contradiction].
     assert (1 <= r') by omega.
     generalize (ntarai_continuous_n 1 r' v' H15).
     rewrite Hterm. rewrite H14.
     intro. inversion H16. auto.
  Qed.

  Lemma ntarai_map_X:
    0 < nc ->
    exists r, forall r', r <= r' ->
      Tarai_X nc (map (ntarai r') (ntarai_make wc)) xc.
  Proof.
    intros.
    generalize (X_length (S nc) wc xc HX).
    destruct ntarai_map_Y as [r0 ?].
    exists r0.
    intros.
    constructor.
    destruct (In_n_exists nc (map (ntarai r') (ntarai_make wc))).
    rewrite (map_length).
    rewrite (ntarai_make_length).
    omega.
    destruct (H0 r' nc x).
    auto. omega. omega. auto.
    rewrite <- H5. auto. omega.
    intros.
    destruct (H0 r' i y).
    auto. omega. omega. auto. auto.
  Qed.     

  Lemma ntarai_Y:
    0 < nc ->
    exists r,
      Tarai_Y r nc (map (ntarai r) (ntarai_make wc)) xc.
  Proof.
    intros.
    destruct ntarai_map_X as [r0 ?].
    auto.
    assert (nc - 1 < nc) by omega.
    destruct (IHn (nc - 1) H1 (map (ntarai r0) (ntarai_make wc)) xc) as [r1 ?].
    replace (S (nc - 1)) with nc by omega.
    apply H0. omega.
    exists (r0 + r1).
    apply Y_indep with (r1). omega.
    replace (S (nc - 1)) with nc in H2 by omega.
    apply Y_contin with (map (ntarai r0) (ntarai_make wc)); auto.
    apply map_fcontinuous.
    intro.
    apply ntarai_continuous_n.
    omega.
  Qed.
End X_Y.

Open Scope Z_scope.

Lemma X_impl_Y: forall k v x,
  Tarai_X (S k) v x -> exists n, Tarai_Y n (S k) v x.
Proof.
  intro k. pattern k.
  apply lt_wf_ind.
  intros.
  inversion H0.
  destruct v as [|x1].
  contradiction.
  destruct v as [|x2].
  destruct n; simpl Hin; contradiction.
  destruct n.
  exists 1%nat.
  rewrite <- Hin.
  apply TY with x.
  assert (Le x1 (V x)).
  apply Hmax with O; [omega| simpl; auto].
  inversion H1.
  unfold ntarai. simpl.
  destruct (Z_le_dec x0 x); [auto|contradiction].
  omega.

  assert (Le x1 (V x)).
  apply Hmax with O; [omega|simpl; auto].
  inversion H1.
  assert (Le x2 (V x)).
  apply Hmax with (S O); [omega|simpl; auto].
  inversion H5.

  destruct (Z_le_dec x0 x3).
  exists 1%nat.
  simpl.
  apply TY with x3.
  unfold ntarai.
  simpl.
  destruct (Z_le_dec x0 x3); [auto|contradiction].
  auto.

  assert (exists m : nat, x0 - x3 - 1 = Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H9 as [m ?].
  replace x0 with (x3 + 1 + Z_of_nat m)%Z in * |- * by omega.
  rewrite <- H3 in * |-.
  rewrite <- H7 in * |-.
  clear H9 n0 H6 H7 H8 y0 H5 H2 H3 H4 y.
  induction m.
  simpl in * |- *.
  destruct (ntarai_Y (S n) (V (x3 + 1 + 0)::V x3::v) x) as [r ?].
  auto.
  intros.
  apply H.
  omega.
  auto.
  exists 1%nat.
  simpl.
  replace (x3+1+0-1) with x3 by omega.
  exists x3.
  constructor.
  assert (Le (V (x3 + 1 + 0)) (V x)).
  apply Hmax with 0%nat.
  omega. simpl. auto.
  inversion H2. omega.
  unfold ntarai. simpl.
  destruct (Z_le_dec x3 x3). auto.
  apply False_ind. omega.
  omega.
  exists (S r).
  inversion H2.
  apply  TY with v0.
  unfold ntarai.
  simpl.
  destruct (Z_le_dec (x3 + 1 + 0) x3).
  apply False_ind. omega.
  exact Hterm.
  auto.

  rewrite inj_S in * |- *.
  replace (x3+1+Zsucc(Z_of_nat m)) with (x3 + 2 + Z_of_nat m) in *|-* by omega.
  destruct (ntarai_Y (S n) (V (x3 + 2 + Z_of_nat m)::V x3::v) x) as [r ?].
  auto.
  intros.
  apply H.
  auto. auto.
  assert (forall i y, (i < S (S n))%nat -> In_n i y (V (x3+1+Z_of_nat m)::V x3::v) -> Le y (V x)).
  intros.
  destruct i.
  assert (x3 + 2 + Z_of_nat m <= x).
  inversion H1. auto.
  simpl in H2.
  rewrite H3.
  constructor.
  omega.
  apply Hmax with (S i).
  exact H2. exact H3.
  destruct IHm as [r ?].
  constructor.
  exact Hin. exact H2. exact Hin. exact H2.
  inversion H1. constructor. omega.
  inversion H3.
  exists r. exists v0.
  constructor. auto.
  simpl.
  replace (x3 +2 + Z_of_nat m - 1) with (x3 + 1 + Z_of_nat m) by omega.
  auto.
  omega.

  exists (S r).
  inversion H2.
  apply TY with v0.  
  unfold ntarai.
  simpl.
  destruct (Z_le_dec (x3+2+Z_of_nat m) x3).
  apply False_ind. omega.
  exact Hterm.
  auto.
Qed.

Definition max_In_n k x (vec: list Z) :=
  In_n k x vec /\ forall i y, In_n i y vec -> y <= x.

Lemma max_In_n_ex: forall (vec: list Z), vec <> nil -> exists k, exists x,
  max_In_n k x vec.
Proof.
  induction vec.
  congruence.
  intros.
  destruct vec.
  exists O. exists a.
  constructor. simpl. auto.
  intros.
  destruct i; simpl in H0.
  omega.
  destruct i; contradiction.
  destruct IHvec as [k' [x' ?]].
  congruence.
  destruct (Z_le_dec a x').
  exists (S k'). exists x'.
  destruct H0.
  constructor. auto.
  destruct i.
  simpl. congruence.
  simpl. apply H1.
  exists O. exists a.
  destruct H0.
  constructor. simpl. auto.
  destruct i.
  simpl. intros. omega.
  simpl. intros.
  specialize (H1 i y H2).
  omega.
Qed.

Lemma ntarai_terminate_max_nz: forall kmax xmax (vec: list Z), max_In_n (S kmax) xmax vec ->
  exists r, exists v, ntarai r (mapV vec) = V v /\ v <= xmax.
Proof.
  intros.
  assert (Tarai_X (S kmax) (mapV vec) xmax).
  destruct H.
  constructor.
  apply In_n_map_2. auto.
  intros.
  destruct (In_n_exists i vec).
  generalize (In_n_length (S kmax) vec xmax H).
  omega.
  assert (V x = y).
  apply In_n_map with i vec; auto.
  rewrite <- H4.
  constructor.
  apply H0 with i; auto.
  destruct (X_impl_Y kmax (mapV vec) xmax H0).
  exists x.
  destruct H1.
  exists v.
  auto.
Qed.

Lemma ntarai_terminate_split: forall kmax xmax (vec: list Z), max_In_n kmax xmax vec ->
  (exists r, exists v, ntarai r (mapV vec) = V v /\ v <= xmax) \/ kmax = O.
Proof.
  destruct kmax.
  right. auto.
  left. apply ntarai_terminate_max_nz with kmax. auto.
Qed.

Lemma In_n_map_r:  forall {A B} (f: A->B) k (vec: list A) v,
  In_n k v (map f vec) -> exists v', f v' = v /\ In_n k v' vec.
Proof.
  intros.
  destruct (In_n_exists k vec) as [v' ?].
  apply In_n_length in H.
  rewrite map_length in H.
  auto.
  exists v'.
  constructor; auto.
  apply In_n_map with k vec; auto.
Qed.

Lemma max_tau: forall x0 vec, max_In_n O x0 (x0::vec) ->
  Tarai_X (length vec) (tau (mapV (x0::vec))) x0.
Proof.
  intros.
  assert (In_n (length vec) (V x0) (tau (mapV (x0::vec)))).
  induction vec.
  simpl. auto.
  simpl in * |- *.
  apply IHvec.
  destruct H.
  constructor.
  auto.
  intros.
  destruct i.
  apply H0 with O.
  exact H1.
  apply H0 with (S (S i)).
  exact H1.
  constructor.
  auto.
  intros.
  destruct H.
  simpl in H2.
  assert (In_n i y (mapV vec)).
  apply In_n_app_2 with (V x0::nil); auto.
  unfold mapV. rewrite map_length. auto.
  destruct (In_n_map_r (@V Z) i vec y). auto.
  destruct H5.
  rewrite <- H5.
  constructor.
  apply H3 with (S i).
  auto.
Qed.

Check ntarai_make_aux_X.

Lemma ntarai_max_make_nz: forall x0 vec k v, max_In_n O x0 (x0::vec) ->
  In_n (S k) v (ntarai_make (mapV (x0::vec))) ->
  Tarai_X (length vec - k)%nat v x0.
Proof.
  intros.
  generalize (ntarai_make_aux_X
                    (length (mapV vec))
                    (length vec - k - 1)
                    k
                    (tau (mapV (x0::vec))) v x0 H0).
  simpl.
  intros.
  assert (S k < length (ntarai_make (mapV (x0::vec))))%nat.
  apply In_n_length with v; auto.
  rewrite ntarai_make_length in H2.
  unfold mapV in H2. rewrite map_length in H2.
  simpl in H2.
  replace (length vec - k)%nat with (S (length vec - k - 1))%nat by omega.
  apply H1.
  replace (length vec - k - 1 + k + 1)%nat with (length vec) by omega.
  generalize (max_tau x0 vec H).
  simpl.
  auto.
Qed.

Lemma ntarai_max_map_aux: forall x0 vec k v, max_In_n O x0 (x0::vec) ->
  (0 < length vec)%nat ->
  (exists r, exists y, ntarai r (sigma (mapV (x0::vec))) = V y /\ y <= x0) ->
  In_n k v (ntarai_make (mapV (x0::vec))) ->
  exists r, exists y, ntarai r v = V y /\ y <= x0 /\ (k = length vec -> y = x0).
Proof.
  intros.
  destruct k.
  simpl in * |- *.
  rewrite H2.
  destruct H1 as [r [v' ?]].
  exists r. exists v'.
  destruct H1.
  constructor. auto. constructor. auto.
  intro. omega.
  assert (S k < length (ntarai_make (mapV (x0::vec))))%nat.
  apply In_n_length with v; auto.
  rewrite ntarai_make_length in H3.
  unfold mapV in H3. rewrite map_length in H3.
  simpl in H3.
  apply ntarai_max_make_nz in H2; auto.
  replace (length vec - k)%nat with (S (length vec - k - 1)) in H1 by omega.
  destruct (eq_nat_dec (S k) (length vec)).
  exists 1%nat. exists x0. constructor.
  replace (length vec - k)%nat with 1%nat in H2 by omega.
  destruct H2.
  destruct v as [|x0']. contradiction.
  destruct v as [|x1']. contradiction.
  simpl in Hin. rewrite <- Hin in * |- *.
  assert (Le x0' (V x0)).
  apply Hmax with O. omega. simpl. auto.
  destruct H2.
  unfold ntarai. simpl.
  destruct (Z_le_dec x y); [auto|contradiction].
  constructor. omega. auto.
  replace (length vec - k)%nat with (S (length vec - k - 1)) in H2 by omega.
  apply X_impl_Y in H2.
  destruct H2 as [r [v' ?]].
  exists r. exists v'.
  constructor. auto. constructor. auto.
  intros. contradiction.
Qed.

Lemma ntarai_max_map: forall x0 vec, max_In_n O x0 (x0::vec) ->
  (0 < length vec)%nat ->
  (exists r, exists y, ntarai r (sigma (mapV (x0::vec))) = V y /\ y <= x0) ->
  exists r, forall k v,
  In_n k v (ntarai_make (mapV (x0::vec))) ->
  exists y, ntarai r v = V y /\ y <= x0 /\ (k = length vec -> y = x0).
Proof.
  intros.
  destruct (take_max (S (length vec))
                    (fun k r => forall v, In_n k v (ntarai_make (mapV (x0::vec))) ->
                    exists y, ntarai r v = V y /\ y <= x0 /\ (k = length vec -> y = x0))) as [r ?].
  intros. destruct (H3 v H4).
  exists x.
  destruct H5. constructor; auto.
  apply ntarai_continuous_nv with r; auto.
  intros.
  destruct (In_n_exists k (ntarai_make (mapV (x0::vec)))).
  rewrite ntarai_make_length.
  unfold mapV. rewrite map_length. auto.
  destruct (ntarai_max_map_aux x0 vec k x) as [r [y ?]]; auto.
  exists r.
  intros.
  rewrite <- (In_n_unique k (ntarai_make (mapV (x0::vec))) x v); auto.
  exists y. auto.
  exists r.
  intros.
  apply H2.
  assert (k < length (ntarai_make (mapV (x0::vec))))%nat.
  apply In_n_length with v; auto.
  rewrite ntarai_make_length in H4.
  unfold mapV in H4. rewrite map_length in H4.
  auto.
  auto.
Qed.

Lemma ntarai_max_map_X: forall x0 vec, max_In_n O x0 (x0::vec) ->
  (0 < length vec)%nat ->
  (exists r, exists y, ntarai r (sigma (mapV (x0::vec))) = V y /\ y <= x0) ->
  exists r,
  Tarai_X (length vec) (map (ntarai r) (ntarai_make (mapV (x0::vec)))) x0.
Proof.
  intros.
  destruct (ntarai_max_map x0 vec) as [r ?]; auto.
  exists r.
  constructor.
  destruct (In_n_exists (length vec) (ntarai_make (mapV (x0::vec)))).
  rewrite ntarai_make_length.
  unfold mapV. rewrite map_length. simpl. omega.
  destruct (H2 (length vec) x); auto.
  destruct (In_n_exists (length vec) (map (ntarai r) (ntarai_make (mapV (x0::vec))))).
  rewrite map_length.
  rewrite ntarai_make_length.
  unfold mapV. rewrite map_length. simpl. omega.
  rewrite <- (In_n_map (ntarai r) (length vec) (ntarai_make (mapV (x0::vec))) x x2) in H5; auto.
  destruct H4. rewrite H4 in H5.
  destruct H6.
  rewrite H7 in H5; auto.
  intros.
  destruct (In_n_exists i (ntarai_make (mapV (x0::vec)))).
  rewrite ntarai_make_length.
  unfold mapV. rewrite map_length. simpl. omega.
  destruct (H2 i x); auto.
  rewrite <- (In_n_map (ntarai r) i (ntarai_make (mapV (x0::vec))) x y); auto.
  destruct H6. rewrite H6.
  constructor. tauto.
Qed.
    

Lemma ntarai_max_map_Y: forall x0 vec, max_In_n O x0 (x0::vec) ->
  (0 < length vec)%nat ->
  (exists r, exists y, ntarai r (sigma (mapV (x0::vec))) = V y /\ y <= x0) ->
  exists r,
  Tarai_Y r (length vec) (map (ntarai r) (ntarai_make (mapV (x0::vec)))) x0.
Proof.
  intros.
  destruct (ntarai_max_map_X x0 vec) as [r0 ?]; auto.
  replace (length vec) with (S (length vec - 1)) in H2 by omega.
  apply X_impl_Y in H2.
  destruct H2 as [r1 ?].
  exists (r0 + r1)%nat.
  replace (S (length vec - 1))%nat with (length vec) in H2 by omega.
  apply Y_indep with r1. omega.
  apply Y_contin with (map (ntarai r0) (ntarai_make (mapV (x0::vec)))); auto.
  apply map_fcontinuous.
  red. intro.
  apply ntarai_continuous_n. omega.
Qed.

Lemma ntarai_terminate_1: forall x0 x1 (vec: list Z),
  exists r, exists v, exists k, exists x,
  ntarai r (mapV (x0::x1::vec)) = V v /\ In_n k x (x0::x1::vec) /\ v <= x.
Proof.
  intros.
  destruct (Z_le_dec x0 x1).
  exists 1%nat. exists x1. exists 1%nat. exists x1.
  constructor.
  unfold ntarai. simpl.
  destruct (Z_le_dec x0 x1); [auto|contradiction].
  simpl. omega.

  assert (exists m : nat, x0 - x1 - 1 = Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H as [m ?].
  replace x0 with (x1 + 1 + Z_of_nat m)%Z in * |- * by omega.
  clear n H x0.
  
  induction m.
  simpl.
  destruct (max_In_n_ex (x1+1+0::x1::vec)) as [kmax [xmax Hmax]].
  congruence.
  destruct (ntarai_terminate_split kmax xmax (x1+1+0::x1::vec)); auto.
  destruct H as [r [v ?]].
  exists r. exists v. exists kmax. exists xmax.
  destruct H. destruct Hmax. simpl in * |- *. tauto.

  rewrite H in * |- *.
  clear H.

  replace xmax with (x1 + 1 + 0) in * |- *.
  destruct (ntarai_max_map_Y (x1 + 1 + 0) (x1::vec)) as [r ?]; auto.
  simpl. omega.
  exists 1%nat. exists x1.
  constructor.
  unfold ntarai. simpl.
  destruct (Z_le_dec (x1 + 1 + 0 - 1) x1). auto.
  apply False_ind. omega. omega.
  destruct H.
  exists (S r). exists v. exists O. exists (x1+1+0).
  constructor.
  unfold ntarai. simpl.
  destruct (Z_le_dec (x1+1+0) x1).
  apply False_ind. omega.
  exact Hterm.
  simpl. auto.
  destruct Hmax.
  simpl in H.
  auto.  

  destruct (max_In_n_ex (x1+1+Z_of_nat (S m)::x1::vec)) as [kmax [xmax Hmax]].
  congruence.
  destruct (ntarai_terminate_split kmax xmax (x1+1+Z_of_nat (S m)::x1::vec)); auto.
  destruct H as [r [v ?]].
  exists r. exists v. exists kmax. exists xmax.
  destruct H. destruct Hmax. simpl in * |- *. tauto.

  rewrite H in * |- *.
  clear H.
  replace xmax with (x1 + 1 + Z_of_nat (S m)) in * |- *.
  destruct (ntarai_max_map_Y (x1 + 1 + Z_of_nat (S m)) (x1::vec)) as [r ?]; auto.
  simpl. omega.
  destruct IHm as [r [v [k [x?]]]].
  exists r. exists v.
  rewrite inj_S in *|- *.
  constructor. simpl.
  replace (x1+1+Zsucc (Z_of_nat m)-1) with (x1+1+Z_of_nat m) by omega.
  tauto.
  destruct Hmax.
  destruct H. destruct H2.
  destruct k.
  simpl in H2. omega.
  specialize (H1 (S k) x H2). omega.
  destruct H.
  exists (S r). exists v. exists O. exists (x1+1+Z_of_nat (S m)).
  rewrite inj_S in * |- *.
  constructor.
  unfold ntarai. simpl.
  destruct (Z_le_dec (x1+1+Zsucc (Z_of_nat m)) x1).
  apply False_ind. omega.
  exact Hterm.
  destruct Hmax. auto.
  destruct Hmax.
  simpl in H. auto.
Qed.

Open Scope nat_scope.

Theorem ntarai_termination: forall (vec: list Z), length vec >= 2 ->
  exists r, exists v, ntarai r (mapV vec) = V v.
Proof.
  intros.
  destruct vec as [|x0].
  simpl in H. apply False_ind. omega.
  destruct vec as [|x1].
  simpl in H. apply False_ind. omega.
  destruct (ntarai_terminate_1 x0 x1 vec) as [r [v [k [x ?]]]].
  exists r. exists v.
  tauto.
Qed.
