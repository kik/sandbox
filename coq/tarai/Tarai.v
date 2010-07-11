Require Import ZArith.
Require Import List.
Require Import Tarai_Base.
Require Import Denotation.
Require Import Util.

Open Scope Z_scope.

Inductive Le : dZ -> dZ -> Prop :=
| LE x y: x <= y -> Le (V x) (V y).

Definition Vz := @V Z.

Inductive Tarai_X (k: nat) : VdZ -> Z -> Prop :=
| TX head x tail
  (Hmax: forall i y, In_n i y head -> y <= x)
  (Hlen: length head = k):
  Tarai_X k (map Vz head ++ (V x)::tail) x.

Inductive Tarai_Y (n: nat) (k: nat) : VdZ -> Z -> Prop :=
| TY head x tail v
  (Hterm: ntarai n (head++(V x)::tail) = V v)
  (Hle: v <= x)
  (Hlen: length head = k):
  Tarai_Y n k (head ++ (V x)::tail) x.

Open Scope nat_scope.

Lemma remove_V: forall v,
   (forall i y, In_n i y v -> y <> B) ->
   exists v', map Vz v' = v.
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
   rewrite <- (map_length Vz v').
   congruence.
Qed.

Section X_functions.
  Open Scope Z_scope.
  Lemma sigma_X: forall k v x, Tarai_X (S k) v x -> Tarai_X (S k) (sigma v) x.
  Proof.
    intros.
    destruct H.
    destruct head.
    inversion Hlen.
    simpl.
    replace (V (z-1)::map Vz head++V x::tail) with (map Vz (z-1::head)++V x::tail) by auto.
    apply (TX (S k) (z-1::head) x tail).
    intros.
    destruct i; simpl in H.
    assert (z <= x).
    apply Hmax with O.
    simpl. auto.
    omega.
    apply Hmax with (S i).
    simpl. auto.
    simpl in * |- *. auto.
  Qed.
  
  Lemma tau_X: forall k v x, Tarai_X (S k) v x -> Tarai_X k (tau v) x.
  Proof.
    intros.
    inversion H.
    destruct head.
    simpl in Hlen.
    congruence.
    simpl.
    rewrite <- ass_app.
    apply (TX k head x (tail ++ V z::nil)).
    intros.
    apply Hmax with (S i).
    simpl. auto.
    simpl in Hlen.
    congruence.
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
    rewrite (app_length).
    simpl.
    rewrite map_length.
    omega.
  Qed.
End Length.

Lemma Y_indep: forall r r' k v x, (r <= r')%nat ->
  Tarai_Y r k v x -> Tarai_Y r' k v x.
Proof.
  intros.
  inversion H0.
  apply (TY r' k head x tail v0); auto.
  intros.
  specialize (ntarai_continuous_n r r' (head++V x::tail) H).
  intros.
  rewrite Hterm in H3.
  inversion H3.
  auto.
Qed.

Section X_Y.
  Open Scope nat_scope.
  Variable n: nat.
  Variable IHn: forall m,
    m < n -> forall v x, Tarai_X (S m) v x ->
    exists n : nat, Tarai_Y n (S m) v x.

  Lemma ntarai_make_aux_Y: forall n' m k w v x,
    m < n ->
    In_n k v (ntarai_make_aux w n') ->
    Tarai_X (m+k+1) w x ->
    exists r,
    Tarai_X (S m) v x /\ Tarai_Y r (S m) v x.
  Proof.
    intros.
    assert (Tarai_X (S m) v x).
    apply ntarai_make_aux_X with n' k w; auto.
    destruct (IHn m H v x H2) as [r ?].
    exists r.
    auto.
  Qed.

  Variable w: VdZ.
  Variable x: Z.
  Variable HX: Tarai_X n w x.
  Variable IHsigma: exists r, Tarai_Y r n (sigma w) (x - 1)%Z.

  Lemma ntarai_make_Y_aux: forall k v,
    1 <= k < n ->
    In_n k v (ntarai_make w) ->
    exists r,
    Tarai_X (n - k) v x /\ Tarai_Y r (n - k) v x.
  Proof.
    intros.
    replace (n - k) with (S (n - k - 1)) by omega.
    apply ntarai_make_aux_Y with (length w) k w.
    omega.
    auto.
    replace (n - k - 1 + k + 1) with n by omega.
    apply HX.
  Qed.

  Lemma ntarai_make_Y: exists r, forall k v,
      1 <= k < n ->
      In_n k v (ntarai_make w) ->
     Tarai_X (n - k) v x /\ Tarai_Y r (n - k) v x.
  Proof.
     intros.
     generalize (X_length n w x HX).
     intros.
     generalize (take_max n (fun k r => k < 1 \/ forall v, In_n k v (ntarai_make w) ->
                                       Tarai_X (n - k) v x /\ Tarai_Y r (n - k) v x)).
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
     destruct (In_n_exists (S k) (ntarai_make w)) as [v ?].
     rewrite (ntarai_make_length w).
     omega.
     destruct (ntarai_make_Y_aux (S k) v) as [r ?]; auto.
     omega.
     exists r.
     right.
     intros.
     rewrite (In_n_unique (S k) (ntarai_make w) v0 v); auto.
     exists x0.
     intros.
     destruct (H0 k).
     omega.
     apply False_ind. omega.
     auto.
  Qed.

  Lemma ntarai_map_Y: exists r, forall r' k v,
      1 < n ->
      k < n -> r <= r' ->
      In_n k v (map (ntarai r') (ntarai_make w)) -> Le v  (V x) /\ (k+1 = n -> v = (V x)).
  Proof.
     intros.
     generalize (X_length n w x HX).
     intros.
     destruct ntarai_make_Y as [r ?]; auto.
     destruct IHsigma as [r0 ?].
     exists (r + r0 + 1).
     intros.
     destruct (In_n_exists k (ntarai_make w)) as [v' ?].
     rewrite (ntarai_make_length w).
     omega.
     destruct k.
        assert (ntarai r' v' = v).
        apply In_n_map with 0 (ntarai_make w); auto.
        unfold ntarai_make in H6.
        replace (length w) with (S (length w - 1)) in H6 by omega.
        simpl in H6.
        rewrite <- H6 in H1.
        assert (r0 <= r') by omega.
        generalize (Y_indep r0 r' n v' (x - 1)%Z H8 H1).
        intro.
        inversion H9.
        replace v with (V v0) by congruence.
        constructor. constructor. omega.
        intros.
        apply False_ind. omega.
     assert (1 <= (S k) < n) by omega.
     specialize (H0 (S k) v' H7 H6).
     destruct H0.
     assert (r <= r') by omega.
     generalize (Y_indep r r' (n - S k) v' x H9 H8).
     intros.
     inversion H10.
     assert (VdZ_le tail tail) by auto with tarai.
     rewrite <- H12 in Hterm.
     rewrite H11 in Hterm.
     destruct (In_n_exists (S k) (map (ntarai r') (ntarai_make w))) as [v'' ?].
     rewrite map_length.
     rewrite (ntarai_make_length w).
     omega.
     generalize (In_n_map (ntarai r') (S k) (ntarai_make w) v' v H6 H5).
     intros.
     rewrite Hterm in H15.
     rewrite <- H15.
     constructor. constructor.
     auto.
     intros.
     assert (n - S k = 1) by omega.
     rewrite H17 in * |- *.
     assert (ntarai 1 v' = V x).
     inversion H0.
     destruct head0 as [|x' ?].
     simpl in Hlen0. congruence.
     destruct head0.
     assert (x' <= x)%Z.
     apply Hmax with 0.
     simpl. auto.
     unfold ntarai. simpl.
     destruct (Z_le_dec x' x); [auto|contradiction].
     simpl in Hlen0.
     congruence.
     assert (1 <= r') by omega.
     generalize (ntarai_continuous_n 1 r' v' H19).
     rewrite H18. rewrite Hterm.
     intros.
     inversion H20.
     auto.
  Qed.

  Lemma ntarai_map_X:
    1 < n ->
    exists r, forall r', r <= r' ->
      Tarai_X (n-1) (map (ntarai r') (ntarai_make w)) x.
  Proof.
    intros.
    generalize (X_length n w x HX).
    destruct ntarai_map_Y as [r0 ?].
    exists r0.
    intros.
    apply make_X.
    destruct (In_n_exists (n-1) (map (ntarai r') (ntarai_make w))).
    rewrite (map_length).
    rewrite (ntarai_make_length).
    omega.
    destruct (H0 r' (n-1) x0).
    auto. omega. omega. auto. auto.
    rewrite <- H5.
    auto. omega.
    intros.
    destruct (H0 r' i y).
    auto. omega. omega. auto. auto.
  Qed.     

  Lemma VdZ_split: forall u v w, VdZ_le (u++v) w ->
    exists u', exists v', u' ++ v' = w /\ VdZ_le u u' /\ VdZ_le v v'.
  Proof.
    induction u.
    exists nil. exists w0.
    simpl in * |- *.
    auto with tarai.
    intros.
    destruct w0.
    simpl in H. inversion H.
    simpl in H. inversion H.
    destruct (IHu  v w0) as [u' [v' ?]]; auto.
    exists (d::u'). exists v'.
    constructor; auto.
    rewrite <- app_comm_cons.
    destruct H6. congruence.
    constructor.
    constructor; auto. tauto. tauto.
  Qed.

  Lemma VdZ_le_length: forall v w, VdZ_le v w -> length v = length w.
  Proof.
    induction v.
    intros.
    inversion H.
    auto.
    intros.
    inversion H.
    simpl.
    auto.
  Qed.

  Lemma Y_contin: forall n k v v' x,
    Tarai_Y n k v x -> VdZ_le v v' -> Tarai_Y n k v' x.
  Proof.
    intros.
    generalize (ntarai_continuous n0 v v' H0).
    intros.
    inversion H.
    destruct (VdZ_split head (V x0::tail) v') as [head' [t ?]].
    rewrite <- H3. rewrite <- H2 in H0. auto.
    destruct H4. destruct H5.
    destruct t as [|x2 tail'].
    inversion H6.
    inversion H6.
    rewrite <- H4. inversion H10.
    apply (TY n0 k head' x0 tail' v0).
    rewrite <- H2 in H1.
    rewrite H3 in H1.
    rewrite Hterm in H1.
    inversion H1.
    rewrite H17.
    rewrite <- H4.
    rewrite <- H14.
    auto.
    auto.
    generalize (VdZ_le_length head head' H5).
    intro.
    rewrite <- Hlen.
    auto.
  Qed.

  Lemma ntarai_Y:
    1 < n ->
    exists r,
      Tarai_Y r (n-1) (map (ntarai r) (ntarai_make w)) x.
  Proof.
    intros.
    destruct ntarai_map_X as [r0 ?].
    auto.
    assert (n - 2 < n) by omega.
    destruct (IHn (n - 2) H1 (map (ntarai r0) (ntarai_make w)) x) as [r1 ?].
    replace (S (n - 2)) with (n - 1) by omega.
    apply H0. omega.
    exists (r0 + r1).
    apply Y_indep with (r1). omega.
    replace (S (n - 2)) with (n - 1) in H2 by omega.
    apply Y_contin with (map (ntarai r0) (ntarai_make w)); auto.
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
  destruct head as [|x1].
  inversion Hlen.
  destruct head as [|x2].
  inversion Hlen.
  exists 1%nat.
  apply (TY 1 1 (V x1:: nil) x tail x).
  assert (x1 <= x).
  apply Hmax with 0%nat.
  red.
  auto.
  unfold ntarai.
  simpl.
  destruct (Z_le_dec x1 x); [auto|contradiction].
  omega.
  simpl.
  auto.
  destruct (Z_le_dec x1 x2).
  exists 1%nat.
  simpl.
  apply (TY 1 (S n) (V x1::V x2::map Vz head) x tail x2).
  unfold ntarai.
  simpl.
  destruct (Z_le_dec x1 x2); [auto|contradiction].
  apply Hmax with 1%nat.
  simpl.
  auto.
  simpl. rewrite map_length.
  simpl in Hlen. auto.

  assert (exists m : nat, x1 - x2 - 1 = Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H3 as [m ?].
  replace x1 with (x2 + 1 + Z_of_nat m)%Z in * |- * by omega.
  clear H3.

  induction m. Focus 2.
  simpl. replace (x1 + 1 + 0) with (x1 + 1) by omega.
  Focus 2.
  destruct n.
  apply False_ind. omega.

Lemma ntarai_map_X: forall n f v,
  Tarai_X (S n) v ->
  (forall k v, k < n -> Tarai_X k v -> exists r, Tarai_Y r k v) ->
  Tarai_X n (map f (ntarai_make v)).
