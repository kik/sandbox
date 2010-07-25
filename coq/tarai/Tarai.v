Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Tarai_Base.
Require Import Denotation.
Require Import Util.

Open Scope Z_scope.

Definition mapV := map (@V Z).

Inductive Tarai_X (k: nat) (vec: VdZ) (x: Z): Prop :=
| TX
  (Hin: In_n k (V x) vec)
  (Hmax: forall i, (i < k)%nat -> exists y, In_n i (V y) vec /\ y <= x):
  Tarai_X k vec x.

Inductive Terminate_with (r: nat) (vec: VdZ) (P: Z -> Prop) : Prop :=
| Terminate (v: Z) (Hterm: ntarai r vec = V v) (HP: P v).

Hint Constructors Tarai_X: tarai.

Open Scope nat_scope.

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

  Lemma mapV_length: forall vec,
    length (mapV vec) = length vec.
  Proof.
    unfold mapV.
    apply map_length.
  Qed.

  Lemma X_length: forall k w x, Tarai_X k w x -> k < length w.
  Proof.
    intros.
    destruct H.
    apply In_n_length with (V x).
    auto.
  Qed.

End Length.

Section X_functions.
  Open Scope Z_scope.

  Lemma sigma_X: forall k v x, Tarai_X (S k) v x -> Tarai_X (S k) (sigma v) x.
  Proof.
    intros.
    inversion H.
    destruct v as [|x0]. contradiction.
    constructor.
    exact Hin.
    intros.
    destruct (Hmax i) as [y [? ?]]; auto.
    destruct i.
    exists (y - 1)%Z.
    rewrite <- H1.
    simpl in * |- *.
    constructor. auto. omega.
    exists y. auto.
  Qed.
  
  Lemma tau_X: forall k v x, Tarai_X (S k) v x -> Tarai_X k (tau v) x.
  Proof.
    intros.
    destruct H.
    destruct v as [|x0]. contradiction.
    constructor.
    apply In_n_app; eauto with tarai.
    intros.
    destruct (Hmax (S i)) as [y [? ?]].
    auto with arith.
    exists y.
    simpl in * |- *.
    constructor.
    auto using  @In_n_app.
    auto.
  Qed.

  Lemma ntarai_make_aux_X: forall n m k w v x,
    In_n k v (ntarai_make_aux w n) ->
    Tarai_X (m+k+1)%nat w x -> Tarai_X (S m) v x.
  Proof.
    induction n.
    intros.
    destruct k; contradiction.
    intros.
    destruct k.
    rewrite H.
    apply sigma_X.
    replace (S m) with (m + 0 + 1)%nat by omega.
    auto.
    apply IHn with k (tau w); eauto with tarai.
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

  Lemma ntarai_X_1: forall w x, Tarai_X 1 w x -> ntarai 1 w = V x.
  Proof.
    intros.
    destruct H.
    destruct w as [|x0]. contradiction.
    destruct w as [|x1]. contradiction.
    rewrite <- Hin.
    destruct (Hmax O) as [y [? ?]]; auto with tarai.
    rewrite <- H.
    unfold ntarai. simpl.
    destruct (Z_le_dec y x); [auto|contradiction].
  Qed.

End X_functions.

Section X_term.
  Open Scope nat_scope.

  Section X_term_induction.
    (* Our goal is proving "exists r, Terminate_with r wc (fun y => y <= x)".   *)
    Variable nc: nat.
    Variable wc: VdZ.
    Variable xc: Z.
    Variable HX: Tarai_X (S nc) wc xc.

    (* Induction Hyp.  smaller n case.  *)
    Variable IHn: forall n v x, n < nc ->
      Tarai_X (S n) v x -> exists r, Terminate_with r v (fun y => y <= x)%Z.

    (* Induction Hyp. smaller wc[0] case.  *)
    Variable IHsigma:
      exists r, Terminate_with r (sigma wc) (fun y => y <= xc)% Z.

    Definition result_le k y := (y <= xc)%Z /\ (k = nc -> y = xc).

    (* If v = (ntarai_make wc)[k],  then there exists r and "tarai r v" termnates. *)
    Lemma X_term_ntarai_make_aux: forall k v,
      k <= nc ->
      In_n k v (ntarai_make wc) ->
      exists r, Terminate_with r v (result_le k).
    Proof.
      intros.
      assert (Tarai_X (S (S nc - k - 1)) v xc).
      apply ntarai_make_X with k wc.
      auto.
      replace (S nc - k - 1 + k + 1) with (S nc) by omega.
      apply HX.
      destruct (eq_nat_dec (k + 1) (S nc)).
      (* k = nc *)
      exists 1. apply Terminate with xc.
      replace (S nc - k - 1) with O in H1 by omega.
      apply ntarai_X_1. auto.
      constructor. omega. auto.
      (* k < nc *)
      destruct k.
      (* k = 0 *)
      destruct IHsigma as [r [v0]].
      exists r. apply Terminate with v0.
      unfold ntarai_make in H0.
      destruct wc. contradiction.
      rewrite H0. auto.
      constructor. auto.
      intros. apply False_ind. omega.
      (* 0 < k < nc *)
      destruct (IHn (S nc - S k - 1) v xc) as [r [v0]].
      omega.
      auto.
      exists r. apply Terminate with v0.
      auto.
      constructor.
      auto.
      intros. apply False_ind. omega.
    Qed.

    Lemma wc_length: (S nc) < length wc.
    Proof.
      apply X_length with xc. auto.
    Qed.

    (* swap forall and exists in X_term_ntarai_make_aux.  *)
    (* There exists r such that if v = (ntarai_make wc)[k] then tarai r v terminates.  *)
    Lemma X_term_ntarai_make: exists r, forall k v,
      k <= nc ->
      In_n k v (ntarai_make wc) ->
      Terminate_with r v (result_le k).
    Proof.
      generalize wc_length.
      intros.
      (* k runs over {0..nc} which is finite.  We can take max r.  *)
      destruct (take_max (S nc) (fun k r => forall v, In_n k v (ntarai_make wc) ->
                                            Terminate_with r v (result_le k))) as [rmax ?].
      (* r independence *)
      intros.
      destruct (H1 v H2) as [v0].
      apply Terminate with v0.
      apply ntarai_continuous_nv with r; auto.
      auto.

      (* r existance *)
      intros.
      destruct (In_n_exists k (ntarai_make wc)) as [v Hin1].
      rewrite (ntarai_make_length wc).
      omega.
      destruct (X_term_ntarai_make_aux k v) as [r ?]; auto.
      omega.
      exists r.
      intros ? Hin2.
      rewrite (In_n_unique _ _ _ _ Hin2 Hin1); auto.

      (* now we have rmax.  *)
      exists rmax.
      intros.
      apply H0.
      omega.
      auto.
    Qed.

    Lemma X_term_ntarai_map_aux:
       0 < nc ->
      exists r,
      Tarai_X nc (map (ntarai r) (ntarai_make wc)) xc.
    Proof.
      generalize wc_length.
      intros.
      destruct X_term_ntarai_make as [r0 ?]; auto.
      exists r0.
      intros.
      constructor.
      apply In_n_intro.
      rewrite map_length. rewrite ntarai_make_length. omega.
      intros.
      destruct (In_n_unmap _ _ _ _ H2) as [v [? ?]].
      destruct (H1 nc v). omega. auto.
      destruct HP.
      rewrite <- H6. congruence. auto.

      intros.
      destruct (In_n_exists i (ntarai_make wc)) as [v].
      rewrite ntarai_make_length. omega.
      destruct (H1 i v) as [v0]. omega. auto.
      exists v0.
      constructor.
      elim Hterm.
      apply In_n_map. auto.
      destruct HP. auto.
    Qed.

    Lemma X_term_ntarai_map:
      0 < nc ->
      exists r,
      Terminate_with r (map (ntarai r) (ntarai_make wc)) (fun y => y <= xc)%Z.
    Proof.
      intros.
      destruct X_term_ntarai_map_aux as [r0 ?].
      auto.
      destruct (IHn (nc - 1) (map (ntarai r0) (ntarai_make wc)) xc) as [r1 ?].
      omega.
      replace (S (nc - 1)) with nc by omega.
      auto.
      exists (r0 + r1).
      destruct H1 as [v0].
      apply Terminate with v0; auto.
      apply ntarai_continuous_nv with r1.
      omega.
      apply ntarai_continuous_v with (map (ntarai r0) (ntarai_make wc)).
      apply map_fcontinuous.
      apply ntarai_continuous_n.
      omega.
      auto.
    Qed.

  End X_term_induction.

  Open Scope Z_scope.

  Theorem X_term: forall k v x,
    Tarai_X (S k) v x -> exists r, Terminate_with r v (fun y => y <= x).
  Proof.
    intro k. pattern k.
    apply lt_wf_ind.
    intros.
    destruct n.
    (* k = 0 *)
    exists 1%nat. exists x.
    apply ntarai_X_1; auto. omega.
    (* k > 0 *)
    inversion H0.
    destruct v as [|x0]. contradiction.
    destruct v as [|x1]. destruct n; contradiction.
    destruct (Hmax 0%nat) as [y0 [Hy0in]]. omega.
    destruct (Hmax 1%nat) as [y1 [Hy1in]]. omega.
    rewrite <- Hy0in in * |- *.
    rewrite <- Hy1in in * |- *.
    clear x0 x1 Hin Hmax Hy0in Hy1in H1.

    destruct (Z_le_dec y0 y1).
    (* y0 <= y1 *)
    exists 1%nat. exists y1.
    unfold ntarai. simpl.
    destruct (Z_le_dec y0 y1); [auto|contradiction].
    auto.
    (* y0 > y1 *)
    assert (exists m : nat, y0 - y1 - 1 = Z_of_nat m). 
    apply Z_of_nat_complete.
    omega. 
    destruct H1 as [m ?].
    replace y0 with (y1 + 1 + Z_of_nat m)%Z in * |- * by omega.
    clear n0 H1.
    (* y0 = y1 + m *)
    induction m.
    (* m = 0 *)
    destruct (X_term_ntarai_map (S n) (V (y1+1+Z_of_nat 0)::V y1::v) x) as [r0 [v0]]; auto.
    intros.
    apply H with n0; auto.
    exists 1%nat. exists y1.
    unfold ntarai. simpl.
    destruct (Z_le_dec (y1+1+0-1) y1). auto.
    apply False_ind. omega.
    auto. omega.
    exists (S r0). exists v0; auto.
    unfold ntarai. simpl.
    destruct (Z_le_dec (y1+1+0) y1).
    apply False_ind. omega. auto.
    (* S m *)
    rewrite inj_S in * |- *.
    destruct (X_term_ntarai_map (S n) (V (y1+1+Zsucc (Z_of_nat m))::V y1::v) x) as [r0 [v0]]; auto.
    intros.
    apply H with n0; auto.
    generalize (sigma_X _ _ _ H0).
    simpl.
    replace (y1 + 1 + Zsucc (Z_of_nat m) - 1) with (y1 + 1 + Z_of_nat m) by omega.
    apply IHm.
    omega.
    exists (S r0). exists v0; auto.
    unfold ntarai. simpl.
    destruct (Z_le_dec (y1+1+Zsucc (Z_of_nat m)) y1).
    apply False_ind. omega. auto.
  Qed.
End X_term.

Open Scope Z_scope.

Definition max_In_n k x (vec: list Z) :=
  In_n k x vec /\ forall i y, In_n i y vec -> y <= x.

Lemma max_In_n_ex: forall (vec: list Z), vec <> nil -> exists k, exists x,
  max_In_n k x vec.
Proof.
  intros.
  induction vec.
  congruence.
  destruct vec.
  exists O. exists a.
  constructor.
  reflexivity.
  intros.
  destruct i.
  rewrite H0. omega.
  destruct i; contradiction.
  destruct IHvec as [k [x ?]].
  congruence.
  destruct (Z_le_dec a x).
  exists (S k). exists x.
  destruct H0.
  constructor. auto.
  intros.
  destruct i.
  rewrite H2. auto.
  apply H1 with i. auto.
  exists O. exists a.
  destruct H0.
  constructor. reflexivity.
  intros.
  destruct i.
  rewrite H2. omega.
  specialize (H1 i y H2).
  omega.
Qed.

Lemma max_X: forall kmax xmax vec, max_In_n kmax xmax vec ->
  Tarai_X kmax (mapV vec) xmax.
Proof.
  intros.
  destruct H.
  constructor.
  apply In_n_map. auto.
  intros.
  destruct (In_n_exists i vec).
  generalize (In_n_length kmax vec xmax H).
  omega.
  exists x.
  constructor.
  apply In_n_map; auto.
  apply H0 with i; auto.
Qed.

Section max_O.
  Variable vec: list Z.
  Variable x0: Z.
  Variable HmaxO: max_In_n O x0 (x0::vec).

  Lemma max_O_tau: Tarai_X (length vec) (tau (mapV (x0::vec))) x0.
  Proof.
    intros.
    assert (In_n (length vec) (V x0) (tau (mapV (x0::vec)))).
    destruct HmaxO.
    clear HmaxO H0.
    induction vec.
    simpl. auto.
    simpl in * |- *.
    apply IHl. auto.

    constructor.
    auto.
    intros.
    destruct HmaxO.
    destruct (In_n_exists i vec).
    auto.
    exists x.
    simpl.
    constructor.
    apply In_n_app.
    apply In_n_map.
    auto.
    apply H2 with (S i).
    auto.
  Qed.

  Lemma ntarai_max_make_nz: forall k v,
    In_n (S k) v (ntarai_make (mapV (x0::vec))) ->
    Tarai_X (length vec - k)%nat v x0.
  Proof.
    intros.
    assert (k < length vec)%nat.
    apply In_n_length in H.
    rewrite ntarai_make_length in H.
    rewrite mapV_length in H.
    auto with arith.
    unfold ntarai_make in H.
    simpl in H.
    generalize max_O_tau.
    intro.
    generalize (ntarai_make_aux_X
                      (length (mapV vec))
                      (length vec - k - 1)
                      k
                      (tau (mapV (x0::vec))) v x0 H).
    intros.
    replace (length vec - k - 1 + k + 1)%nat with (length vec) in H2 by omega.
    replace (S (length vec - k - 1)) with (length vec - k)%nat in H2 by omega.
    auto.
  Qed.

  Lemma ntarai_max_map_aux: forall k v,
    (0 < length vec)%nat ->
    (exists r, Terminate_with r (sigma (mapV (x0::vec))) (fun y => y <= x0)) ->
    In_n k v (ntarai_make (mapV (x0::vec))) ->
    exists r, Terminate_with r v (fun y => y <= x0 /\ (k = length vec -> y = x0)).
  Proof.
    intros.
    destruct k.
    (* k = 0 *)
    simpl in * |- *.
    rewrite H1.
    destruct H0 as [r [v' ?]].
    exists r. exists v'; auto.
    constructor. auto.
    intro. apply False_ind. omega.
    (* S k *)
    assert (S k < length (ntarai_make (mapV (x0::vec))))%nat.
    apply In_n_length with v; auto.
    rewrite ntarai_make_length in H2.
    rewrite mapV_length in H2.
    simpl in H2.
    apply ntarai_max_make_nz in H1; auto.
    destruct (eq_nat_dec (S k) (length vec)).
    (* S k = length vec *)
    replace (length vec - k)%nat with 1%nat in H1 by omega.
    apply ntarai_X_1 in H1.
    exists 1%nat. exists x0; auto.
    constructor. omega. auto.
    (* S k < length vec *)
    replace (length vec - k)%nat with (S (length vec - k - 1)) in H1 by omega.
    apply X_term in H1.
    destruct H1 as [r [v0]].
    exists r. exists v0; auto.
    constructor. auto.
    intro. contradiction.
  Qed.

  Lemma ntarai_max_map:
    (0 < length vec)%nat ->
    (exists r, Terminate_with r (sigma (mapV (x0::vec))) (fun y => y <= x0)) ->
    exists r, forall k v,
    In_n k v (ntarai_make (mapV (x0::vec))) ->
    Terminate_with r v (fun y => y <= x0 /\ (k = length vec -> y = x0)).
  Proof.
    intros.
    destruct (take_max (S (length vec))
                    (fun k r => forall v, In_n k v (ntarai_make (mapV (x0::vec))) ->
                      Terminate_with r v (fun y => y <= x0 /\ (k = length vec -> y = x0)))) as [r ?].
    (* r independence *)
    intros. destruct (H2 v H3).
    exists v0; auto.
    apply ntarai_continuous_nv with r; auto.
    (* r existence *)
    intros.
    destruct (In_n_exists k (ntarai_make (mapV (x0::vec)))).
    rewrite ntarai_make_length.
    rewrite mapV_length. auto.
    destruct (ntarai_max_map_aux k x) as [r [y ?]]; auto.
    exists r. intros.
    rewrite <- (In_n_unique k (ntarai_make (mapV (x0::vec))) x v); auto.
    exists y; auto.
    (* rmax *)
    exists r.
    intros.
    apply H1.
    apply In_n_length in H2.
    rewrite ntarai_make_length in H2.
    rewrite mapV_length in H2. auto.
    auto.
  Qed.

  Lemma ntarai_max_map_X:
    (0 < length vec)%nat ->
    (exists r, Terminate_with r (sigma (mapV (x0::vec))) (fun y => y <= x0)) ->
    exists r,
    Tarai_X (length vec) (map (ntarai r) (ntarai_make (mapV (x0::vec)))) x0.
  Proof.
    intros.
    destruct ntarai_max_map as [r ?]; auto.
    exists r.
    constructor.
    apply In_n_intro.
    rewrite map_length. rewrite ntarai_make_length. rewrite mapV_length.
    simpl. auto.
    intros.
    destruct (In_n_unmap _ _ _ _ H2) as [y' [Heq Hin]].
    destruct (H1 _ _ Hin) as [y'']. destruct HP.
    rewrite <- H4; auto.
    congruence.
    intros.
    destruct (In_n_exists i (ntarai_make (mapV (x0::vec)))) as [v].
    rewrite ntarai_make_length. rewrite mapV_length. simpl. omega.
    destruct (H1 i v) as [v0]; auto.
    exists v0.
    constructor.
    rewrite <- Hterm.
    apply In_n_map.
    auto.
    tauto.
  Qed.
    
  Lemma ntarai_max_map_term:
    (0 < length vec)%nat ->
    (exists r, Terminate_with r (sigma (mapV (x0::vec))) (fun y => y <= x0)) ->
    exists r,
    Terminate_with r (map (ntarai r) (ntarai_make (mapV (x0::vec)))) (fun y => y <= x0).
  Proof.
    intros.
    destruct (ntarai_max_map_X) as [r0 ?]; auto.
    replace (length vec) with (S (length vec - 1)) in H1 by omega.
    apply X_term in H1.
    destruct H1 as [r1 [v0]].
    exists (r0 + r1)%nat.
    exists v0; auto.
    apply ntarai_continuous_nv with r1.
    omega.
    apply ntarai_continuous_v with (map (ntarai r0) (ntarai_make (mapV (x0::vec)))).
    apply map_fcontinuous.
    apply ntarai_continuous_n. omega.
    auto.
  Qed.

End max_O.

Lemma ntarai_term_max_nz: forall kmax xmax (vec: list Z), max_In_n (S kmax) xmax vec ->
  exists r,
  Terminate_with r (mapV vec) (fun y => y <= xmax).
Proof.
  intros.
  assert (Tarai_X (S kmax) (mapV vec) xmax).
  destruct H.
  constructor.
  apply In_n_map. auto.
  intros.
  destruct (In_n_exists i vec).
  apply In_n_length in H.
  omega.
  exists x.
  constructor.
  apply In_n_map; auto.
  apply H0 with i; auto.
  destruct (X_term kmax (mapV vec) xmax H0) as [r [v]].
  exists r. exists v; auto.
Qed.

Lemma ntarai_terminate_max: forall kmax xmax x0 x1 (vec: list Z), max_In_n kmax xmax (x0::x1::vec) ->
  (kmax = O -> 
    (exists r, Terminate_with r (sigma (mapV (x0::x1::vec))) (fun y => y <= xmax))) ->
  exists r,
  Terminate_with r (mapV (x0::x1::vec)) (fun y => y <= xmax).
Proof.
  intros.
  destruct kmax.
  replace x0 with xmax in * |- *.
  destruct (ntarai_max_map_term (x1::vec) xmax) as [r [v0]]; auto.
  simpl. omega.
  destruct (Z_le_dec xmax x1); auto.
  exists 1%nat. exists x1.
  unfold ntarai. simpl.
  destruct (Z_le_dec xmax x1); [auto|contradiction].
  destruct H.
  apply H1 with 1%nat; reflexivity.
  exists (S r). exists v0; auto.
  unfold ntarai. simpl.
  destruct (Z_le_dec xmax x1); [contradiction|auto].
  destruct H. exact H.
  apply ntarai_term_max_nz with kmax. auto.
Qed.

Lemma ntarai_terminate_aux: forall x0 x1 (vec: list Z),
  exists r,
  Terminate_with r (mapV (x0::x1::vec))
      (fun y => exists k, exists x, In_n k x (x0::x1::vec) /\ y <= x).
Proof.
  intros.
  destruct (Z_le_dec x0 x1).
  (* x0 <= x1 *)
  exists 1%nat. exists x1.
  unfold ntarai. simpl.
  destruct (Z_le_dec x0 x1); [auto|contradiction].
  exists 1%nat. exists x1.
  constructor. reflexivity. omega.

  (* x0 > x1 *)
  assert (exists m : nat, x0 - x1 - 1 = Z_of_nat m). 
  apply Z_of_nat_complete.
  omega. 
  destruct H as [m ?].
  replace x0 with (x1 + 1 + Z_of_nat m)%Z in * |- * by omega.
  clear n H x0.
  
  (* x0 = x1 + 1 + m *)
  induction m.
  (* m = 0 *)
  simpl.
  destruct (max_In_n_ex (x1+1+0::x1::vec)) as [kmax [xmax Hmax]].
  congruence.
  destruct (ntarai_terminate_max kmax xmax (x1+1+0) x1 vec) as [r [v]]; auto.
  intros.
  rewrite H in Hmax. 
  exists 1%nat. exists x1.
  unfold ntarai. simpl.
  destruct (Z_le_dec (x1+1+0-1) x1); auto.
  elim n. omega.
  destruct Hmax. simpl in H0.
  omega.
  exists r. exists v; auto.
  destruct Hmax.
  exists kmax. exists xmax.
  constructor; eauto.

  (* S m *)
  destruct (max_In_n_ex (x1+1+Z_of_nat (S m)::x1::vec)) as [kmax [xmax Hmax]].
  congruence.
  destruct (ntarai_terminate_max kmax xmax (x1+1+Z_of_nat (S m)) x1 vec) as [r [v]]; auto.
  intros.
  rewrite H in Hmax.
  destruct IHm as [r [v0]].
  rewrite inj_S. simpl.
  replace (x1+1+Zsucc(Z_of_nat m)-1) with (x1+1+Z_of_nat m) by omega.
  exists r. exists v0; auto.
  destruct HP as [k [x []]].
  destruct Hmax.
  destruct k.
  specialize (H3  O (x1+1+Z_of_nat (S m)) (refl_equal _)).
  rewrite inj_S in H3. simpl in * |- *. omega.
  specialize (H3 (S k) x H0). omega.
  exists r. exists v; auto.
  exists kmax. exists xmax.
  destruct Hmax.
  auto.
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
  destruct (ntarai_terminate_aux x0 x1 vec) as [r [v]].
  exists r. exists v; auto.
Qed.
