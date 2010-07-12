Require Import ZArith.
Require Import List.
Require Import Tarai_Base.

Open Scope Z_scope.

Inductive dZ_le: dZ -> dZ -> Prop :=
| dZ_eq x : dZ_le x x
| dZ_B  x : dZ_le B x.

Hint Constructors dZ_le: tarai.

Lemma dZ_le_refl: forall a, dZ_le a a.
Proof.
  auto with tarai.
Qed.

Hint Resolve dZ_le_refl: tarai.

Lemma dZ_le_trans: forall a b c, dZ_le a b -> dZ_le b c -> dZ_le a c.
Proof.
  intros.
  destruct H; auto with tarai.
Qed.

Inductive VdZ_le: VdZ -> VdZ -> Prop :=
| VdZ_le_nil: VdZ_le nil nil
| VdZ_le_cons x xs y ys: dZ_le x y -> VdZ_le xs ys -> VdZ_le (x::xs) (y::ys).

Hint Constructors VdZ_le: tarai.

Lemma VdZ_le_refl: forall v, VdZ_le v v.
Proof.
  induction v; auto with tarai.
Qed.

Hint Resolve VdZ_le_refl: tarai.

Lemma VdZ_le_trans: forall v w u, VdZ_le v w -> VdZ_le w u -> VdZ_le v u.
Proof.
  induction v.
  intros.
  inversion H.
  rewrite <- H2 in H0.
  auto.
  intros.
  destruct w; destruct u;
    try inversion H; try inversion H0.
  constructor.
  apply dZ_le_trans with d; auto.
  apply IHv with w; auto.
Qed.

Lemma dZ_dec_le: forall a b, dZ_le a b -> dZ_le (dZ_dec a) (dZ_dec b).
Proof.
  intros.
  destruct H; auto with tarai.
Qed.

Hint Resolve dZ_dec_le: tarai.

Definition continuous (f: VdZ -> dZ) :=
  forall v w, VdZ_le v w -> dZ_le (f v) (f w).

Definition continuous_v (f: VdZ -> VdZ) :=
  forall v w, VdZ_le v w -> VdZ_le (f v) (f w).

Lemma sigma_continuous: continuous_v sigma.
Proof.
  red.
  intros.
  destruct v; destruct w; try inversion H.
  auto with tarai.
  simpl in * |- *.
  auto with tarai.
Qed.

Lemma VdZ_app_le_l: forall v w u, VdZ_le v w -> VdZ_le (v ++ u) (w ++ u).
Proof.
  induction v.
  intros.
  inversion H.
  auto with tarai.
  intros.
  inversion H.
  simpl in *|- *.
  auto with tarai.
Qed.

Lemma VdZ_app_le_r: forall v w u, VdZ_le w u -> VdZ_le (v ++ w) (v ++ u).
Proof.
  induction v.
  auto.
  simpl.
  auto with tarai.
Qed.

Lemma VdZ_split: forall u v w, VdZ_le (u++v) w ->
  exists u', exists v', u' ++ v' = w /\ VdZ_le u u' /\ VdZ_le v v'.
Proof.
  induction u.
  exists nil. exists w.
  simpl in * |- *.
  auto with tarai.
  intros.
  destruct w.
  simpl in H. inversion H.
  simpl in H. inversion H.
  destruct (IHu  v w) as [u' [v' ?]]; auto.
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

Lemma tau_continuous: continuous_v tau.
Proof.
  red.
  intros.
  destruct H.
  auto with tarai.
  simpl in * |- *.
  apply VdZ_le_trans with (ys ++ x::nil).
  apply VdZ_app_le_l; auto.
  apply VdZ_app_le_r. auto with tarai.
Qed.

Lemma Y_continuous: forall n init recur,
  continuous init ->
  (forall f, continuous f -> continuous (recur f)) ->
  continuous (Yn n init recur).
Proof.
  intros.
  induction n; simpl; auto.
Qed.

Lemma ntarai_init_continuous: continuous ntarai_init.
Proof.
  red.
  auto with tarai.
Qed.

Definition VVdZ := list VdZ.

Inductive VVdZ_le: VVdZ -> VVdZ -> Prop :=
| VVdZ_le_nil: VVdZ_le nil nil
| VVdZ_le_const x xs y ys: VdZ_le x y -> VVdZ_le xs ys -> VVdZ_le (x::xs) (y::ys).

Lemma ntarai_make_aux_continuous: forall n v w, VdZ_le v w ->
  VVdZ_le (ntarai_make_aux v n) (ntarai_make_aux w n).
Proof.
  induction n.
  simpl.
  constructor.
  simpl.
  constructor.
  auto using sigma_continuous.
  apply IHn.
  auto using tau_continuous.
Qed.

Lemma ntarai_make_continuous: forall v w, VdZ_le v w ->
  VVdZ_le (ntarai_make v) (ntarai_make w).
Proof.
  unfold ntarai_make.
  intros.
  replace (length w) with (length v).
  auto using ntarai_make_aux_continuous.
  induction H; auto.
  simpl.
  congruence.
Qed.

Lemma ntarai_make_map_continuous: forall f v w, continuous f ->
  VVdZ_le v w -> VdZ_le (map f v) (map f w).
Proof.
  intros.
  induction H0.
  simpl.
  auto with tarai.
  simpl.
  auto with tarai.
Qed.

Lemma ntarai_recur_continuous_aux: forall f,
  continuous f -> continuous (fun v => f (map f (ntarai_make v))).
Proof.
  red.
  intros.
  apply H.
  apply ntarai_make_map_continuous.
  auto.
  apply ntarai_make_continuous.
  auto.
Qed.

Lemma ntarai_recur_continuous: forall f,
  continuous f -> continuous (ntarai_recur f).
Proof.
  red.
  intros.
  generalize (ntarai_recur_continuous_aux f H v w H0).
  inversion H0.
  auto with tarai.
  inversion H3.
  inversion H2.
  intros.
  destruct x as [x|]; destruct y as [y|]; auto with tarai.
  destruct x as [x|]; destruct y as [y|]; auto with tarai.
  destruct x0 as [x0|]; destruct y0 as [y0|]; auto with tarai.
  unfold ntarai_recur.
  inversion H1. inversion H6.
  destruct (Z_le_dec y y0).
  auto with tarai.
  auto with tarai.
  inversion H6.
  inversion H1.
Qed.

Theorem ntarai_continuous: forall n, continuous (ntarai n).
Proof.
  red.
  intros.
  apply Y_continuous.
  exact ntarai_init_continuous.
  exact ntarai_recur_continuous.
  exact H.
Qed.

Lemma Y_add: forall A B n m (init: A -> B) (recur: (A -> B) -> A -> B),
  Yn (n+m)%nat init recur = Yn n (Yn m init recur) recur.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  congruence.
Qed.

Definition f_le f g := forall (v: VdZ), dZ_le (f v) (g v).

Lemma Y_fcontinuous: forall n f g recur,
  f_le f g -> continuous f -> continuous g ->
  (forall f g, f_le f g -> continuous f -> continuous g-> f_le (recur f) (recur g)) ->
  (forall f, continuous f -> continuous (recur f)) ->
  f_le (Yn n f recur) (Yn n g recur).
Proof.
  intros.
  induction n.
  auto.
  simpl.
  auto using Y_continuous.
Qed.

Lemma map_fcontinuous: forall f g v,
  f_le f g -> VdZ_le (map f v) (map g v).
Proof.
  induction v.
  auto with tarai.
  simpl.
  auto with tarai.
Qed.

Lemma ntarai_continuous_n_aux: forall n m v, dZ_le (ntarai n v) (ntarai (n+m)%nat v).
Proof.
  unfold ntarai.
  intros.
  rewrite (Y_add VdZ dZ n m ntarai_init ntarai_recur).
  apply Y_fcontinuous; auto with tarai.
  intro.
  auto with tarai.
  exact ntarai_init_continuous.
  exact (ntarai_continuous m).
  red.
  intros.
  destruct v0.
  auto with tarai.
  destruct v0.
  destruct d; auto with tarai.
  destruct d; destruct d0; auto with tarai.
  unfold ntarai_recur.
  destruct (Z_le_dec z z0); auto with tarai.
  apply dZ_le_trans with (f (map g (ntarai_make (V z::V z0::v0)))); auto.
  apply H0.
  apply map_fcontinuous; auto.
  exact ntarai_recur_continuous.
Qed.

Theorem ntarai_continuous_n: forall n n' v, (n <= n')%nat ->
  dZ_le (ntarai n v) (ntarai n' v).
Proof.
  intros.
  replace n' with (n + (n' - n))%nat by omega.
  apply ntarai_continuous_n_aux.
Qed.
