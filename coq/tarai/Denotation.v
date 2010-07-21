Require Import ZArith.
Require Import List.
Require Import Tarai_Base.

Open Scope Z_scope.

Class PreOrder (A: Type) := {
  le: A -> A -> Prop;
  preorder_refl: forall x, le x x;
  preorder_trans: forall x y z, le x y -> le y z -> le x z
}.

Hint Resolve @preorder_refl: tarai.

Inductive dZ_le: dZ -> dZ -> Prop :=
| dZ_le_refl x : dZ_le x x
| dZ_le_B  x : dZ_le B x.

Hint Constructors dZ_le: tarai.

Instance dZ_Order: PreOrder dZ := {
  le := dZ_le
}.
Proof.
  constructor.
  intros. destruct H; auto with tarai.
Defined.

Inductive list_le `{AO: PreOrder A} : list A -> list A -> Prop :=
| list_le_nil: list_le nil nil
| list_le_cons x xs y ys: le x y -> list_le xs ys -> list_le (x::xs) (y::ys).

Hint Constructors list_le: tarai.

Instance list_PreOrder `{AO: PreOrder A} : PreOrder (list A) := {
  le := list_le
}.
Proof.
  induction x.
  constructor.
  constructor.
  apply preorder_refl.
  exact IHx.

  induction x.
  intros.
  inversion H.
  congruence.
  intros.
  destruct y; destruct z;
    try inversion H; try inversion H0.
  constructor.
  apply preorder_trans with a0; auto.
  apply IHx with y; auto.
Defined.

Section list_le_props.
  Variable a: Type.
  Variable aord: PreOrder a.

  Lemma app_le_l: forall (v w u: list a), le v w -> le (v ++ u) (w ++ u).
  Proof.
    induction v.
    intros.
    inversion H.
    auto with tarai.
    intros.
    inversion H.
    simpl in * |- *.
    auto with tarai.
  Qed. Check app_le_l.

  Lemma app_le_r: forall (v w u: list a), le w u -> le (v ++ w) (v ++ u).
  Proof.
    induction v.
    auto.
    simpl in * |- *.
    auto with tarai.
  Qed.

  Lemma le_length: forall (v w: list a), le v w -> length v = length w.
  Proof.
    simpl.
    induction v.
    intros.
    inversion H.
    auto.
    intros.
    inversion H.
    simpl.
    auto.
  Qed.
End list_le_props.

Implicit Arguments app_le_l [[a] [aord]].
Implicit Arguments app_le_r [[a] [aord]].
Implicit Arguments le_length [[a] [aord]].

Definition continuous `{aord: PreOrder a, bord: PreOrder b} (f: a -> b) :=
  forall x y, le x y -> le (f x) (f y).

Lemma dZ_dec_continuous: continuous dZ_dec.
Proof.
  red. simpl. intros.
  destruct H; auto with tarai.
Qed.

Hint Resolve dZ_dec_continuous: tarai.

Lemma sigma_continuous: continuous sigma.
Proof.
  red. simpl. intros.
  destruct x; destruct y; try inversion H.
  auto with tarai.
  simpl in * |- *.
  auto with tarai.
Qed.


Lemma tau_continuous: continuous tau.
Proof.
  red.
  intros.
  destruct H.
  auto with tarai.
  unfold tau.
  apply preorder_trans with (ys ++ x::nil).
  apply app_le_l; auto.
  apply app_le_r.
  simpl. auto with tarai.
Qed.

Lemma Y_continuous: forall `{aord: PreOrder a, bord: PreOrder b},
  forall n (init: a -> b) (recur: (a -> b) -> a -> b),
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

Lemma ntarai_make_aux_continuous: forall n, continuous (fun v => ntarai_make_aux v n).
Proof.
  red.
  induction n.
  auto with tarai.
  simpl.
  constructor.
  auto using sigma_continuous.
  apply IHn.
  auto using tau_continuous.
Qed.

Lemma ntarai_make_continuous: continuous ntarai_make.
Proof.
  red.
  unfold ntarai_make.
  intros.
  replace (length y) with (length x).
  apply ntarai_make_aux_continuous.
  auto.
  apply le_length.
  auto.
Qed.

Lemma map_continuous: forall `{aord: PreOrder a, bord: PreOrder b} (f: a -> b),
  continuous f -> continuous (map f).
Proof.
  red.
  intros.
  induction H0.
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
  apply map_continuous.
  auto.
  apply ntarai_make_continuous.
  auto.
Qed.

Lemma ntarai_recur_continuous: forall f,
  continuous f -> continuous (ntarai_recur f).
Proof.
  red.
  intros.
  generalize (ntarai_recur_continuous_aux f H x y H0).
  inversion H0.
  auto with tarai.
  inversion H2.
  destruct x0; destruct y0; auto with tarai.
  destruct x0 as [x0|]; destruct y0 as [y0|]; try inversion H1; auto with tarai.
  destruct x1 as [x1|]; destruct y1 as [y1|]; try inversion H5; auto with tarai.
  unfold ntarai_recur.
  destruct (Z_le_dec y0 y1).
  auto with tarai.
  auto with tarai.
  simpl. auto with tarai.
  simpl.  auto with tarai.
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

Lemma Y_add: forall A n m (init: A) (recur: A -> A),
  Yn (n+m)%nat init recur = Yn n (Yn m init recur) recur.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  congruence.
Qed.

Definition f_le `{aord: PreOrder a, bord: PreOrder b} (f g: a -> b) :=
  forall v, le (f v) (g v).

Instance CFOrder `{aord: PreOrder a, bord: PreOrder b} : PreOrder (a -> b) := {
  le := f_le
}.
Proof.
  red.
  auto with tarai.

  unfold f_le.
  intros.
  apply preorder_trans with (y v); auto.
Defined.

Lemma map_fcontinuous: forall `{aord: PreOrder a, bord: PreOrder b},
  continuous (@map a b).
Proof.
  red.
  intros. intro.
  induction v.
  auto with tarai.
  simpl in * |- *.
  auto with tarai.
Qed.

Lemma Y_fcontinuous: forall `{aord: PreOrder a, bord: PreOrder b},
  forall n (f g: a -> b) recur,
  (forall f, continuous f -> continuous (recur f)) ->
  (forall f g, f_le f g -> continuous f -> continuous g -> le (recur f) (recur g)) ->
  f_le f g -> continuous f -> continuous g ->
  le (Yn n f recur) (Yn n g recur).
Proof.
  induction n.
  auto.
  intros.
  simpl.
  apply H0.
  apply IHn; auto.
  apply Y_continuous; auto.
  apply Y_continuous; auto.
Qed.

Lemma ntarai_continuous_n_aux: forall n m, le (ntarai n) (ntarai (n+m)%nat).
Proof.
  intros.
  change (le (Yn n ntarai_init ntarai_recur) (Yn (n+m)%nat ntarai_init ntarai_recur)).
  rewrite (Y_add _ n m).
  apply Y_fcontinuous.
  exact ntarai_recur_continuous.
  intros. intro.
  destruct v as [|x0]. auto with tarai.
  destruct v as [|x1]. destruct x0; auto with tarai.
  destruct x0 as [x0|]; auto with tarai.
  destruct x1 as [x1|]; auto with tarai.
  unfold ntarai_recur.
  destruct (Z_le_dec x0 x1); auto with tarai.
  apply preorder_trans with (f (map g (ntarai_make (V x0::V x1::v)))).
  apply H0.
  apply map_fcontinuous; auto.
  apply H.
  intro. unfold ntarai_init. simpl.
  auto with tarai.
  exact ntarai_init_continuous.
  exact (ntarai_continuous m).
Qed.

Theorem ntarai_continuous_n: forall n n', (n <= n')%nat ->
  le (ntarai n) (ntarai n').
Proof.
  intros.
  replace n' with (n + (n' - n))%nat by omega.
  apply ntarai_continuous_n_aux.
Qed.

Theorem ntarai_continuous_nv: forall n n' v x, (n <= n')%nat ->
  ntarai n v = V x -> ntarai n' v = V x.
Proof.
  intros.
  generalize (ntarai_continuous_n n n' H v).
  rewrite H0.
  intro.
  inversion H1.
  auto.
Qed.
