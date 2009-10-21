Require Import Reals.
Require Import Fourier.

Open Local Scope R_scope.

Definition ball x r y := x - r < y < x + r.

Definition subset (E F: R -> Prop) :=
  forall y, E y -> F y.

Lemma ball_le_subset: forall x r1 r2,
  r1 <= r2 -> subset (ball x r1) (ball x r2).
Proof.
  unfold subset, ball.
  intros.
  destruct H0.
  constructor; fourier.
Qed.

Lemma ball_min_subset_l: forall x r1 r2,
  subset (ball x (Rmin r1 r2)) (ball x r1).
Proof.
  intros.
  apply ball_le_subset.
  apply Rmin_l.
Qed.

Lemma ball_min_subset_r: forall x r1 r2,
  subset (ball x (Rmin r1 r2)) (ball x r2).
Proof.
  intros.
  apply ball_le_subset.
  apply Rmin_r.
Qed.

Definition invimg (f: R -> R) (E: R -> Prop) :=
  fun y => E (f y).

Definition continuity (f: R -> R) :=
  forall x eps,
  eps > 0 ->
  { delta: R | delta > 0 /\ subset (ball x delta) (invimg f (ball (f x) eps)) }.

Definition inner_pt (E: R -> Prop) x :=
  { delta: R | delta > 0 /\ subset (ball x delta) E}.

Definition complement (E: R -> Prop) :=
  fun x => ~ E x.

Lemma sup_def_1: forall (E: R -> Prop) s, is_lub E s ->
  forall eps, eps > 0 -> forall x, s < x < s+eps -> ~E x.
Proof.
  unfold is_lub.
  intros.
  intro.
  destruct H.
  destruct H1.
  assert (x <= s) by auto.
  fourier.
Qed.

Lemma sup_def_2: forall (E: R -> Prop) s, is_lub E s ->
  forall eps, eps > 0 -> ~forall x, s-eps < x <= s -> (complement E) x.
Proof.
  unfold is_lub, complement.
  intros.
  intro.
  destruct H.
  assert (is_upper_bound E (s - eps)).
  red.
  intros.
  assert (H4 := H1 x).
  assert (H5 := H x H3).
  destruct (total_order_T (s - eps) x) as [[Hlt|Heq]|Hgt].
  assert (s - eps < x <= s) by auto.
  tauto.
  fourier.
  fourier.
  assert (H4 := H2 (s - eps) H3).
  fourier.
Qed.

Lemma sup_not_inner: forall (E: R -> Prop) s, is_lub E s ->
  inner_pt E s -> False.
Proof.
  intros.
  destruct H0.
  destruct a.
  assert (E (s + x * /2)).
  unfold subset in H1.
  apply H1.
  unfold ball. constructor; fourier.
  assert (H3 := sup_def_1 E s H x H0).
  apply H3 with (s + x * / 2).
  constructor; fourier.
  auto.
Qed.

Lemma sup_not_outer: forall (E: R -> Prop) s, is_lub E s ->
  inner_pt (complement E) s -> False.
Proof.
  intros.
  destruct H0.
  destruct a.
  unfold subset in H1.
  assert (forall y, s - x < y <= s -> complement E y).
  intros.
  apply H1.
  unfold ball.
  destruct H2.
  constructor; fourier.
  assert (H3 := sup_def_2 E s H x H0).
  tauto.
Qed.

Theorem IVT: 
  forall (f:R -> R) (x y:R),
    continuity f ->
    x < y -> f x < 0 -> 0 < f y -> { z:R | x <= z <= y /\ f z = 0 }.
Proof.
  intros.
  set (A := fun t => t <= y /\ f t <= 0).

  assert (HAx: A x).
  constructor; auto with real.
  assert (Huby: is_upper_bound A y).
  unfold is_upper_bound.
  intros.
  destruct H3.
  auto.

  assert (Hsup: {m: R & is_lub A m}).
  apply completeness.
  exists y; auto.
  exists x; auto.
  destruct Hsup as [z Hsup].

  exists z.
  assert (Hxzy: x <= z <= y).
  case Hsup.
  constructor; auto.
  constructor; auto.

  destruct (total_order_T (f z) 0) as [[Hpos|Hzero]|Hneg].
  (* Hpos *)
  apply False_ind.
  assert (inner_pt A z).

  assert (z < y).
  destruct (Rtotal_order z y); auto.
  destruct H3.
  rewrite H3 in Hpos. fourier.
  destruct Hxzy. fourier.

  set (eps := - f z).
  assert (Hepspos: eps > 0).
  unfold eps; auto with real.
  destruct (H z eps Hepspos) as [delta1 [Hdelta1pos Hdelta1]].

  set (delta2 := y - z).
  assert (Hdelta2pos : delta2 > 0).
  unfold delta2; fourier.
  set (delta := Rmin delta1 delta2).
  exists delta.
  constructor.
  unfold delta. auto using Rmin_Rgt_r.

  unfold subset.
  intro t. intros.
  constructor.
  generalize (ball_min_subset_r z delta1 delta2 t H4).
  unfold ball, delta2. intros [Ht1 Ht2]. fourier.

  generalize (ball_min_subset_l z delta1 delta2 t H4).
  intros.
  generalize (Hdelta1 t H5).
  unfold invimg, ball, eps. intros [Ht1 Ht2]. fourier.

  exact (sup_not_inner A z Hsup H3).

  (* Hzero *)
  auto.

  (* Hpos *)
  apply False_ind.
  assert (inner_pt (complement A) z).
  set (eps := f z).
  assert (Hepspos: eps > 0) by auto.
  destruct (H z eps Hepspos) as [delta [Hdeltapos Hdelta]].
  exists delta.
  constructor. auto.
  unfold subset.
  intros.
  generalize (Hdelta y0 H3).
  unfold invimg, ball, eps, complement.
  intros. unfold A. intro.
  destruct H5. destruct H4. fourier.
  exact (sup_not_outer A z Hsup H3).
Qed.
