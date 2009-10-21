Require Import Arith.
Require Import List.

Inductive pos : Set := pos1 | pos2 | pos3.

Definition pos_eq_dec: forall (p1 p2: pos), {p1=p2}+{p1<>p2}.
Proof.
  decide equality.
Defined.

Definition tower := list pos.

Fixpoint single_tower (t: tower) (p: pos) {struct t} :=
match t with
| nil => True
| hd::tl => p = hd /\ single_tower tl p
end.

Lemma single_tower_app_1: forall (t t': tower) (p: pos),
  single_tower t p -> single_tower t' p -> single_tower (t++t') p.
Proof.
  induction t.
  auto.
  simpl.
  intros.
  constructor; try tauto.
  apply IHt; auto.
  tauto.
Qed.

Lemma single_tower_app_left: forall (t t': tower) (p: pos),
  single_tower (t++t') p -> single_tower t p.
Proof.
  induction t.
  simpl.
  auto.
  intros.
  replace ((a::t)++t') with (a::(t++t')) in H by auto.
  simpl in H.
  destruct H.
  simpl.
  constructor; auto.
  apply (IHt t').
  auto.
Qed.

Lemma single_tower_app_right: forall (t t': tower) (p:pos),
  single_tower (t++t') p -> single_tower t' p.
Proof.
  induction t.
  auto.
  intros.
  replace ((a::t)++t') with (a::(t++t')) in H by auto.
  simpl in H.
  apply IHt.
  tauto.
Qed.

Lemma rev_single_tower: forall (t:tower) (p:pos),
  single_tower (rev t) p -> single_tower t p.
Proof.
  induction t.
  auto.
  intros.
  replace (rev (a::t)) with (rev t ++ a::nil) in H by auto.
  generalize (single_tower_app_left (rev t) (a::nil) p H).
  generalize (single_tower_app_right (rev t) (a::nil) p H).
  intros.
  replace (a::t) with ((a::nil)++t) by auto.
  apply single_tower_app_1; auto.
Qed.

Inductive move : Set :=
| from_to (from to: pos):  move.

Definition moves := list move.

Fixpoint legal_move_rev (t:tower) (m: move) {struct t} :=
match t with
| hd::tl =>
  match m with from_to from to =>
  if pos_eq_dec from hd then True else
  if pos_eq_dec to hd then False else
  legal_move_rev tl m
  end
| nil => False
end.

Definition legal_move (t: tower) (m: move) := legal_move_rev (rev t) m.

Fixpoint make_move_rev (t:tower) (m:move) {struct t} :=
match t with
| hd::tl =>
  match m with from_to from to =>
  if pos_eq_dec from hd then to::tl else
  if pos_eq_dec to hd then hd::tl else
  hd::make_move_rev tl m
  end
| nil => nil
end.

Definition make_move (t:tower) (m:move) := rev (make_move_rev (rev t) m).

Fixpoint legal_moves (m:moves) (t:tower) {struct m} :=
match m with
| hd::tl => legal_move t hd /\ legal_moves tl (make_move t hd)
| nil => True
end.

Definition make_moves (m:moves) (t:tower) :=
  fold_left make_move m t.

Definition add_disk (t: tower) (p:pos) := p::t.

Lemma make_move_len: forall (t:tower) (m:move),
  length (make_move t m) = length t.
Proof.
  unfold make_move.
  intros.
  rewrite (rev_length (make_move_rev (rev t) m)).
  rewrite <- (rev_length t).
  induction (rev t).
  auto.
  simpl.
  destruct m.
  destruct (pos_eq_dec from a).
  auto.
  destruct (pos_eq_dec to a).
  auto.
  simpl.
  auto.
Qed.

Lemma make_moves_len: forall (m:moves) (t:tower),
  length (make_moves m t) = length t.
Proof.
  induction m.
  auto.
  simpl.
  intros.
  rewrite (IHm (make_move t a)).
  apply make_move_len.
Qed.

Lemma add_disk_comm_move: forall (t:tower) (m:move) (p:pos),
  legal_move t m ->
  legal_move (add_disk t p) m /\
  add_disk (make_move t m) p = make_move (add_disk t p) m.
Proof.
  unfold add_disk, make_move, legal_move.
  intros.
  replace (rev (p::t)) with (rev t ++ p::nil) by auto.
  induction (rev t).
  inversion H.

  simpl.
  destruct m.
  simpl in H.
  destruct (pos_eq_dec from a).
  rewrite <- (rev_unit (to::l) p).
  auto.
  destruct (pos_eq_dec to a).
  contradiction.
  
  simpl.
  assert (IH := IHl H).
  destruct IH.
  rewrite <- H1.
  auto.
Qed.

Lemma add_disk_comm_moves: forall (m:moves) (t:tower) (p:pos),
  legal_moves m t ->
  legal_moves m (add_disk t p) /\
  add_disk (make_moves m t) p = make_moves m (add_disk t p).
Proof.
  induction m.
  auto.
  intros.
  simpl in H.
  destruct H.
  simpl.
  destruct (add_disk_comm_move t a p H).
  rewrite <- H2.
  destruct (IHm (make_move t a) p H0).
  auto.
Qed.

Fixpoint answer (n: nat) (from to rest: pos) {struct n} :=
match n with
| O => nil
| S m =>  answer m from rest to ++ (from_to from to::nil) ++ answer m rest to from
end.

Lemma legal_moves_app: forall (m m':moves) (t:tower),
  legal_moves m t ->
  legal_moves m' (make_moves m t) ->
  legal_moves (m++m') t.
Proof.
  induction m.
  auto.
  simpl.
  intros.
  destruct H.
  constructor.
  auto.
  apply (IHm m' (make_move t a)); auto.
Qed.

Lemma make_moves_app: forall (m m':moves) (t:tower),
  make_moves m' (make_moves m t) = make_moves (m++m') t.
Proof.
  induction m.
  auto.
  simpl.
  intros.
  auto.
Qed.

Lemma single_add_move: forall (t:tower) (from to rest: pos),
  from <> to -> from <> rest -> to <> rest ->
  single_tower t rest ->
  legal_move (add_disk t from) (from_to from to) /\
  add_disk t to = make_move (add_disk t from) (from_to from to).
Proof.
  unfold add_disk, legal_move, make_move.
  intros.
  assert (single_tower (rev t) rest).
  apply rev_single_tower.
  rewrite (rev_involutive t).
  auto.

  replace (rev (from::t)) with (rev t ++ from::nil) by auto.
  replace (to::t) with (to::rev (rev t)).
  induction (rev t).
  simpl.
  destruct (pos_eq_dec from from).
  auto.
  congruence.
  simpl in H3.
  destruct H3.
  destruct (IHl H4).
  rewrite <- H3.
  replace ((rest::l)++from::nil) with (rest::(l++from::nil)) by auto.
  simpl.
  destruct (pos_eq_dec from rest).
  contradiction.
  destruct (pos_eq_dec to rest).
  contradiction.
  replace (rev (rest::make_move_rev (l++from::nil) (from_to from to)))
      with (rev (make_move_rev (l++from::nil) (from_to from to)) ++ rest::nil) by auto.
  rewrite <- H6.
  auto.
  rewrite (rev_involutive t).
  auto.
Qed.

Theorem hanoi_1: forall (n:nat) (t: tower) (from to rest: pos),
  from <> to -> from <> rest -> to <> rest ->
  length t = n ->
  single_tower t from ->
  legal_moves (answer n from to rest) t
   /\ single_tower (make_moves (answer n from to rest) t) to.
Proof.
  induction n.
  simpl.
  intros.
  destruct t; auto.
  simpl in H2.
  discriminate.

  simpl.
  intros.
  destruct t.
  discriminate.
  simpl in H3.
  destruct H3.
  rewrite <- H3.

  simpl in H2.
  assert (length t = n) by auto.

  assert (rest <> to) by auto.
  generalize (IHn t from rest to H0 H H6 H5 H4).
  intros (H7, H8).

  replace (from::t) with (add_disk t from) by auto.

  set (m1 := answer n from rest to) in * |- *.
  rewrite <- (make_moves_app m1 (from_to from to::answer n rest to from) (add_disk t from)).

  destruct (add_disk_comm_moves m1 t from H7). 
  set (t1 := make_moves m1 (add_disk t from)) in * |- *.
  set (t1' := make_moves m1 t) in * |- *.

  destruct (single_add_move t1' from to rest H H0 H1 H8).
  rewrite H10 in * |-.

  assert (length t1' = n).
  rewrite <- H5.
  apply (make_moves_len m1 t).

  assert (rest <> from) by auto.
  assert (to <> from) by auto.
  destruct (IHn t1' rest to from H6  H14 H15 H13 H8).

  set (m2 := answer n rest to from) in * |- *.
  replace (from_to from to :: m2) with ((from_to from to::nil)++m2) by auto.
  rewrite <- (make_moves_app (from_to from to::nil) m2 t1).
  simpl.
  set (t2 := make_move t1 (from_to from to)) in * |- *.

  destruct (add_disk_comm_moves m2 t1' to H16).
  rewrite H12 in * |- *.

  set (t3 := make_moves m2 t2) in * |- *.

  constructor.

  apply legal_moves_app.
  auto.
  replace (from_to from to :: m2) with ((from_to from to::nil)++m2) by auto.
  apply legal_moves_app.
  simpl.
  auto.
  auto.

  rewrite <- H19.
  simpl.
  auto.
Qed. 

Fixpoint pow (n m: nat) {struct m} :=
match m with
| O => 1
| S r => 2 * pow n r
end.

Inductive diff_largest (t s: tower) : Prop :=
diff_largest_c (t' s': tower) (p q: pos):
  t = add_disk t' p ->
  s = add_disk s' q -> p <> q -> diff_largest t s.

Definition move_largest (t: tower) (m: move) : Prop :=
   diff_largest t (make_move t m).
(*
Definition from_of_move (m: move) :=
match m with from_to f t => f end.

Definition to_of_move (m: move) :=
match m with from_to f t => t end.

Definition rest_of_move (m: move) :=
match m with
| from_to pos1 pos2 => pos3
| from_to pos1 pos3 => pos2
| from_to pos2 pos1 => pos3
| from_to pos2 pos3 => pos1
| from_to pos3 pos1 => pos2
| from_to pos3 pos2 => pos1
| _ => pos1
end.
*)
Lemma move_large_impl_single: forall (t: tower) (from to rest: pos),
  from <> to -> from <> rest -> to <> rest ->
  legal_move (add_disk t from) (from_to from to) ->
  move_largest (add_disk t from) (from_to from to) ->
    single_tower t rest.
Proof.
  unfold add_disk, legal_move.
  intros t from to rest.
  replace (rev (from::t)) with (rev t ++ from::nil) by auto.
  intros.
  inversion H3.

Theorem hanoi_2: forall (n:nat) (t: tower) (from to rest: pos),
  from <> to -> from <> rest -> to <> rest ->
  length t = n ->
  single_tower t from ->
  legal_moves (answer n from to rest) t ->
  single_tower (make_moves (answer n from to rest) t) to ->
  length (answer n from to rest) = pow 2 n - 1.



