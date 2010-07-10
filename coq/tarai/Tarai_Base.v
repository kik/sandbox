Require Import ZArith.
Require Import List.

Open Scope Z_scope.

Inductive den (A: Type) : Type :=
| V : A -> den A
| B : den A.

Implicit Arguments V [A].
Implicit Arguments B [A].

Definition dZ := den Z.
Definition VdZ := list dZ.

Definition dZ_dec x :=
match x with
| V x => V (x - 1)
| B => B
end.

Definition sigma (v: VdZ) :=
match v with
| nil => nil
| h::t => dZ_dec h::t
end.

Definition tau (v: VdZ) :=
match v with
| nil => nil
| h::t => t ++ h::nil
end.

Fixpoint Yn {A: Type} n (init: A) (recur: A -> A) : A :=
match n with
| O => init
| S n' => recur (Yn n' init recur)
end.

Fixpoint ntarai_make_aux (v: VdZ) (n: nat) : list VdZ :=
match n with
| O => nil
| S n' => sigma v::ntarai_make_aux (tau v) n'
end.

Definition ntarai_make (v: VdZ) : list VdZ := ntarai_make_aux v (length v).

Definition ntarai_init (v: VdZ) : dZ := B.
Definition ntarai_recur (f: VdZ -> dZ) (v: VdZ) : dZ :=
match v with
| V x1::V x2::tl =>
  if Z_le_dec x1 x2 then V x2
  else f (map f (ntarai_make v))
| _ => B
end.

Definition ntarai (n: nat) (v: VdZ) := Yn n ntarai_init ntarai_recur v.
