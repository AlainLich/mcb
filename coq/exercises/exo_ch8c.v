From HB Require Import structures.
From mathcomp Require Import all_ssreflect perm fingroup.

(* The version fully built over the HB/library interfaces, with a few 
   checks and printouts added. Otherwise same as chap8.v  *)

Inductive windrose : predArgType := N | S | E | W.

Definition w2o w : 'I_4 :=
  match w with
  | N => inord 0
  | S => inord 1
  | E => inord 2
  | W => inord 3
  end.

Definition o2w (o : 'I_4) :=
  match val o with
  | 0 => N
  | 1 => S
  | 2 => E
  | 3 => W
  | _ => N
  end.

Lemma can_wo4 : cancel w2o o2w.
Proof. by case; rewrite /o2w /= inordK. Qed.

Fail Check (windrose:eqType).

#[log, verbose]
HB.instance Definition _ :=  Equality.copy windrose (can_type can_wo4).

Check (windrose:eqType).

Fail Check (windrose:choiceType).

HB.instance Definition _ :=  Choice.copy windrose (can_type can_wo4).

Check (windrose:choiceType).


Fail Check (windrose:countType).

HB.instance Definition _ :=  Countable.copy windrose (can_type can_wo4).

Check (windrose:countType).


Fail Check (windrose:finType).

HB.instance Definition _ :=  Finite.copy windrose (can_type can_wo4).

Check (windrose:finType).


Lemma ord4_is_w : cancel o2w w2o.
Proof.
move=> x; apply: val_inj; case: x.
by do 5! [ case=> [?|//]; first by rewrite /= inordK ].
Qed.

Lemma test : (N != S) && (N \in windrose) && (#| windrose | == 4).
Proof.
case: eqP => //= _; rewrite -[4]card_ord.
rewrite -(card_image (can_inj can_wo4)).
apply/eqP; apply: eq_card=> o; rewrite inE.
by apply/imageP; exists (o2w o) => //=; rewrite ord4_is_w.
Qed.




