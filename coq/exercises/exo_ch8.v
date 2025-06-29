From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Module WR_module.

Inductive windrose : Type := North | South | East | West.

Definition w2o w : 'I_4 :=
  match w with
  | North => inord 0
  | South => inord 1
  | East => inord 2
  | West => inord 3
  end.

Definition o2w (o : 'I_4) :=
  match val o with
  | 0 => North
  | 1 => South
  | 2 => East
  | 3 => West
  | _ => North (* default ? *)
  end.

Lemma pcan_wo4 : cancel w2o o2w.
Proof. by case; rewrite /o2w /= inordK. Qed.

(* This is required by isCountable.Build *)

Definition pick := w2o.

Definition o2w_opt:= (fun x => Some (o2w x)).
Remark pcan_o2w_prelim : pcancel w2o o2w_opt -> pcancel (pickle \o  w2o) (pcomp o2w_opt unpickle).
Proof. by apply pcan_pickleK. Qed.
Remark pcan_o2w_opt: pcancel (pickle \o  w2o) (pcomp o2w_opt unpickle).
Proof. apply pcan_o2w_prelim. rewrite /o2w_opt. by apply (can_pcan pcan_wo4). Qed.



Definition windrose_eq (a b : windrose) : bool :=
  match (a, b) with
  | (North, North) => true
  | (South, South) => true
  | (East,  East)  => true
  | (West,  West)  => true
  | _    => false
  end.

Lemma windrose_eqP : Equality.axiom windrose_eq.
Proof.
rewrite /Equality.axiom => x y.  
apply: (iffP idP). 
  by case x; case y =>//.
  move => ->. by case: y . 
Qed.

(* We sould need Equality.sort for this to typeCheck*)
Fail Check  North == South.
Fail Check  North == North.
Check  North = South.
Check  North = North.


HB.about hasDecEq.Build.
#[log, verbose]
HB.instance Definition _ := @hasDecEq.Build windrose windrose_eq windrose_eqP.

Arguments windrose_eq !a !b.  (* Ensures the function will be unfolded only if all 
                                 the args marked with ! evaluate to constructors. *)
Arguments windrose_eqP {x y}. (* Here we need to know the hidden names, this declares
                                 the enclosed names as implicit, minimally inserted. *)

(* Now the notations work and we have an exqType *)
Check  North == South.
Eval compute in  North == South.


HB.about isCountable.Build.
#[log, verbose]
HB.instance Definition _ := isCountable.Build _ pcan_o2w_opt.


Remark windrose_isCountable:  isCountable windrose.
Proof. 
by econstructor; eapply pcan_o2w_opt.
Qed.

Definition wr_enum  := [:: North; South; East; West] .
Lemma wr_enumP : Finite.axiom wr_enum.
Proof. rewrite /Finite.axiom /wr_enum => elt.
       elim Helim: elt;  by []. 
Qed.

HB.about isFinite.Build.

#[log, verbose]
HB.instance Definition _:= @isFinite.Build windrose wr_enum wr_enumP. 

Remark windrose_isFinite:  isFinite windrose.
Proof.
econstructor.
Unshelve. 
    - by apply wr_enumP.
Qed.

#[log, verbose]
HB.instance Definition _:= choice_isCountable__to__choice_hasChoice.

Remark windrose_hasChoice:  hasChoice windrose.
Proof.
apply  choice_isCountable__to__choice_hasChoice.
Qed.

Remark Rem1: #|[set North; South]| == 2.
Proof.
have HH:=  enum_tupleP [set North; South]. 
by rewrite -(eqP HH) (perm_size (enum_setU _ _)) undup_id !enum_set1 =>//=. 
Qed.


Fail Check North:>'I_4.
(* This adds something *)
Coercion  w2o : windrose >-> ordinal.
Print Coercion Paths windrose ordinal.

Check  #|'I_4| = 4.
Check  #| wr_enum| = 4.
Check North:>'I_4.

Lemma ord4_is_windrose : cancel o2w w2o.
Proof.
move=> x; apply: val_inj; case: x.
by do 5! [ case=> [?|//]; first by rewrite /= inordK ].
Qed.

Goal (~~ windrose_eq North  South).
Proof. by []. Qed.

(* We just check the notations in eqtype! *)
Goal North != South. Proof. by []. Qed.

Fail Check  (North \in windrose). 
Fail Goal (#|enum windrose| == 4).
Fail Goal ( size (enum windrose)  == 4).

Goal  #|'I_4| == 4. Proof. by rewrite card_ord. Qed.
Goal  #| wr_enum| = 4.
Proof.
have H1: (uniq wr_enum); first by [].
by rewrite ((@card_uniqP _ wr_enum)  H1).
Qed.


Goal  North \in wr_enum.
Proof. by []. Qed.

(* Now the only issue is that we do not have the nice notation ..*)

End  WR_module.
