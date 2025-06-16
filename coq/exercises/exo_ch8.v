From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

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

(* Inspired by coq/user-contrib/mathcomp/ssreflect/ssrnat.v , 
    enables the notation == e.g North == South*)
Fail Check  North == South.

HB.about hasDecEq.Build.
#[log, verbose]
HB.instance Definition _ := @hasDecEq.Build windrose windrose_eq windrose_eqP.

(* This would be redundant with above !!
HB.instance Definition _ := hasDecEq.Build _ windrose_eqP.
*)
Arguments windrose_eq !a !b.  (* Ensures the function will be unfolded only if all 
                                 the args marked with ! evaluate to constructors. *)
Arguments windrose_eqP {x y}. (* Here we need to know the hidden names, this declares
                                 the enclosed names as implicit, minimally inserted. *)

(* Now the notations work and we have an exqType *)
Check  North == South.
Eval compute in  North == South.

(* in fintype.v 
    HB.instance Definition _ := isCountable.Build fT fin_pickleK.
    HB.instance Definition _ := isFinite.Build fT f. *)

HB.about isCountable.Build.
#[log, verbose]
HB.instance Definition _ := isCountable.Build _ pcan_o2w_opt.
(*
(pickle \o  w2o): windrose -> nat
(pcomp o2w_opt unpickle): nat -> option windrose
pcan_o2w_opt : pcancel (pickle \o  w2o) (pcomp o2w_opt unpickle)
*)

HB.about  isFinite.Build.



Definition wr_enum  := [:: North; South; East; West] .
Lemma wr_enumP : Finite.axiom wr_enum.
Proof. rewrite /Finite.axiom /wr_enum => elt.
       elim Helim: elt;  by []. 
Qed.

#[log, verbose]
HB.instance Definition _:= @isFinite.Build windrose wr_enum wr_enumP. 

#[log, verbose]
HB.instance Definition _:= choice_isCountable__to__choice_hasChoice.

(* This is a consequence of isCountable *)
Remark windrose_has_Choice:  hasChoice windrose.
Proof.
apply choice_isCountable__to__choice_hasChoice.
Qed.

(*  HB: hasChoice.Build is a factory constructor (from "./choice.v", line 261)
    HB: hasChoice.Build requires its subject to be already equipped with:
    HB: hasChoice.Build provides the following mixins:
        - hasChoice
    HB: arguments: hasChoice.Build T [find_subdef] choice_correct_subdef choice_complete_subdef choice_extensional_subdef
        - T : Type
        - find_subdef : pred T -> nat -> option T
        - choice_correct_subdef :
            forall (P : pred T) (n : nat) (x : T),
            Choice.InternalTheory.find P n = Some x -> P x
        - choice_complete_subdef :
            forall P : pred T,
            (exists x : T, P x) -> exists n : nat, Choice.InternalTheory.find P n
        - choice_extensional_subdef :
            forall P Q : pred T,
            P =1 Q -> Choice.InternalTheory.find P =1 Choice.InternalTheory.find Q
*)


(* Now I need to understand why this fails ???*)
Fail Goal (#| windrose | == 4).

Lemma ord4_is_w : cancel o2w w2o.
Proof.
move=> x; apply: val_inj; case: x.
by do 5! [ case=> [?|//]; first by rewrite /= inordK ].
Qed.

Goal (~~ windrose_eq North  South).
Proof. by []. Qed.

(* We just check the notations in eqtype! *)
Goal North != South. Proof. by []. Qed.

Fail Check  (North \in windrose). (* Need choice or fintype ? *)
Fail Goal (#|enum windrose| == 4).
Fail Goal ( size (enum windrose)  == 4).
Locate "#| _ |".

Goal  (card.body (mem 'I_4) ) == 4. Proof. by rewrite card_ord. Qed.


(* Notation "#| A |" := (card.body (mem A)) : nat_scope (default interpretation)*)

(* For comparison*)
Goal (#|'I_4| == 4). Proof. by rewrite card_ord. Qed.

(* Until we get the Notation right ... this is meaningless 
Goal  (North \in windrose).
Proof.
by rewrite inE.
Qed.
*)
HB.about windrose.
(*
HB: windrose is canonically equipped with structures:
    - Countable
      choice.Choice
      (from "(stdin)", line 61)
    - eqtype.Equality
      (from "(stdin)", line 42)
    - fintype.Finite
      (from "(stdin)", line 78)
*)


