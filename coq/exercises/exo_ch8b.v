From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

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

(* This must exist in the library ..*)
Lemma haveFun (A B:Type) (f: A->B): forall z1 z2, z1 = z2 -> f z1 = f z2.
Proof.  by move => z1 z2 Hr ; rewrite Hr. Qed.

(* These are convenience lemmas *)

Remark inordS (l:nat) (i: 'I_l.+1):  i < l.+1 -> @inord l (@inord l i) = i.
Proof.  by move => H; rewrite inordK; [ apply inord_val |]. Qed.

Remark inordL  (l:nat) (i:nat) : i < l.+1 ->  nat_of_ord (@inord l i) = i. 
Proof. by move => H; rewrite inordK. Qed.

Remark inordN  (l:nat) (i:'I_l.+1) : i < l.+1 ->  nat_of_ord (@inord l (@inord l i)) = i. 
Proof. by rewrite inordS. Qed.

(* This is used for  isCountable *)

Lemma pcan_wo4 : cancel w2o o2w.
Proof. by case; rewrite /o2w /= inordK. Qed.

Remark inj_w2o: injective w2o.  
Proof.
move => x y. rewrite /w2o.
elim x; elim y =>//=;
move =>H; have:= haveFun _ _ (@nat_of_ord _) _ _ H; rewrite !inordK =>//=.   
Qed.

(* Required to establish isFinite ..., only uses eqType and ordinal properties *)
Lemma pcan_ow4: cancel o2w w2o.
Proof.
move=> x; apply: val_inj; case: x.
by do 5! [ case=> [?|//]; first by rewrite /= inordK ].
Qed.

Remark inj_o2w: injective o2w. 
Proof.
by move => x y; apply:can_inj; apply pcan_ow4.
Qed.


Definition windrose_eq (a b : windrose) : bool := w2o a == w2o b.

Lemma windrose_eqP : Equality.axiom windrose_eq.
Proof.
rewrite /Equality.axiom => x y.  
apply: (iffP idP) => H ; last by  rewrite H /windrose_eq =>//=.
by apply inj_w2o; move:H; rewrite /windrose_eq =>H; apply/eqP.
Qed.


HB.about hasDecEq.Build.
#[log, verbose]
HB.instance Definition _ := @hasDecEq.Build windrose _  windrose_eqP .


(* This is required by isCountable.Build *)
Definition pick := w2o.
Definition o2w_opt:= (fun x => Some (o2w x)).
Remark pcan_o2w_prelim : pcancel w2o o2w_opt -> pcancel (pickle \o  w2o) (pcomp o2w_opt unpickle).
Proof. by apply pcan_pickleK. Qed.
Definition pcan_o2w_opt: pcancel (pickle \o  w2o) (pcomp o2w_opt unpickle).
Proof. apply pcan_o2w_prelim. rewrite /o2w_opt. by apply (can_pcan pcan_wo4). Qed.

HB.about isCountable.Build.
#[log, verbose]
HB.instance Definition _ := isCountable.Build _ pcan_o2w_opt.

(* Verification .. *)
Remark windrose_isCountable:  isCountable windrose.
Proof. 
by econstructor; eapply pcan_o2w_opt.
Qed.

Definition sub_pick_w2o:= fun (P: pred windrose) (w:windrose) =>
      if (P w) then  ((pickle \o  w2o ) w) else (@None windrose).

Definition sub_o2w_opt: pred windrose -> nat ->  option windrose
      := fun (P: pred windrose) (n: nat) =>
      if (n<4) then let w:= o2w ( inord n) 
                     in if P w then Some w
                               else (@None windrose)
               else  (@None windrose).


Remark o2w_inord_w2o w : o2w (inord(w2o w)) = w.
Proof.
rewrite /w2o  /o2w => //=. 
elim Hel: w;  
  rewrite (_:forall i, i< 4 -> (nat_of_ord (inord (inord i))) = i) =>//=; 
          move =>i Hineq; rewrite inordK inordL =>//=. 
Qed.
(* Here we used an anonymous lemma in the rewrite tactic, see Gonthier&Mahboubi p. 48 *)

Remark w2o_lt_n (w:windrose): w2o w < 4 = true.
Proof. apply ltn_ord.  Qed.

(* This is a verification, hasChoice is a consequence of isCountable *)
Remark windrose_hasChoice: hasChoice windrose.
Proof.
   rewrite /hasChoice.phant_axioms.  
   econstructor. Unshelve.
   all: swap 1 4.
   by apply sub_o2w_opt.
   by  move => P exH; elim exH => w HP; exists (w2o w);
       rewrite /sub_o2w_opt w2o_lt_n  o2w_inord_w2o; replace (P w) with true. 
   move => P Q H. 
  by move => w; rewrite /sub_o2w_opt H =>//.
  { move => P n w; rewrite /sub_o2w_opt =>//.
     elim Hn4: (n<4).
     elim HP: ( P (o2w (inord n))) => HSome. 
     by move: HP; rewrite (Some_inj HSome) => H.  
     by discriminate. 
     by discriminate. 
  }
Qed.


Definition wr_enum  :=  [seq o2w i  | i <- ord_enum 4].

Lemma wr_enumP : Finite.axiom wr_enum.
Proof. 
     rewrite /Finite.axiom /wr_enum => elt.
     have H := @map_inj_uniq 'I_4 windrose  o2w inj_o2w ( ord_enum 4).
     have Hu: uniq (ord_enum 4) == true; first by rewrite ord_enum_uniq.
     have Hu' : uniq [seq o2w i  | i <- ord_enum 4]; first by rewrite H (eqP Hu).
     rewrite (count_uniq_mem _ Hu').
     elim Hcontra: (elt  \in [seq o2w i  | i <- ord_enum 4]) =>//=.
     exfalso.

     have :=  @mem_map _ _ _ inj_o2w (ord_enum 4) (w2o elt); 
     rewrite pcan_wo4 Hcontra //= => Hcontr1.

     case : (w2o elt) Hcontr1 => m Hlt //=. 
     rewrite /ord_enum  mem_pmap_sub -/(iota 0 4) mem_iota add0n //= .
     by move => H1; rewrite -H1 in Hlt.    
Qed.

(* We do not have finType yet !*)
Fail Check (windrose:finType).

HB.about isFinite.Build.
(*HB: arguments: isFinite.Build T [enum_subdef] enumP_subdef
    - T : Type
    - enum_subdef : seq T
    - enumP_subdef :
        Finite.axiom
          (T:={|
                Equality.sort := T;
                Equality.class :=
                  {| Equality.eqtype_hasDecEq_mixin := Finite.class T |}
              |}) enum_subdef
*)
#[log, verbose]
HB.instance Definition _:= @isFinite.Build windrose wr_enum wr_enumP. 

(* verification; now finType is usable *)
Check (windrose:finType).


Lemma test : (N != S) && (N \in windrose) && (#| windrose | == 4).
Proof.
case: eqP => //= _; rewrite -[4]card_ord.
rewrite -(card_image (can_inj pcan_wo4)).
apply/eqP; apply: eq_card=> o; rewrite inE.
by apply/imageP; exists (o2w o) => //=; rewrite pcan_ow4.
Qed.

(* The detail testing shows the how to resolve the various terms in isolation *)
Lemma mini_test1 : (N != S) .
Proof.
case: eqP => //= _; rewrite -[4]card_ord.
Qed.

Lemma mini_test2 : (N \in windrose).
Proof.
by rewrite inE.
Qed.

Lemma mini_test3 : (#| windrose | == 4).
Proof.
rewrite -[4]card_ord -(card_image (can_inj pcan_wo4)).
apply/eqP; apply: eq_card=> o;  rewrite inE.
by apply/imageP; exists (o2w o) => //=; rewrite pcan_ow4.
Qed.

