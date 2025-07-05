From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

Set Implicit Arguments.

(* Looks at book's Chap 7.4 p. 146 *)
(* TBD: Remaining issues with Mixins/Canonicals *)

(* Check some typing attributes*)
Section Try_1.
Variables (T:eqType) (TF:finType) (s:seq T).
Print Coercion Paths bool nat.
Check (nat:eqType).
Fail Check (nat:finType).
Check (bool:finType).
Check (seq T: eqType).

Check (seq T: Type).
Fail Check (seq T: finType).
Fail Check (seq TF: finType).

Check Ordinal.
Check ('I_3).
Remark P1: 2 <4. Proof. by apply/eqP. Defined.
Print P1.
Check ([eta introTF (c:=true) eqP] erefl).
Check (Ordinal P1:'I_4).
Check (@Ordinal 4 3 P1:'I_4).
Check (@Ordinal 4 3 ([eta introTF (c:=true) eqP] erefl) :'I_4).
Check (@Ordinal 4 0 ([eta introTF (c:=true) eqP] erefl) :'I_4).

(* Ordinals coerce to nats*)
Check (fun (oi:'I_4) => oi ) : 'I_4 -> nat.
Print Coercion Paths ordinal nat.

Check 'I_4. (* Coq.ssr.ssrbool.predArgType *)

End Try_1.


Module Ordinal74.
  (* Note: the theory of ordinals is in fintype.v *)
  Inductive ordinal' (n : nat) : Type := Ordinal' m of m < n.
  Notation "''I_' n" := (ordinal' n). 
  (* This differs from librarie's version, which uses predArgType. *)

  Coercion nat_of_ord' n (i : ordinal' n) := let: Ordinal' m _ := i in m.
  
  Canonical ordinal_subType' n := [isSub for ( @nat_of_ord' n)].
  
 
  Definition nat_to_ord'' (card:nat) (n:nat) (pf: n < card): ordinal' card.
  Proof. by exists n.  Defined.
   
  Definition nat_to_ord' := fun card n : nat => [eta Ordinal' card n].
  Remark R0: nat_to_ord' = nat_to_ord''. Proof. by []. Qed.

  Definition nat_to_ord_subtype (card:nat) (n:nat) (pf: n < card): 
            subType (T:=nat) (fun x : nat => x < card).
  Proof.
  econstructor. 
  apply :SubType.Class. 
  apply: ordinal_subType'.
  Defined.


Definition nat_to_ord_option (card:nat) 
      := fun  (n : nat)
        => match @idP  (n < card) in (Bool.reflect _ b)
                  return (option nat)
            with
              | @Bool.ReflectT _ _  => @Some nat n
              | @Bool.ReflectF _ _ => @None  nat
            end.

Section Test1.

  (* Verify our function a little bit *)
  Goal (nat_to_ord_option 4 1)  = Some 1.
  Proof.
    by rewrite /nat_to_ord_option; elim (@idP (leq 2 4 ));  compute.
  Qed.

  Goal (nat_to_ord_option 4 6)  = None.
  Proof.
    by rewrite /nat_to_ord_option; elim (@idP (leq 7 4) ); compute.
  Qed.

  Goal (nat_to_ord_option 4 1)  = Some 0 -> False.
  Proof.
    by rewrite /nat_to_ord_option; elim (@idP (leq 2 4 )) => H1; [injection|].
  Qed.

  Lemma nat_to_ord_lt: forall l m, m < l -> nat_to_ord_option l m = Some m.
  Proof.
    by move => l m Ineq; rewrite /nat_to_ord_option;
    elim (@idP (leq (S m) l)). 
  Qed.

  (* Here we need to coerce iota to list (ordinal' n) *)
  Variables (n:nat).
  Check (iota 0 n).
  
  Check (map (nat_to_ord_option n  ) (iota 0 n)).
  Check (let n:=4 in (map (nat_to_ord_option n  ) (iota 0 n))).
  
  Goal (let n:=3 in (map (nat_to_ord_option n  ) (iota 0 n))) = (Some 0)::(Some 1)::(Some 2)::nil.
  Proof.
  simpl. rewrite /nat_to_ord_option. 
  elim (@idP (leq 0 3)) => H0 //=.
  elim (@idP (leq 1 3)) => H1 //=.
  elim (@idP (leq 2 3)) => H2 //=.
  elim (@idP (leq 3 3)) => H3 //=.
  Qed.


Remark R1: forall l,  [seq i <- iota 0 l  | i < l] == iota 0 l.
Proof.
move => l. 
have := @filter_iota_ltn 0 l l; rewrite add0n => //= H; first by rewrite H. 
Qed. 

Remark R2:  forall (T:eqType) (s s': seq T) (m:T), 
    s =i s' -> mem s m = mem s' m.
Proof.
by move=> T s s' m Hi;  apply: Hi.  
Qed.

Remark R3: forall n, (map (nat_to_ord_option n  ) (iota 0 n)) = map Some (iota 0 n).
Proof.
move => l.
wlog: l/    (size (iota 0 l) <= l) 
         && ([seq i <- iota 0 l  | i < l] == iota 0 l ); 
    first by move =>HStrong; apply:HStrong; rewrite size_iota R1 leqnn. 

elim/last_ind: (iota 0 l)  => //= s m IH HSz.

(* We (hopefully) have a usable / strengthened induction*)  
rewrite !map_rcons; congr (rcons _).
{
  apply IH.  move: HSz; rewrite size_rcons => H.
  case (andP H) => H1 H2; clear H; apply/andP; split; auto.
  set sm:= rcons s m in  H2.
  (* This is probably more painful than necessary ..*) 
    have Hall:= @all_filterP _ (fun i => i < l) sm. 
    have H2':= eqP H2. 
    rewrite H2' in Hall.
    have Hid: sm=sm; first by [].
    have:= introT Hall Hid.
   (* End painful sequence (?)*)
  rewrite all_rcons  => HS; case (andP HS) => HS1 HS2. 
  have Hall2:=  (@all_filterP _  (fun i : nat => i < l) s) HS2.
  by rewrite Hall2. 
}
{ move: HSz; rewrite size_rcons => H.
  case (andP H) => H1; rewrite filter_rcons.
  elim Hel: (m<l) =>HI; first by apply: nat_to_ord_lt; rewrite Hel.
  exfalso. (* HI: "all elements in LHS seq are smaller than l" contradicts Hel ...*)
  have: m \in [seq i <- s  | i < l]; rewrite (eqP HI).

  rewrite /in_mem. have Hrew:= (R2 m (mem_rcons s m)).
  have: mem (m::s) m; first by apply mem_head.
  by rewrite -Hrew.
  move => Hmrc.
  replace (rcons s m) with ([seq i <- s  | i < l]) in  Hmrc; last by apply/eqP.
  by move: Hmrc ; rewrite mem_filter Hel.
}
Qed.

End Test1.

(** UNTIL WE PROVIDE THE COERCIONS/CANONICALS this tests the ssreflect library...
*)
Check ord_enum.
End Ordinal74.

Lemma val_ord_enum n : map val (ord_enum n) = iota 0 n.
Proof.
  rewrite pmap_filter; last by exact: insubK.
    by apply/all_filterP; apply/allP => i; rewrite mem_iota isSome_insub.
Qed.

Lemma ord_enum_uniq n : uniq (ord_enum n).
Proof. by rewrite pmap_sub_uniq ?iota_uniq. Qed.

Lemma mem_ord_enum n i : i \in (ord_enum n).
Proof.
    by rewrite -(mem_map (@ord_inj n)) (val_ord_enum n) mem_iota ltn_ord.
Qed.


Lemma tnth_default T n (t : n.-tuple T) : 'I_n -> T.
Proof. by rewrite -(size_tuple t); case (tval t) => [|//] []. Qed.

Definition tnth T n (t : n.-tuple T) (i : 'I_n) : T :=
  nth (tnth_default t i) t i.


(* Another use of ordinals is to express the position of an inhabitant of a finType 
   in its enumeration.*)
Definition enum_rank (T : finType) : T -> 'I_#|T|.
Proof.
move => finSet. rewrite unlock.
(* finSet says that finType is inhabited, therefore its card is strictly positive !
 *)
by apply (@Ordinal _ 0); rewrite -cardT; apply/card_gt0P; exists finSet.
Qed.


