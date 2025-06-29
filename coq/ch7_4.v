From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* WARNING: the approach here deviates from the book's: we use a different ordinal definition
   for greater separation from the library. This ensures we test our developpents, 
   not the librarie's.

   To make this apparent, the notation 'I_' is renamed 'K_' for disambiguation.
*)

Module Ordinal74.
  Inductive ordinal (n : nat) : Type := Ordinal m of m < n.
  Notation "''K_' n" := (ordinal n) (at level 8, n at level 2, format "''K_' n").

  Coercion nat_of_ord n  (i : ordinal n ) := let: Ordinal m _ := i in m.


  Section Subtype_Ordinal.
  Variables (n:nat).

 Definition OrdinalEq := fun (o1 o2: ordinal n) =>   nat_of_ord o1 == nat_of_ord o2.
  Remark OrdinalEqP : Equality.axiom OrdinalEq.
  Proof.
  rewrite /Equality.axiom => x y; apply/(iffP idP);
     first by rewrite /OrdinalEq; elim: x; elim y => //= m H1 l H2 Heq; 
     have Heq':=(eqP Heq); move :  H2; rewrite Heq' => H2; congr (Ordinal _); apply eq_irrelevance.
  
  by move => H; rewrite H /OrdinalEq.
  Qed.

  HB.about hasDecEq.Build.
  #[log, verbose]
  HB.instance Definition _ := hasDecEq.Build  _   OrdinalEqP. 

  HB.about isSub.Build.
  #[log, verbose]
  HB.instance Definition _ := [isSub  for (@nat_of_ord n)].
 
 HB.about isCountable.Build.
 #[log, verbose]
  HB.instance Definition _ := [Countable of (ordinal n) by <:].

(* We have the choice property as a side effect of being countable *)
Remark ordinal_hasChoice:  hasChoice (ordinal n).
Proof.
apply  Ordinal74_ordinal__canonical__choice_Choice .
Qed. 

(* We also have the Subtype property ( hopefully ) with some goodies *)
Eval hnf in  SubType.eqtype_isSub_mixin (SubType.class Ordinal74_ordinal__canonical__eqtype_SubType).
Eval hnf in  (SubType.eqtype_isSub_mixin (SubType.class Ordinal74_ordinal__canonical__eqtype_SubType)).

End Subtype_Ordinal.

Section Finite_Ordinal.
(* Now the question is how to use this to register as a finType *)

Variables (n:nat).


(* Here we already know that ordinal is a subtype, therefore we will use insub, rather than
   redoing it painfully....
*)

Definition ord_enum: seq (ordinal n):= (pmap insub (iota 0 n)).

Lemma ord_enum_uniq  : uniq ord_enum.
Proof.
by rewrite /ord_enum; apply: pmap_sub_uniq; apply iota_uniq.
Qed.

Lemma ord_enum_equal: ord_enum =i Ordinal74_ordinal__canonical__eqtype_Equality n.
Proof.
move => x. rewrite /Ordinal74_ordinal__canonical__eqtype_Equality =>//=.
rewrite /ord_enum mem_pmap_sub =>//=.
by elim: x => m Hlt //=; rewrite mem_iota.
Qed.


HB.about isFinite.Build.
#[log, verbose]
HB.instance Definition _
  := @isFinite.Build (ordinal n) (ord_enum ) 
                     (@Finite.uniq_enumP _ (ord_enum ) ord_enum_uniq ord_enum_equal).


End Finite_Ordinal.

End Ordinal74.
Import Ordinal74.

(* Now we apply the above Canonical properties to 'K_n .... just as if it had been 'I_n
   in the ssreflect library
 *)

Lemma tnth_default T n (t : n.-tuple T) : 'K_n -> T.
Proof. by rewrite -(size_tuple t); case (tval t) => [|//] []. Qed.

Definition tnth T n (t : n.-tuple T) (i : 'K_n) : T :=
  nth (tnth_default t i) t i.

Definition enum_rank (T : finType) : T -> 'K_#|T|.
Proof.
  (* First deal with absurd case #|T| = 0 *)
  have PosNatDec: forall n:nat, { n = 0} + { 0 < n }; 
   first by  move => n; elim n; [left|move => m H; right].
  case (PosNatDec #|T|); 
    first by move => Hc0 Hab; exfalso; apply: (fintype0 _ Hc0).

  move => Hlt hab; econstructor. 
     Unshelve. all: swap 1 2. (* this sequence allows to deal with existential*)
        by apply #|T|.-1. 
        by rewrite ltn_predL.
Qed.
