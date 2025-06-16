From mathcomp Require Import all_ssreflect.
(* From HB Require Import structures.*)

Require Import libSsr.LibNat.
Require Import libSsr.LibLogic.

Set Implicit Arguments.

Lemma addn2E: forall n, n.+2 = n + 2.
Proof.
move =>n. by elim :n =>//= [n IH]; rewrite IH. 
Qed.
Lemma addn1E: forall n, n.+1 = n + 1.
Proof.
by move =>n; rewrite addnC =>//=.
Qed.

Lemma oddNm2: forall n, ~~ (odd n.*2).
Proof.
move => n. by rewrite odd_double.
Qed.

Lemma muln2E: forall n, n.*2 = n + n. 
Proof. move=>m //=; by symmetry; apply addnn. Qed.

(* Big Ops in 6.7 *)
Section Starters.

Lemma sum_odd n : \sum_(0 <= i < n.*2 | odd i) i = n^2.
Proof.
   
  elim: n => //=; first rewrite exp0n; replace 0.*2 with 0; try auto with arith.
  by rewrite unlock //=.
  move => n IH.
  replace (n.+1.*2) with (n.*2 + 2). 

  replace (n.*2 + 2 ) with ((n.*2.+1).+1).
  rewrite big_mkcond =>//=. rewrite big_nat_recr. rewrite big_nat_recr. 
  rewrite big_mkcond in IH. rewrite  IH =>//=. rewrite oddNm2 odd_double =>//=.
  rewrite addn0 {2}addn1E.
  
  rewrite expnD expn1 =>//=; rewrite  mulSn mulnS addnA addnC mulnn.  
  apply addnPlus. 
  by rewrite muln2E; auto with arith.  
  by apply leq0n. 
  by apply leq0n.  
  by apply addn2E.
  by rewrite doubleS muln2E (addn2E (n + n) ). 
Qed.

  
Lemma sum_odd_3 : \sum_(0 <= i < 3.*2 | odd i) i = 3^2.
Proof.
apply sum_odd.
Qed.

End Starters. 

