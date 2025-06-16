From mathcomp Require Import all_ssreflect.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example gauss n :
  \sum_(0 <= i < n.+1) i = n * n.+1 %/ 2.
Proof.
elim: n =>[|n IHn]; first by apply: big_nat1.

(* Constant mathcomp.ssreflect.bigop.big_nat_recr
big_nat_recr : 
  forall (R : Type) (idx : R) (op : Monoid.law idx)
         (n m : nat) (F : nat -> R),
         m <= n -> \big[op/idx]_(m <= i < n.+1) F i 
                       =op (\big[op/idx]_(m <= i < n)  F i) (F n) *)

rewrite big_nat_recr //= IHn addnC -divnMDl //. 
by rewrite mulnS muln1 -addnA -mulSn -mulnS.
Qed.

(* Recommended headers *)
(* From mathcomp Require Import all_ssreflect. *)
(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)
