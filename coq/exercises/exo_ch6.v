From mathcomp Require Import all_ssreflect eqtype ssrnat ssrbool.

Require Import libSsr.LibNat.
Require Import libSsr.LibLogic.
Set Implicit Arguments.


(* Checking sec 6.9 p. 134-5*)
Section TryBigops.
(* See that these are readily computed *)
Eval cbv in (iota 0 7).
Eval  cbv in (index_iota  4 7).

Check nat:eqType.
Locate eqType.


(* Search "bool" "eqtype".
Do not look for bool_eqType... this has become:
Datatypes_bool__canonical__eqtype_Equality = {|
  Equality.sort := bool;
  Equality.class := {| Equality.eqtype_hasDecEq_mixin 
                          := eqtype.HB_unnamed_factory_3 |}
  |}: eqType
*)

Check (@eq_op  Datatypes_bool__canonical__eqtype_Equality true false).
Check (eq_op true false).

Goal (@eq_op  Datatypes_bool__canonical__eqtype_Equality true false)
      =(eq_op true false).
Proof. auto. Qed.

Goal (eq_op true false) = (@eqb true false). 
Proof. auto. Qed.
Eval cbn in forall x y : bool, x == y.
Eval cbn in forall x y : bool, true == false || x == y.

Goal forall x y : bool, (x == y) = (true == false || x == y).
Proof. auto. Qed.


(*
Constructor mathcomp.ssreflect.bigop.BigBody
Variant bigbody (R I : Type) : Type :=
  BigBody : I -> (R -> R -> R) -> bool -> R -> bigbody R I.
*)

Implicit Type l : seq nat.
Lemma example F l1 l2 :
  \sum_(i <- l1 ++ l2) F i = \sum_(i <- l2 ++ l1) F i.
Proof.
   rewrite big_cat.
   (* Here the simplification is absolutely needed !! *)
   Fail rewrite addnC -big_cat. 
   (* Correction is easy ... once you think of it *)
   by rewrite  /= addnC -big_cat.
Qed.

End TryBigops.

(* Concerns Chaap 6.5 p. 125*)
Section Using_Generic_Equality.

Lemma test (x y : nat) : x == y -> x + y == y + y.
Proof. by move => /eqP -> ; apply /eqP. Qed.

End Using_Generic_Equality.

Section ProdEqType.
Variable T1 T2 : eqType.

Check (Equality.sort T1).
Locate "*". 
Check  ((Equality.sort T1) * (Equality.sort T2))%type.

Definition my_andb: bool*bool -> bool:= fun (pb: bool*bool) => pb.1 && pb.2 .
Check my_andb.

Check (fun (x y:  ((Equality.sort T1) * (Equality.sort T2))%type) 
           => (my_andb ((x.1 == y.1), (x.2 == y.2)))). 


Definition pair_eq: rel ( (Equality.sort T1) * (Equality.sort T2) )
   := (fun (x y:  ((Equality.sort T1) * (Equality.sort T2))%type) 
           => (my_andb ((x.1 == y.1), (x.2 == y.2)))).
           
Lemma pair_eqP : Equality.axiom pair_eq.
Proof.
move=> [x1 x2] [y1 y2] /=; apply: (iffP andP) => [[]|[<- <-]] //=.
by move/eqP->; move/eqP->. 
Qed.

Definition prod_eqMixin := Equality.Mixin pair_eqP.
Canonical prod_eqType :=  prod_eqMixin.

End ProdEqType.


Check (nat : Equality.Exports.eqType).
Check (bool : Equality.Exports.eqType).
Check (nat:eqType).
Check (bool:eqType).
Check (fun x y : nat => x == y).

Check (prod_eqType nat bool).

Lemma testP1 (x y : nat) (a b : bool) : (a,x) == (b,y) -> fst (a,x) == b.
Proof. by move=> /eqP ->. Qed.

Lemma testP2 (x y : nat) : (true,x) == (false,y) -> false.
Proof. by []. Qed.

Lemma test_EM (x y : nat) : if x == y.+1 then x != 0 else true.
Proof. by case: ifP => // /eqP ->. Qed.
