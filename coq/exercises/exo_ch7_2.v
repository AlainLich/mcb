From mathcomp Require Import all_ssreflect.
From mathcomp Require Import eqtype.
From HB Require Import structures.
Set Implicit Arguments.

(* Here we are in  Chap 7.2  p. 141*)

Module Chapter72.
  (* Goal :make tuples an eqtype: we reuse the equality of sequences  *)
  Definition tcmp n (T : eqType) (t1 t2 : n.-tuple T) := tval t1 == tval t2.

  (* Length equality*)
  Lemma eqtupleP n (T : eqType) : Equality.axiom (@tcmp n T).
  Proof.
   move => x y. (* Goal becomes "reflect (x = y) (tcmp x y)" and is reduced to equalities 
                   by this apply.*)
   Set Printing Coercions. (* Otherwise tval is hidden ... and things look trivial in both
                             subgoals *)
   apply: (iffP eqP); last by move => ->.
      (* Now the other goal; explicit the structures/records/inductive by 'case' *)
    case: x; case: y => s1 sz1 s2 sz2 /= HeqSz. rewrite HeqSz in sz2 *.
    Unset Printing Coercions.  
    (* equational irrelevance is here a consequence of eqtype, see 
       mathcomp.ssreflect.eqtype.eq_irrelevance *)
    by rewrite (eq_irrelevance sz1 sz2).
Qed.
  
  (* From ssreflect/eqtype.v::  eqType implies that equalities (in the eqType) are proof irrelevant *)
  Theorem eq_irrelevance' (T : eqType) x y : forall e1 e2 : x = y :> T, e1 = e2.
  Proof.
  pose proj z e := if x =P z is ReflectT e0 then e0 else e.
  suff: injective (proj y) by rewrite /proj  => injp e e' ; apply: injp; case: eqP.
  pose join (e : x = _) := etrans (esym e).
  apply: can_inj (join x y (proj x (erefl x))) _.
  by case: y /; case: _ / (proj x _).
  Qed.

(* Porting : "Canonical tuple_eqType n T : eqType := 
                       Equality.Pack (Equality.Mixin (@eqtupleP n T))." to HB *)
#[log, verbose]
HB.mixin Record Is_eqty_Tuple (n:nat) (T:eqType) := {
    val : n.-tuple T;
}.
#[log, verbose]
HB.structure Definition Tuple_eqType n  := { NT of Is_eqty_Tuple n  NT }.

HB.about  Is_eqty_Tuple.
HB.about  Tuple_eqType. 


Parameter n: nat.
Check Is_eqty_Tuple.Build n bool.
Check Is_eqty_Tuple.Build n nat.
Check Is_eqty_Tuple.Build n (seq nat).
Check Is_eqty_Tuple.Build 0 (seq bool).
Check Is_eqty_Tuple.Build 0 (seq (seq bool)).
Set Printing Coercions. 
Check Is_eqty_Tuple.Build 0 (seq (seq nat)).
Unset Printing Coercions. 


HB.howto nat   Tuple_eqType.type.
HB.about Is_eqty_Tuple.Build.

#[log, verbose]
HB.instance Definition  ntuple_Eqtype_Tuple n (T:eqType) (nt: n.-tuple T) 
                            (* : Is_eqty_Tuple n T  (* Can be inferred !!*)*)
                            := Is_eqty_Tuple.Build n T nt.



HB.about  Is_eqty_Tuple.
HB.about  Tuple_eqType.

About  ntuple_Eqtype_Tuple.
Fail HB.about  ntuple_Eqtype_Tuple.


Locate tuple_of.
Print Canonical Projections tuple_of.
Print Canonical Projections ntuple_Eqtype_Tuple.
(*
_ <- Is_eqty_Tuple.val ( ntuple_Eqtype_Tuple )
*)

Print  Tuple_eqType.type. 

HB.about Is_eqty_Tuple.Build.

Locate Tuple_eqType.type.
Locate ntuple_Eqtype_Tuple.
Check Tuple_eqType.type.
Check ntuple_Eqtype_Tuple.
(* ntuple_Eqtype_Tuple : forall (n : nat) (T : eqType),
      n.-tuple T -> Is_eqty_Tuple.axioms_ n T *)

Check nat: Tuple_eqType.type 3. 
Check 4.-tuple nat: Tuple_eqType.type 4.
Check 4.-tuple nat: eqType. 

Check Is_eqty_Tuple.phant_axioms .
Print Is_eqty_Tuple.phant_axioms .

Check (Is_eqty_Tuple _ nat ).
HB.about Is_eqty_Tuple.


Check forall t : 3.-tuple nat, [:: t] == [::].
Check forall t : 3.-tuple bool, uniq [:: t; t].
(* Locate uniq: Constant mathcomp.ssreflect.seq.uniq *)
(* Locate undup_uniq: Constant mathcomp.ssreflect.seq.undup_uniq *)
Section Try_It.
Variable t : 3.-tuple (7.-tuple nat).
Check undup_uniq [ :: t; t].
End Try_It.

(* Do we need this (?) (*)
Canonical tuple_eqTuple n T : eqType := Equality.Pack (Equality.Mixin (@eqtupleP n T)).
*)*)


Section Try_It.
Variable s : seq nat.
Variable t :  3.-tuple ( 5.-tuple nat).
Variable  n : nat.
Check (seq nat: Type).
Check (@tval 3 _ t ).
Set Printing Coercions.
Check (@tval 3 ( 5.-tuple nat) t ).
Set Printing All.
Check (@tval 3 ( 5.-tuple nat) t ).
Unset Printing All.
End Try_It.


(* This does not exist anymore ... cf.
 less -N +565 /mount/built/opam/CP.~8.20~2025.01/lib/coq/user-contrib/mathcomp/ssreflect/eqtype.v
 Current: isNew isSub
*)
Locate "[ 'subType' 'for' v ]".
Locate "[ 'isNew' 'for' v ]".


Locate "[ 'isSub' 'for' v ]".


(* Examples of isSub and isNew *)
Section Try_It_1.
Variable  n : nat.
Variable t :  n.-tuple ( (n.+2).-tuple nat).

Check [ isSub for (@tval n nat)]. 
(*[isSub for tval (T:=nat)]
     : isSub.axioms_ (seq nat) (fun x : seq nat => size x == n) 
                     (n.-tuple nat)
  *)
Unset Printing Coercions.
Check [ isSub for (@tval n nat)]. 
Check tuple_of.


(*  This clones the canonical subType structure for n.-tuple nat.  *)
Canonical tuple_subType n s :=  Eval hnf in [isSub for (@tval n s)].


Fail Canonical tuple_subType' n s := [isNew for (@tval _ _)]   .
(* The command has indeed failed with message:
    Destructing let on this type expects 2 variables. Issue is in evaluating
    [isNew for (@tval n s)] . 
 *)
Fail Canonical tuple_subType'  := [isNew for @tval] .
(*The command has indeed failed with message:
  The term "tval" has type "forall (n : nat) (T : Type), n.-tuple T -> seq T"
  while it is expected to have type "nat -> ?T" (cannot instantiate "?T"
  because "n" is not in its scope).
*)

Check (@tval n nat). 
Fail Check [ isNew for (@tval n nat ) ]. 
(* The command has indeed failed with message:
   Destructing let on this type expects 2 variables.
*)
End Try_It_1.

End Chapter72.


(* ------------------------------------------------------------------------ 
 *                    THE FOLLOWING IS DONE IN exo_ch7_2b.v
 * ------------------------------------------------------------------------ *)
  (* REPLACED ABOVE
     Canonical tuple_subType n s := [subType for (@tval n s)].
   *)
  (* Fail Definition tuple_eqMixin n T := [eqMixin of n.-tuple T by <:].
     Canonical tuple_eqType n (T : eqType) := EqType (n.-tuple T) (@tuple_eqMixin n T).
  *)

Module Chapter721.
  Canonical tuple_subType n T := Eval hnf in [isSub for (@tval n T)].
  Locate tuple_subType.
    (* This is local, despite redundancy detected *)
  Locate tval.
    (* This is redundant, we use mathcomp.ssreflect.tuple.tval *)

  Section Chap721_tryit.
    (* This exercises Sub, insub and in subd from the library!*)
    Variables (s : seq nat) (t : 3.-tuple nat).
    Variables size3s : size s == 3.
    Let t1 : 3.-tuple nat := Sub s size3s.
    Let t2 := if insub s is Some t then val (t : 3.-tuple nat) else nil.
    Let t3 := insubd t s. (* 3.-tuple nat *)

    Locate insubd.
  End Chap721_tryit.

  (* Dealt with in exo_ch7_2b, but accepted! *)
  Section SubTypeKit.
    Variables (T : Type) (P : pred T).

    Structure subType : Type := SubType {
      sub_sort :> Type;
      val : sub_sort -> T;
      Sub : forall x, P x -> sub_sort;
      (* elimination rule for sub_sort *)
      _ : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
      _ : forall x Px, val (@Sub x Px) = x
    }.
  End SubTypeKit.

  Notation "[ 'subType' 'for' v ]" := (SubType _ v _
    (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)
    (fun x px => erefl x)).
End Chapter721.


