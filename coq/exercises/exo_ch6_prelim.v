From mathcomp Require Import all_ssreflect.

Require Import libSsr.LibNat.
Require Import libSsr.LibLogic.
Set Implicit Arguments.
(* NOTE: In this file, we redefine Equality ... and we do not establish that nat and
         bool are eqType with our redefined Equality ..... Therefore much breaks. 

         Therefore we have separated the file in 2, and exo_ch6 does not go about these
         preliminaries...
*)

(* Now look at pages 124 ->.. *)
(* 
    NOTE: The version in mathcomp.ssreflect.eqtype.Equality differs substantially
    and it is based on HB (Hierarchy Builder)
*)


Module Equality_prelim.

Structure type : Type := Pack {
  sort : Type;
  op : sort -> sort -> bool;
  axiom : forall x y, reflect (x = y) (op x y)
}.

End Equality_prelim.


Module Equality.

Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).
Record mixin_of T := Mixin { op : rel T; 
                              _ : axiom  op}.
Notation class_of := mixin_of.

Structure type : Type := Pack { sort :> Type; 
                                class : class_of sort; }.
End Equality.

Notation eqType := Equality.type.
Definition eq_op T := Equality.op (Equality.class T).
Notation "x == y" := (@eq_op _ x y).

(* Remark the use of :> instead of : to type the field called sort. 
   This tells Coq to declare the Equality.sort projection as a coercion. 
   This makes it possible to write:
        (forall T : eqType, forall x y : T, P) 
   even if T is not a type and only (sort T) is.
*)

Section About_Equality.

Lemma eqnP : Equality.axiom eqn.
Proof.
rewrite /Equality.axiom. (* this clarifies that we can do intros*)
move => n m.
apply:(iffP idP) => [|->]; last by elim m.
by elim: n m => [| n IHn] [|m] //=; move => /IHn ->. 
Qed.

Definition nat_eqMixin := Equality.Mixin eqnP.
Canonical nat_eqType := @Equality.Pack nat nat_eqMixin.
End About_Equality.

Section Using_Generic_Equality.
Check eqn.
Check (Equality.axiom eqn).
Check Equality.op. 


Lemma eqP (T : eqType) : Equality.axiom (Equality.op (Equality.class T)).
Proof. 
(* case considers eqtype as an inductive type with a single constructor
   again we case decompose the mixin into [op axiome] 
*)
case: T => typ  [op axiome ]; exact: axiome.
Qed.

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
by split; apply/eqP.
Qed.

Definition prod_eqMixin := Equality.Mixin pair_eqP.
Canonical prod_eqType := @Equality.Pack ((Equality.sort T1) * (Equality.sort T2)) prod_eqMixin.

End ProdEqType.

(* Here we stop, stuck with the redefined eqType, ... and we do not want to redo it all!
 *)