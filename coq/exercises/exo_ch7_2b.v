From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

Set Implicit Arguments.

(* Here we jump to Sec 7.2 p. 143,where the making of the subtype kit is described.
   It has for purpose to faclitate the declaration of related Canonicals.
 *)
Section SubTypeKit.
(* Purpose: When one has a base type T and a sub-type ST defined as a boolean sigma type, 
   the Mathematical Components library provides facilities to build all the applicable
  canonical instances from just the name of the projection going from ST to T.

  The subType structure provides a generic notation 'val' for the projector of a sub-type
   (i.e., tval for tuple), with an overloaded injectivity lemma 'val_inj' saying that two 
   objects equal in T are also equal in ST.

  In addition to the generic projection, we get a generic static constructor 'Sub', which
  takes a value in the type T and a proof.

  The sub-type kit provides the dynamic constructors 'insub' and 'insubd' that do not need
  a proof as they dynamically test the property, and oﬀer an attractive encapsulation of the
  diﬃcult convoy pattern [Chl14, section 8.4]. The 'insubd' constructor takes a default
  sub-type value which it returns if the tests fails, while 'insub' takes only a base type
  value and returns an option; both are locked and will not evaluate the test, even
  for a ground base type value.
*)
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
Arguments SubType [T P].

Notation "[ 'xsubType' 'for' v ]" :=
  (SubType _ v _ 
    (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)
    (fun x px => erefl x)).

(* This is explained on p. 143; 
  The subType constructor notation assumes the sub-type is isomorphic to a sigma-type,
  so that its elimination rule can be derived using Coq’s generic destructing 
  let  " (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)", 
  and the projector-constructor identity can be proved by reflexivity: 
  "(fun x px => erefl x)".

  In pratice that means only 'v' needs to be provided , 
  the rest is deduced, (possibly including T and P as the next example shows)!
*)


Record sub_eq3 := { v :> nat; p : v == 3 }.

Canonical x_sub := Eval hnf in [xsubType for v].

Print sub_eq3.
About sub_eq3.
HB.about sub_eq3. 
Print Canonical Projections sub_eq3.

Check insub.
Check insubT.
Check insubF.

(* Here we can use sub_eq3 as a subtype of nat *)
Remark R1 (v:nat) : v >= 0. Proof. by []. Qed.
Remark R2 (f:sub_eq3) : (v f) == 3. Proof. case: f => v P //=. Qed.
Remark R3 (f:sub_eq3) : (v f) > 2. case: f => v P //=; by move: (eqP P) ->. Qed.

(* Now we use x_sub as a subtype of nat*)
Print x_sub.
About x_sub.

(* x_sub: subType (eq_op^~ 3) *)
(* subType : forall T : Type, pred T -> Type *)

Remark R4(x:x_sub) : (v x) == 3. Proof. by case: x. Qed.
Remark R5(x:x_sub) : (v x) < 4. Proof. case: x =>//= vv; by move/eqP ->. Qed.


(* Redoing it explicitely *)
Section RedoSubTypeKit.

(* Variables (T : Type) (P : pred T).*)

Locate SubType. 
Eval simpl in (SubType ).
Eval simpl in (exo_ch7_2b.SubType ).


Record sub_eq3' := { v' :> nat; p' : v' == 3 }. 
                   (* v',p' are defined as "projections" of sub_eq3'*)

Canonical x_sub' := Eval hnf in [xsubType for v'].

Check [xsubType for v'].
      (* Note that v' is not a 'free' variable to bind.. but the projector
        of Record sub_eq3'*)
Check (SubType _ v' _ 
    (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)
    (fun x px => erefl x)).
 
About x_sub.
Eval simpl in (eq_op ^~ 3).

End RedoSubTypeKit.




