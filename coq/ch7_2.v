From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Chapter72.
Section EqualTuple.
  Variables (n:nat) (T:eqType).
  Definition tcmp (t1 t2 : n.-tuple T) := tval t1 == tval t2.

  Lemma eqtupleP : Equality.axiom tcmp .
  Proof.
    move => x y; apply: (iffP eqP); last first.
      by move => ->.
      case: x; case y => s1 p1 s2 p2 /= E.
      rewrite E in p2 *.
        by rewrite (eq_irrelevance p1 p2).
  Qed.

  HB.about hasDecEq.Build.
  (* HB: arguments: hasDecEq.Build T [eq_op] eqP
        - T : Type
        - eq_op : rel T
        - eqP : Equality.axiom eq_op *)
  #[log, verbose]
  HB.instance Definition _ := @hasDecEq.Build _ tcmp eqtupleP.

(* Definition HB_unnamed_factory_101 : Equality.mixin_of (n.-tuple T) 
    := {| hasDecEq.eq_op := tcmp; hasDecEq.eqP := eqtupleP |}.
   Local Arguments HB_unnamed_factory_101 : clear implicits.

   Definition eqtype_hasDecEq__to__eqtype_hasDecEq : hasDecEq.phant_axioms(n.-tuple T)
    := tuple.HB_unnamed_factory_3 n T.
   Local Arguments eqtype_hasDecEq__to__eqtype_hasDecEq : clear implicits.

   Global Canonical eqtype_hasDecEq__to__eqtype_hasDecEq. *)

End EqualTuple.
  Check forall t : 3.-tuple nat, [:: t] == [::].
  Check forall t : 3.-tuple bool, uniq [:: t; t].
  Check forall t : 3.-tuple (7.-tuple nat), undup [:: t; t] == [:: t].
  
Section Subtype_tuple.
  Variables (n:nat) (T:eqType).
  
  #[log, verbose]
  HB.instance Definition _ := [isSub  for (@tval n T) ].
  About eqtype_isSub__to__eqtype_isSub.

End Subtype_tuple.

End Chapter72.

Module Chapter721.
  (* See eqtype.v for definitions of Subtype related: Sub, insub, insubd,... *)
  Canonical tuple_subType n T := Eval hnf in [isSub for (@tval n T)].
  Check tuple_subType.
  Check tval.

  Section TupleSizes.
      Variables (s : seq nat) (t : 3.-tuple nat).
      Variables size3s : size s == 3.
      Let t1 : 3.-tuple nat := Sub s size3s.
      Let t2 := if insub s is Some t then val (t : 3.-tuple nat) else nil.
      Let t3 := insubd t s. (* 3.-tuple nat *)
  End TupleSizes.
  

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

  (* Need to provide Sub, the elimination rule for sub_sort (???) *)
    
    Fail Check [subType for nat].
End Chapter721.

Module Chapter722.
  Theorem eq_irrelevance (T : eqType) (x y : T) : forall e1 e2 : x = y, e1 = e2.
  Proof. (* See ssreflect/eqtype.v *) 
  pose proj z e := if x =P z is ReflectT e0 then e0 else e.
  suff: injective (proj y) by rewrite /proj  => injp e e' ; apply: injp; case: eqP.
  pose join (e : x = _) := etrans (esym e).
  apply: can_inj (join x y (proj x (erefl x))) _.
  by case: y /; case: _ / (proj x _).
  Qed.
  Check eq_irrelevance.
End Chapter722.
