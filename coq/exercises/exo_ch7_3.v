From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Set Implicit Arguments.

(* Chap 7.3 p.145 *)
Locate count. (* Constant mathcomp.ssreflect.seq.count *)

Notation count_mem x := (count [pred y | y == x]).

Module finite.
  Definition axiom (T : eqType) (e : seq T) :=
    forall x : T, count_mem x e = 1.

  Record mixin_of (T : eqType) := Mixin {
    enum : seq T;
    _ : @axiom T enum;                                  
  }.
End finite.

(* Notation mathcomp.ssreflect.fintype.Finite
   Module mathcomp.ssreflect.fintype.FiniteNES.Finite
   Module mathcomp.ssreflect.fintype.Finite
  (shorter name to refer to it in current context is fintype.Finite) *)

(* Definition mytype_finMixin := Finite.Mixin mytype_enum mytype_enumP. *)
(* Canonical mytype_finType := @Finite.Pack mytype mytype_finMixin. *)

(* Lemma myenum_uniq : uniq myenum. *)
(* Lemma mem_myenum : forall x : T, x \in myenum. *)
(* Definition mytype_finMixin := Finite.UniqFinMixin myenum_uniq mem_myenum. *)
Locate cardT.
    (* Constant mathcomp.ssreflect.fintype.cardT
      Constant mathcomp.ssreflect.order.Order.cardT
      (shorter name to refer to it in current context is Order.cardT) *)
Lemma cardT (T : finType) : #|T| = size (enum T).
Proof. 
by rewrite unlock =>//=.
Qed.

Lemma forallP (T : finType) (P : pred T) : reflect (forall x, P x) [forall x, P x].
Proof. (* Quite difficult, uses fintype.v, various lemmas on predicates 'pred' *)
Admitted.



