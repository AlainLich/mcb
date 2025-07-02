From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.

     
Section FinFunDef.
  Variable (aT : finType). (* domain type *)
  Variable (rT : Type). (* codomain type *)

  (* The finfun is represented by its graph (as/stored in a tuple indexed over the domain) *)
  Inductive finfun_type : Type := Finfun of #|aT|.-tuple rT. 
  Definition finfun_of of phant (aT -> rT) := finfun_type.

  Definition fgraph f := let: Finfun t := f in t.
  Coercion fgraph: finfun_type >-> tuple_of. 


  #[log, verbose] 
  HB.instance Definition _ := Eval hnf in [isNew for fgraph].
       (* Makes finfun_type a subtype where fgraph is the isomorphic projection onto tuples*)
 
  Notation "{ 'ffun' fT }" := (finfun_of (Phant fT)).
End FinFunDef.

(* Coercion to a function class*)
Definition fun_of_fin aT rT f x := tnth (@fgraph aT rT f) (enum_rank x).
Coercion fun_of_fin : finfun_type >-> Funclass.


Definition finfun aT rT f := @Finfun aT rT (codom_tuple f).
Notation "[ ’ffun’ x : aT => F ]" := (finfun (fun x : aT => F)).  


Section FinFunProperties.
  Variable (aT : finType). (* domain type *)
  Variable (rT : eqType). (* codomain type *)

(* Equip finfun with eq type; this is not available from first encounter with HB above.*)

Definition finfun_eq  (f1 f2: finfun_type aT rT): bool
    :=  fgraph f1 == fgraph f2.

Lemma finfun_eqP: Equality.axiom finfun_eq.
Proof.
  move=>x y.
  apply/(iffP idP) => Hyp. 
  by move: Hyp; elim x => tx; elim y => ty; rewrite /finfun_eq /fgraph=> H; rewrite (eqP H).
  by rewrite  Hyp /finfun_eq /fgraph; elim y =>//=.
Qed.

HB.about hasDecEq.Build.
#[log, verbose]
HB.instance Definition _ := @hasDecEq.Build (finfun_type aT rT) _ finfun_eqP .

End FinFunProperties.

Section FinFunProperties_Finite.
  Variable (aT : finType). (* domain type *)
  Variable (rT : finType). (* codomain type, required finite *)

  (* Equip with countable *)
  #[log, verbose]
  HB.instance Definition _ :=  [Countable of (finfun_type aT rT) by <: ].

(* Equip with finite *)
  #[log, verbose]
  HB.instance Definition _ :=  [Finite of (finfun_type aT rT) by <:].


End FinFunProperties_Finite.



Lemma card_ffun (aT rT : finType) : #| {ffun aT -> rT} | = #|rT| ^ #|aT|.
Proof.
  apply finfun.card_ffun. (* In finfun.v , where the proof scheme is intricate *)
Qed.


(* The proof was an exercise for ch2, see size_all_words 
   To use this we need to define/prove a bijection between 
   fgraphs and words (size #|aT|) over the rT alphabet...
   The proof in chap2 is simpler than "finfun.card_ffun"'s. 
*)

Definition eqfun A B (f g : B -> A) : Prop := forall x, f x = g x.
Notation "f1 =1 f2" := (eqfun f1 f2).

Lemma ffunP (aT : finType) rT (f1 f2 : {ffun aT -> rT}) : f1 =1 f2 <-> f1 = f2.
Proof.
  apply finfun.ffunP. (* this has an intricate proof. *)
Qed.

(* This is the context one needs in order to type check the lemma, it's an
extract of bigop.v *)
Section Distributivity.

Import Monoid.Theory.

Variable R : Type.
Variables zero one : R.
Local Notation "0" := zero.
Local Notation "1" := one.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Local Notation "x * y" := (times x y).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).
Local Notation "x + y" := (plus x y).

Lemma bigA_distr_bigA (I J : finType) F :
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
  = \big[+%M/0]_(f : {ffun I -> J}) \big[*%M/1]_i F i (f i).
Proof.
(* This proof from ssreflect/bigop.v defers all the arguments to 2 lemmas, also in the
  library *)
 by rewrite bigA_distr_big; apply: eq_bigl => ?; apply/familyP.
Qed.


End Distributivity.

