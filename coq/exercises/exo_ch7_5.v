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
  (*
      Definition HB_unnamed_factory_186 : isSub.axioms_ (#|aT|.-tuple rT) xpredT
                                            finfun_type :=
        [isNew for fgraph].
      Local Arguments HB_unnamed_factory_186 : clear implicits.
      Global Canonical HB_unnamed_factory_186.
      Strategy 1000 [HB_unnamed_factory_186].
      Definition exo_ch7_5_finfun_type__canonical__eqtype_SubType : subType
                                                                      (T:=#|aT|.-tuple
                                                                          rT) xpredT :=
        {|
          SubType.sort := finfun_type;
          SubType.class := {| SubType.eqtype_isSub_mixin := HB_unnamed_factory_186 |}
        |}.
      Local Arguments exo_ch7_5_finfun_type__canonical__eqtype_SubType : clear implicits.
      Global Canonical exo_ch7_5_finfun_type__canonical__eqtype_SubType. 
  *)

  Notation "{ 'ffun' fT }" := (finfun_of (Phant fT)).
  End FinFunDef.

(* These are finite ie in finfun *)
Definition test1: {ffun 'I_7 -> nat}. Abort.
Definition test1: {ffun bool -> nat}. Abort.
(* Not this !*)
Fail Definition test1: {ffun nat -> bool}.


Definition fun_of_fin aT rT f x := tnth (@fgraph aT rT f) (enum_rank x).
Coercion fun_of_fin : finfun_type >-> Funclass.


Definition finfun aT rT f := @Finfun aT rT (codom_tuple f).
Notation "[ ’ffun’ x : aT => F ]" := (finfun (fun x : aT => F)).  


Section FFun_Trials.
Variable n:nat.
Check [ffun i : 'I_4 => i + 2]. (* : {ffun 'I_4 -> nat} *)
Check [ffun i : 'I_4 => i + 2] : {ffun 'I_4 -> nat} .
Check  {ffun 'I_4 -> nat}: eqType.
Fail Check  {ffun 'I_4 -> nat}: finType.
Check  {ffun 'I_4 -> bool}: finType.
Check  {ffun 'I_4 -> 'I_n}: finType.

Check [ffun i : 'I_4 => 2 * i + 2] = [ffun i : 'I_4 => 2 * (i + 1)].
Goal [ffun i : 'I_4 => 2 * i + 2] = [ffun i : 'I_4 => 2 * (i + 1)].
(* eq_dffun from librarie's finfun.v*)
Proof. apply eq_dffun => x.  by rewrite mulnDr muln1. Qed.
End FFun_Trials.

Section More_Finfun_Tree_Trials.
Variables (n:nat).

(* This addition is the librarie's/tutorial example in finfun.v (commented out) , 
   with minimal renaming. Notice that m varies, and can be 0 at a 'leaf' *)
Inductive yatree := node m of yatree ^ m.
Fixpoint yasize t := let: node _ f := t in sumn (codom (yasize \o f)) + 1.

Example yatree_step (K : yatree -> Type) 
  := forall m st (t := node st) & (forall i : 'I_m, K (st i)), 
            K t.

Example yatree_rect_1 K (Kstep : yatree_step K) : forall t, K t.
Proof.
(* See tactic fix in Coq Manual Chap 3.1. The idents (including the first one before 
   the with clause) are the names of the induction hypotheses. natural tells on which 
   premise of the current goal the induction acts, starting from 1, counting both 
   dependent and non-dependent products, but skipping local definitions. *)

   (* This example is very lax, do not really need to apply/Kstep... fix generates a very
      crude induction hypothesis*)
by fix IHt 1 => -[m st]; apply/Kstep=> i; apply: IHt. Defined.


(* Also from finfun.v (example commented out): an artificial example use of dependent 
  functions.                          *)
Inductive tri_tree n := tri_row of {ffun forall i : 'I_n, tri_tree i}.
Fixpoint tri_size n (t : tri_tree n) :=
  let: tri_row f := t in sumn [seq tri_size (f i) | i : 'I_n] + 1.

Example tri_tree_step (K : forall n, tri_tree n -> Type) :=
  forall n st (t := tri_row st) & forall i : 'I_n, K i (st i), K n t.
Example tri_tree_rect' K (Kstep : tri_tree_step K) : forall n t, K n t.
Proof. by fix IHt 2 => m [st]; apply/Kstep=> i; apply: IHt. Defined.


(* Appears as the example "tree3", appearing as a note in the paper: 
 "Since Mathematical Components version 1.9 the definition of finite functions changed.
  The new mplementation is based on a specific list-like data type indexed over the list 
  of the elements of the domain. Thanks to this more sophisticated ecoding, the current 
  Coq type checker accepts, for example, the following declaration of a 
  3-branch tree: Inductive tree3 := Leaf of nat | Node of {ffun ’I_3 -> tree3}." *) 

Inductive tree_n := Leaf_n of nat | Node_n of {ffun 'I_n -> tree_n}.

Fixpoint size_n t := match t with
      | Leaf_n m => 1
      | Node_n ff => sumn (codom ( size_n \o (fun z => ff z))) + 1 
      end.



(* this is non recursive, we test locally, the exploration of the entire tree
   is done via tree_n_myrect (who recurses ? ) *)
Definition treeProp_step PL PN (t:tree_n) : Type:= 
       match t with 
              | Leaf_n m => PL m
              | Node_n ff => forall (i:'I_n), PN (ff i) 
       end.


Example tree_n_myrect (PL: nat -> Type) (PN: tree_n -> Type)  
                      (t: tree_n) 
       : treeProp_step PL PN  t.
Proof.
move: t;  fix IHt 1; apply: IHt.
Abort.

(* The examples above do not look very interesting .... Just show some uses if finfun. 
   and notation 'ffun' *)
End More_Finfun_Tree_Trials.


Section FinFunProperties.
  Variable (aT : finType). (* domain type *)
  Variable (rT : eqType). (* codomain type *)

(* Equip finfun with eq type ; first check this is not available from first encounter
   with HB.*)
Check finfun_type bool bool: Type.
Fail Check finfun_type bool bool: eqType.
Fail Check finfun_type aT rT: eqType.


HB.about hasDecEq.Build.
Definition finfun_eq  (f1 f2: finfun_type aT rT): bool
    :=  fgraph f1 == fgraph f2.

Lemma finfun_eqP: Equality.axiom finfun_eq.
Proof.
move=>x y.
apply/(iffP idP) => Hyp. 
by move: Hyp; elim x => tx; elim y => ty; rewrite /finfun_eq /fgraph=> H; rewrite (eqP H).
by rewrite  Hyp /finfun_eq /fgraph; elim y =>//=.
Qed.

#[log, verbose]
HB.instance Definition _ := @hasDecEq.Build (finfun_type aT rT) _ finfun_eqP .

Check finfun_type aT rT: eqType.
Check (#|aT|.-tuple rT):eqType.
End FinFunProperties.

Section FinFunProperties_Finite.
  Variable (aT : finType). (* domain type *)
  Variable (rT : finType). (* codomain type *)

  Check (#|aT|.-tuple rT):finType.


  Check (#|aT|.-tuple rT):eqType.
  Check (#|aT|.-tuple rT):finType.
  Check (#|aT|.-tuple rT):choiceType.
  Check (#|aT|.-tuple rT):countType.

  

  Check [Countable of (#|aT|.-tuple rT) by <: ]. 
  Fail Check (finfun_type aT rT):choiceType.
  Fail Check (finfun_type aT rT):countType.
  Fail Check (finfun_type aT rT):finType.

  Fail Check (finfun_type aT rT):finType. 
  #[log, verbose]
  HB.instance Definition _ :=  [Countable of (finfun_type aT rT) by <: ].

  Check (finfun_type aT rT):eqType.
  Check (finfun_type aT rT):choiceType.
  Check (finfun_type aT rT):countType.
  Fail Check (finfun_type aT rT):finType.

  #[log, verbose]
  HB.instance Definition _ :=  [Finite of (finfun_type aT rT) by <:].

  Fail Check (finfun_type aT rT):finType.

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

