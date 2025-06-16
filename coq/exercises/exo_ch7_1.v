From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Require Import libSsr.LibAllSsr.

(* Ease of use *)
Lemma eq_op_CR (T:eqType )(x y:T): (x == y) = (y == x).
Proof. by []. Defined.

Module GenLenTuple.
 
Inductive ltuple_of n T := LTuple { tval :> seq T;
                                    pr_sz : size tval == n }.

Notation "n .-ltuple T" := (ltuple_of n T) (at level 2).

(* This already works by coercing to seq!*)
Example just_tuple0 n (t : n.-ltuple  nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. 
by rewrite size_rev size_map  size_rev.
Defined.


(* Taken from tuple.v in the library, shows the use of HB.instance, with some effect
   since this is required for proving Remark size_ltuple. *)
Section TupleDef.

Variables (n : nat) (T : Type).

(* This emits a diagnostic but allows to prove size_ltuple in the next lemma.
   Apparently it seems required to refer to section's variables.
   From eqtype.v;    [isSub for S_val] := [isSub of _ for S_val]  clones the canonical 
   subType structure for S.                       
   
   This defines the following
   GenLenTuple_ltuple_of__canonical__eqtype_SubType: 
                   subType (T:=seq T) (fun x : seq T => size x == n)
*)
(* Global Canonical GenLenTuple_ltuple_of__canonical__eqtype_SubType.
          : subType (T:=seq T) (fun x : seq T => size x == n)

   Global Canonical HB_unnamed_factory_11.
*)
#[log, verbose]
HB.instance Definition _ := [isSub  for (tval n T)].
About GenLenTuple_ltuple_of__canonical__eqtype_SubType.

Remark size_ltuple : forall  (t : n.-ltuple T), size t = n.
Proof.
    move => t.
    exact: (eqP (valP t)). 
Qed.

Remark decomp_tuple : forall (x:n.-ltuple T), 
                        {l:seq T & (size l = n) /\  ((tval _ _  x) = l) }.
Proof.
move => x; set l:= (tval _ _ x).
exists l.  by split; first by rewrite /l => -{l}; elim: x => tv pr;apply/eqP.   
Qed.

End TupleDef.

(* Now we follow the route of adding a FullTuple type (redundant with librarie's) for
   experimenting.
*)

(* This structure with 2 levels owes much to the example in HB: HB/examples/readme.v.
   I would like to see if putting all the data alone in basicTuple and most axioms in 
   GLTuple, makes things easier. (In particular when looking at recognizing equality.)
*)

(*
   Module Exports.
     Global Arguments Axioms_ {_}.
   End Exports.
   Notation BasicTuple_of X1 := ( BasicTuple_of.phant_axioms X1).
*)
#[log, verbose]
HB.mixin Record BasicTuple_of (T:eqType) := {
    glen :> nat;
    gval :> ltuple_of glen T;
}.
HB.about BasicTuple_of.
About BasicTuple_of.

(*
Module Exports.
#[reversible] Coercion sort : GenLenTuple.basicTuple.type >-> eqtype.Equality.type.
#[reversible] Coercion GenLenTuple_BasicTuple_of_mixin : GenLenTuple.basicTuple.axioms_ >-> GenLenTuple.BasicTuple_of.axioms_.
End Exports.

Notation basicTuple X1 := ( basicTuple.axioms_ X1).
 *)
#[primitive, log, verbose] (***)
HB.structure Definition basicTuple:= {T of BasicTuple_of T & }.
About basicTuple.
HB.about basicTuple.

(* Very complex log output ... summary:
      HB: GLTuple_of is a factory (from "(stdin)", line 6)
      HB: GLTuple_of operations and axioms are:
         - ln_ok
         - has_cons
         - has_map
         - has_rev
         - mapA
      HB: GLTuple_of requires the following mixins:
         - BasicTuple_of
      HB: GLTuple_of provides the following mixins:
         - GLTuple_of
*)
#[log, verbose] 
HB.mixin Record GLTuple_of (T:eqType) of BasicTuple_of T := {
    ln_ok: forall n, BasicTuple_of.glen T n  == size (tval _ _ (BasicTuple_of.gval T n ));
    has_cons: forall (n:nat) (s: ltuple_of n T) (x:T), size (x::s) == n.+1;

    has_map:  forall (S:Type) (n:nat) (s: ltuple_of n T) (f : T -> S), 
                  size (map f s) == n;
    has_rev: forall (n:nat) (s: ltuple_of n T), size (rev s) == n;

    mapA:forall  (S R : eqType) (n:nat) (s: ltuple_of n T) 
                  (f : T -> S) (g: S -> R), 
              map g (map f s)  = map  (g \o f) s ;
  
}.
About GLTuple_of.
HB.about GLTuple_of.

(* Shows coercions:
Module Exports.
      #[reversible] Coercion sort : GenLenTuple.fullTuple.type >-> eqtype.Equality.type.
      Definition GenLenTuple_fullTuple_class__to__GenLenTuple_basicTuple_class : 
         forall T : eqType, axioms_ T -> basicTuple.axioms_ T :=
            fun (T : eqType) (c : axioms_ T) =>
            {| basicTuple.GenLenTuple_BasicTuple_of_mixin :=
               GenLenTuple_BasicTuple_of_mixin _ c|}.

      #[reversible] Coercion GenLenTuple_fullTuple_class__to__GenLenTuple_basicTuple_class : 
         GenLenTuple.fullTuple.axioms_ >-> GenLenTuple.basicTuple.axioms_.

      Definition GenLenTuple_fullTuple__to__GenLenTuple_basicTuple : 
         type ->  basicTuple.type := fun s : type => {| basicTuple.sort := s; basicTuple.class := class s |}.

      #[reversible] Coercion GenLenTuple_fullTuple__to__GenLenTuple_basicTuple : 
          GenLenTuple.fullTuple.type >-> GenLenTuple.basicTuple.type.
      Global Canonical GenLenTuple_fullTuple__to__GenLenTuple_basicTuple.
      #[reversible] Coercion GenLenTuple_BasicTuple_of_mixin : 
          GenLenTuple.fullTuple.axioms_ >-> GenLenTuple.BasicTuple_of.axioms_.
      #[reversible] Coercion GenLenTuple_GLTuple_of_mixin :
           GenLenTuple.fullTuple.axioms_ >-> GenLenTuple.GLTuple_of.axioms_.
End Exports.
*)
#[primitive, log, verbose] (***)
HB.structure Definition fullTuple:= {T of GLTuple_of T & }.

Definition mk_tuple_of (T:Type) (s: seq T):= 
     let sz:= size s in {| tval := s; 
                            pr_sz:= eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) sz |}. 

(* Generalizing the specification of mk_tuple_of, here we use pf as a (don't care )placehoder
   since we have eq proof irrelevance *)
Remark R_spec_mk_tuple_of (A:Type) (l: list A):  mk_tuple_of _ l 
        = let pf:= @eq_refl Datatypes_nat__canonical__eqtype_Equality (size l) 
          in {| tval:=l; pr_sz:= pf   |}.
Proof.
  by rewrite /mk_tuple_of. 
Qed.


(* First attempt, this is probably not explicit enough, we try a more explicit expression below*)
Definition mk_basic_tuple_of_seq' (T:eqType) (s: seq T): basicTuple (T:eqType).
Proof. 
    constructor.
    apply: {| BasicTuple_of.glen:= (size s) ; |}.
    have hsz: (size s) == (size s); first by [].
    by apply  {| tval:= s;pr_sz := hsz |}.
Defined.

(* Generates:
    mk_basic_tuple_of_seq' =
    fun (T : eqType) (s : seq T) =>
    {|
        basicTuple.GenLenTuple_BasicTuple_of_mixin :=
        {|
          BasicTuple_of.glen := size s;
          BasicTuple_of.gval :=
             ssr_have_upoly
                (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (size s))
                 [eta LTuple (size s) T s]
        |}
    |}
     : forall T : eqType, seq T -> basicTuple.axioms_ (T : eqType)

Arguments mk_basic_tuple_of_seq T s%seq_scope
*)
(* Try a more  explicit expression *)
Definition mk_basic_tuple_of_seq (T:eqType) (s: seq T)
     : basicTuple (T:eqType)
     := {|
          basicTuple.GenLenTuple_BasicTuple_of_mixin :=
            {|
               BasicTuple_of.glen := size s;
               BasicTuple_of.gval :=  mk_tuple_of T s;
         |}
        |}.


Definition mk_full_tuple_of_seq (T:eqType) (s: seq T): fullTuple (T:eqType).
Proof.
   econstructor. 
    (* Here we handle the BasicTuple items, which handle the "data" part *)
   Unshelve. all: swap 1 2.  
   by apply: mk_basic_tuple_of_seq. 

   constructor. 

    by case => len tup; elim: tup => s1 pr;  rewrite eq_op_CR.
    by move => n tup x; elim: tup => s1 pr //=.
    by move => S n tup; elim: tup => s1 pr f; rewrite size_map.
    by move => n tup;  elim tup=> s1 pr; rewrite size_rev.
    by move => S R n tup f g; rewrite map_comp. 
Defined.



Definition mk_full_tuple_of_basic (T:eqType) (n:nat) (t: basicTuple T): fullTuple (T:eqType).
Proof.
    econstructor.
    Unshelve. all: swap 1 2. 
    by apply t.

    constructor. 

    by case => len tup; elim: tup => s1 pr;  rewrite eq_op_CR.

    by move => m tup x; elim: tup => s1 pr //=.
    by move => S m tup; elim: tup => s1 pr f; rewrite size_map.
    by move => m tup;  elim tup=> s1 pr; rewrite size_rev.
    by move => S R  m tup f g;  rewrite map_comp. 
Defined.


(* This shows the expected 'data' fields , but complemented by proofs of axiom
 compliance. *)

Remark R0 (T: eqType): forall (s: seq T), 
             BasicTuple_of.gval _ (mk_basic_tuple_of_seq _ s) = mk_tuple_of _ s.
Proof. by []. Defined.

Remark R1 (T: eqType): forall (s: seq T), 
             BasicTuple_of.glen _ (mk_basic_tuple_of_seq _ s) == size s.
Proof. by []. Defined.


(* At this stage, we have no defined coercion, but : *)
Remark R2 (T: eqType): forall (s: seq T), 
              tval _ _ (BasicTuple_of.gval _ (mk_full_tuple_of_seq _ s)) == s.
Proof. by [].  Qed.


Definition full_tuple_to_seq (T: eqType) : (fullTuple T) -> (seq T)
                :=fun (ft: (fullTuple T)) => tval _ _ (BasicTuple_of.gval _ ft).


Remark inv_mk_full_tuple (T:eqType): forall (s:seq T), 
               s =  full_tuple_to_seq _ (mk_full_tuple_of_seq _ s).
Proof. by []. Qed.


Remark size_glen (T:eqType) (tup : basicTuple T):
  let tv:= BasicTuple_of.gval T tup  in 
    BasicTuple_of.glen T tup  == size (tval (BasicTuple_of.glen T tup) (Equality.sort T) tv ). 
Proof.
  einduction tup. 
  rewrite /BasicTuple_of.glen /BasicTuple_of.gval => //=.
  elim GenLenTuple_BasicTuple_of_mixin => gl [tv pr].
  by rewrite  (eqP pr).
Qed.

Remark decomp_full_tuple : forall n T (tup:fullTuple T), 
                        n = (BasicTuple_of.glen _  tup) -> 
                        {l:seq T & (size l = n) /\  ((tval _ _  (BasicTuple_of.gval _  tup)) = l) }.
Proof.
move => n T tup Hsz. 
exists (tval _ _  (BasicTuple_of.gval _  tup)).  
split;  move =>//;  rewrite Hsz.
elim tup =>//= Bcomp [LemSize LemCons LemMap LemRev LemComp].
by rewrite -(eqP (LemSize Bcomp)). 
Qed.

Remark decomp_basic_tuple : forall n T (tup:basicTuple T), 
                        n = (BasicTuple_of.glen _  tup) -> 
                        {l:seq T & (size l = n) /\  ((tval _ _  (BasicTuple_of.gval _  tup)) = l) }.
Proof.
   move => n T tup Hsz. 
   exists (tval _ _  (BasicTuple_of.gval _  tup)).  
   split;  move =>//;  rewrite Hsz.
   elim tup =>//= btup.
   induction btup. 
   apply: eqP (pr_sz _ _ gval0).
Qed.


Section EqType_makes_full_tuples.

    Definition T_full_tuple (T:eqType) (n: nat) (habitant:T): 
          fullTuple.axioms_ T.
    Proof.
    econstructor.
    Unshelve.
    all: swap 1 2.
       econstructor. 
          Unshelve.
          all: swap 1 3. 
             by apply n.
          all: swap 1 2.
             by have :=(mk_tuple_of _ (nseq n  habitant)); rewrite size_nseq.
          simpl.

          constructor. 
             {move => tup; einduction tup. 
              by elim gval0 => tv pr //=; rewrite (eqP pr).
             }
             { move => m tup x. einduction tup. 
              by simpl; rewrite (eqP pr_sz0).
             }
             { move => S m tup f.   einduction tup.
                by rewrite size_map.
             }
             { move => m tup. einduction tup. simpl.
               by rewrite size_rev.
             }
             {
              move => S R m tup f g . einduction tup.
              by  rewrite map_comp.
             }
    Qed.

End EqType_makes_full_tuples.


Definition nat_full_tuple_:  fullTuple.axioms_ nat.
Proof.
    by apply T_full_tuple; apply 0.
Defined.
Canonical nat_full_tuple:= fullTuple.Pack nat  (nat_full_tuple_) . 
About nat_full_tuple.

Definition bool_full_tuple_:  fullTuple.axioms_ bool.
Proof.
apply T_full_tuple.  apply 0. apply true.
Defined.
Canonical bool_full_tuple:= fullTuple.Pack bool  (bool_full_tuple_) . 
About bool_full_tuple.


Section Provide_Coercions.
Variables (T: eqType).

Definition seq_to_full_tuple (s: seq T): fullTuple T.
Proof.
   by apply  (mk_full_tuple_of_seq _ s).
Qed.

Definition seq_to_basic_tuple (s: seq T): basicTuple T.
Proof.
   by apply  (mk_basic_tuple_of_seq _ s).
Qed.

Definition basic_to_full_tuple (bt: basicTuple T): fullTuple T.
Proof.
  induction bt as (btAxs).
  elim btAxs => n tup.
  apply  (seq_to_full_tuple tup).
Qed.

End Provide_Coercions.

Definition seq_to_full_tuple_nat (s: seq nat): fullTuple nat
              := seq_to_full_tuple _ s.

Definition seq_to_full_tuple_bool (s: seq bool): fullTuple bool
              := seq_to_full_tuple _ s.

Definition seq_to_full_tuple_T (T:eqType) (s: seq T): fullTuple T
              := seq_to_full_tuple _ s.

#[log, verbose]
HB.instance Definition _ (T:eqType) (s : seq T) : fullTuple T := seq_to_full_tuple_T T s.

#[log, verbose]
HB.instance Definition _ (s : seq nat) : fullTuple nat := seq_to_full_tuple_nat s.

(* #[log, verbose]
HB.instance Definition _ (s : seq bool) : fullTuple bool := seq_to_full_tuple_bool s. *)


#[log, verbose]
HB.instance Definition _ (T:eqType) (s : basicTuple T) : fullTuple T := basic_to_full_tuple T s.

#[log, verbose]
HB.instance Definition _ (s : basicTuple nat) : fullTuple nat := basic_to_full_tuple nat s.

(* #[log, verbose]
HB.instance Definition _ (sb : basicTuple bool) : fullTuple bool := basic_to_full_tuple bool sb. *)


End GenLenTuple.
Import GenLenTuple.
Print Module GenLenTuple.

(* Here we do should attempt to use the Canonical properties to 
   facilitate/automate the proof TBD TBD *)

Example just_tuple n (t : n.-ltuple  nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. 
by rewrite size_rev size_map  size_rev.
Defined.

Example just_tuple' n (t : n.-ltuple  nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. 
  by apply/eqP; rewrite size_rev size_map size_rev. 
Qed.

Example just_tuple'' n (t : n.-ltuple  nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. 
  rewrite size_rev.  
  case :(decomp_tuple _ _ t) => t' [Ht Ht'].
  rewrite Ht' in Ht *. 
  by rewrite Ht size_map size_rev. 
Qed.

Check (nat_full_tuple).

Example just_nat_full_tuple  (t : nat_full_tuple): t == t.
Proof. by []. Qed.
Set Printing Coercions.
Print just_nat_full_tuple .

Section Try_It_2.
Variables (T: eqType) (n: nat)  (tt : nat_full_tuple).

Check mk_full_tuple_of_seq _ [:: 1; 2; 3]: fullTuple _ .
Check mk_full_tuple_of_seq _ [:: 1; 2; 3]:> fullTuple _ .
Check mk_full_tuple_of_seq _ [:: 1; 2; 3]:> fullTuple nat .
Check mk_full_tuple_of_seq _ [:: 1; 2; 3]:> basicTuple nat .
Check mk_full_tuple_of_seq nat [:: 1; 2; 3] :> fullTuple _  .
Check mk_full_tuple_of_seq nat [:: 1; 2; 3] :> basicTuple _  .
Fail Check mk_full_tuple_of_seq nat [:: 1; 2; 3] :> ltuple_of _ _ .

Check mk_basic_tuple_of_seq nat [:: 1; 2; 3] :> basicTuple _  .
Fail Check mk_basic_tuple_of_seq nat [:: 1; 2; 3] :> fullTuple nat  .
Fail Check mk_basic_tuple_of_seq _ [:: 1; 2; 3]: fullTuple _ .


End Try_It_2.

(* Here, we would like to coerce to lift to nat_full_tuple a tuple proof ...*)
(* THIS FAILS ... TBD Look into this
Example just_tupleG n (t : nat_full_tuple) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. 
by rewrite size_rev size_map  size_rev.
Defined.
*)
