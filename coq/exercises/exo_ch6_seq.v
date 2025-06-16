(* We load a minimum of ssreflect, so as to exclude seq. This way we
  need to build a (minimal seq theory). This way we our structures will
  not be absorbed by "seq" equivalent. *)
(* Note: in view of the examples we want to test, it is necessary to 
         Import ssrnat, to make nat an eqType!
*)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From HB Require Import structures.

Require Import libSsr.LibNat.
Require Import libSsr.LibLogic.
Require Import libSsr.LibAllSsr.

Set Implicit Arguments.

(* (Generic) Theory of sequence in Chap 6.6  *)

Section SeqTheory.

Context {T : eqType}.
(* Variable T : eqType. *)

Inductive suite (T : Type) : Type := Nil | Cons of T & suite T.
Declare Scope suite_scope.
Bind Scope suite_scope with suite.
Delimit Scope suite_scope with SUITE.

Arguments cons {T%_type} x.
Arguments nil {T%_type} . 
Implicit Type s : suite T.

Infix "::" := Cons : suite_scope.
Notation "[ :: ]" := Nil (at level 0, format "[ :: ]") : suite_scope.
Notation "[ :: x1 ]" := (Cons x1 Nil)
                         (at level 0, format "[ ::  x1 ]") : suite_scope.
Notation "[ x1 :: s2 ]" := (Cons x1 s2)
                         (at level 0, format "[ x1 :: s2 ]") : suite_scope.


(*
Check (Cons 1 (Nil nat)).
Check  [ :: 1 ]  .
Open Scope suite_scope.
Check (cons 1 nil)%SUITE.
Check [ :: 1 ]%SUITE.
*)




(* Membership in a sequence *)
Fixpoint mem_seq (s:suite T) x := if s is (Cons y  s' )
                          then (y == x) || mem_seq s' x
                          else false.

Fixpoint suitecat s1 s2:= 
    if s1 is (Cons x  s1') 
       then (Cons x  (suitecat s1'  s2)) else s2.


Fixpoint uniq s := if s is (Cons x s') 
                      then (negb ( mem_seq s' x)) && uniq s' 
                      else true.

Fixpoint undup s := if s is (Cons x s') 
                      then
                        if mem_seq s' x 
                          then undup s' 
                          else Cons x (undup  s')
                      else Nil T.

(* Proofs about such concepts can be made pretty much as if the type T 
was nat or bool, i.e. our predicates do compute. *)

Lemma in_cons y s x : (mem_seq   (Cons y  s) x ) = (x == y) || (mem_seq s x).
Proof.
by move=>//=; rewrite {1}eq_sym.
Qed.

Definition eq_mem_suite mp1 mp2 := forall x : T, 
                              mem_seq mp1 x = mem_seq mp2 x.

Lemma mem_undup_suite s: eq_mem_suite (undup s)  s.
Proof.
 move=> x; elim: s => //= y s IHs.
 case Hy: (mem_seq s y); last by rewrite in_cons IHs {1}eq_sym.
 rewrite IHs. by case:eqP   => H //=; rewrite -H.
Qed.

Lemma undup_uniq s : uniq (undup s).
Proof.
by elim s => //= a l IH;
     case Eail: (mem_seq l a ) => //=;
     rewrite //=  mem_undup_suite Eail.  
Qed.


Fixpoint eqsuite s1 s2 {struct s2} :=
        match s1, s2 with
          | Nil, Nil => true
          | Cons x1  s1', Cons x2 s2' => (x1 == x2) && eqsuite s1' s2'
          | _, _ => false
        end.

Lemma eqsuiteP : Equality.axiom eqsuite.
Proof.
elim => [ | x s IH] [ | x' s'] /= ;   do? [exact: ReflectT | exact: ReflectF].
(* Note: reflect (x = x') (x == x') = (x =P x'). *) 
case: (x =P x') => [<-| neqx]; last  by apply ReflectF  => -[eqx _]. 
by apply: (iffP (IH _) ) => [<-|[]]. 
Qed.

Check T:eqType.
Fail Check suite T:eqType.

(* Equivalent formulations, keeping second:
   HB.instance Definition suite_eqMixin := hasDecEq.Build (suite T) eqsuiteP.
*)

HB.instance Definition _ := Equality.Mixin eqsuiteP.

(* This makes suite T into an eqType *)
Check T:eqType.
Check suite T:eqType.

End SeqTheory.

Section TEST.
Variable T:eqType.
Check T: eqType.
Check suite T: eqType.
Check nat:eqType.
Check suite nat:eqType.
End TEST.


(* See if this  works*)
Section Experiment.
Let s1 := Cons 1 (Cons 2 (Nil nat)).
Let s2 := Cons 3 (Cons 5 (Cons 7 (Nil nat))).
Let ss : suite (suite nat) := Cons s1  (Cons s2 (Nil( suite nat))) .


Check  (@mem_seq _ ss s1).
Check  (ss != Nil (suite nat)).
Check ( (ss != Nil (suite nat))  && (mem_seq  ss s1)).
Check undup_uniq ss.
Check ss.
End Experiment.




