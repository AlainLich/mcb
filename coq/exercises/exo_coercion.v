From mathcomp Require Import ssreflect.
From HB Require Import structures.


(* Added, consists of copies of examples in Coq's Manual (online) *)

Section Example1. 
        (*
            f a is ill-typed where f:forall x:A,B and a:A'. 

            If there is a coercion path between A' and A, then f a is transformed 
            into f a' where a' is the result of the application of this coercion
            path to a.

            We first give an example of coercion between atomic inductive types
        *)

        Fail Check (0 = true). 

        Definition bool_in_nat (b:bool) := if b then 0 else 1.
        Coercion bool_in_nat : bool >-> nat.

        Check (0 = true). (* 0 = true: Prop *)

        Set Printing Coercions.
        Check (0 = true). (* 0 = bool_in_nat true: Prop*)

        Fail Check (true = 0). (*  This is "normal" behavior of coercions. To validate
                                true=O, the coercion is searched from nat to bool.
                                There is none. i.e. currying: when true is seen the typing
                                is "oriented" towards a bool equality, requiring a nat->bool
                                coercion.*)

        Unset Printing Coercions.

End Example1.

Section Example2.
        (* We give an example of coercion between classes with parameters. *)

        Parameters (C : nat -> Set) (D : nat -> bool -> Set) (E : bool -> Set).

        Parameter f : forall n:nat, C n -> D (S n) true.
        Coercion f : C >-> D.

        Parameter g : forall (n:nat) (b:bool), D n b -> E b.
        Coercion g : D >-> E.

        Parameter c : C 0.
        Parameter T : E true -> nat.

        Check (T c). (* T c  : nat *)

        Set Printing Coercions.
        Check (T c). (* T (g 1 true (f 0 c))  : nat *)

        Unset Printing Coercions.
End Example2.

Section Example3.
(* In the case of functional arguments, we use the monotonic rule of
  sub-typing. To coerce t : forall x : A, B towards forall x : A', B',
   we have to coerce A' towards A and B towards B'. An example is given below:
*)

        Parameters (A B : Set) (h : A -> B).
        Coercion h : A >-> B.

        Parameter U : (A -> E true) -> nat.
        Parameter t : B -> C 0.

        Check (U t). (* U (fun x : A => t x) : nat *)
        Set Printing Coercions.
        Check (U t). (* U (fun x : A => g 1 true (f 0 (t (h x)))) : nat *)

        Unset Printing Coercions.
        (* Remark the changes in the result following the modification of the previous 
        example. *)
        Parameter U' : (C 0 -> B) -> nat.
        Parameter t' : E true -> A.

        Check (U' t'). (* U' (fun x : C 0 => t' x) : nat *)
        Set Printing Coercions.
        Check (U' t'). (* U' (fun x : C 0 => h (t' (g 1 true (f 0 x)))) : nat *)
        Unset Printing Coercions.
End Example3.

Section Example4.
        (* Coercion to a type

        An assumption x:A when A is not a type, is ill-typed. It is replaced by
        x:A' where A' is the result of the application to A of the coercion path
        between the class of A and Sortclass if it exists. 

        This case occurs in the abstraction fun x:A => t, universal quantification
        forall x:A,B, global variables and parameters of (co)inductive definitions 
        and functions.
        In forall x:A,B, such a coercion path may also be applied to B if necessary. *)

        Parameter Graph : Type.
        Parameter Node : Graph -> Type.
        Parameter G : Graph.

        Fail Parameter Arrows : G -> G -> Type.
            (*  The command has indeed failed with message:
                The term "G" has type "Graph" which should be Set, Prop or Type.
            *)

        Coercion Node : Graph >-> Sortclass.
        Parameter Arrows : G -> G -> Type.

        Check Arrows. (* Arrows  : G -> G -> Type *)

        Parameter fg : G -> G.
        Check fg. (* fg: G -> G *)

        Set Printing Coercions.
        Check fg. (* fg: Node G -> Node G *)

        Unset Printing Coercions.
End Example4.

Section Example5.
        (* Example: Coercion to a function

            (f a) is ill-typed because f:A is not a function. The term f is replaced by 
            the term obtained by applying to f the coercion path between A and Funclass
            if it exists.
        *)
        Parameter bij : Set -> Set -> Set.
        Parameter b : bij nat nat.

        Fail Check (b 0). (* The command has indeed failed with message:
                            Illegal application (Non-functional construction): 
                            The expression "b" of type "bij nat nat" cannot be applied
                            to the term  "0" : "nat"*)

        Parameter ap : forall A B:Set, bij A B -> A -> B.
        Coercion ap : bij >-> Funclass.


        Check (b 0). (* b 0 : nat *)
        Set Printing Coercions.

        Check (b 0). (* ap nat nat b 0  : nat *)
        Unset Printing Coercions.
End Example5.


Section Example6.
        (* Example: Reversible coercions
        Notice the :> on ssort making it a reversible coercion.
        *)
        Structure S := {
        ssort :> Type;
        sstuff : ssort;
        }.
        Definition test (s : S) := sstuff s.
        Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.
        Check test (nat : Type). (* test (nat : Type)  : nat *)

        (* For comparison *)

        Structure S''' := {
        ssort'''  : Type;
        sstuff''' : ssort''';
        }.
        Definition test''' (s : S''') := sstuff''' s.
        Canonical Structure S_nat''' := {| ssort''' := nat; sstuff''' := 0; |}.
        Fail Check test''' (nat : Type). 
        (* The command has indeed failed with message:
           The term "nat : Type" has type "Type" while it is expected to have 
           type "S'''". *)
End Example6.

Section Example7.
(* Example: Reversible coercions using the reversible attribute
  Notice there is no :> on ssort' and the added Coercion compared to the previous
 example.
*)
Structure S' := {
  ssort' : Type;
  sstuff' : ssort';
}.
Coercion ssort' : S' >-> Sortclass.
Definition test' (s : S') := sstuff' s.
Canonical Structure S_nat' := {| ssort' := nat; sstuff' := 0; |}.
(*
  Since there's no :> on the definition of ssort', the reversible attribute is
  not set:
*)
Fail Check test' (nat : Type).
(*
The command has indeed failed with message:
The term "nat : Type" has type "Type" while it is expected to have type "S'".
*)


(* The attribute can be set after declaring the coercion:*)

#[reversible] Coercion ssort'.
Check test' (nat : Type). (* test' (nat : Type) : nat *)

End Example7.


Section Example8.
        (* Example: Identity coercions. 
           Idea: To make coercions work for both a named class and for Sortclass
           or Funclass, use the Identity Coercion command. 
        *)
        Definition fct := nat -> nat.
        Parameter incr_fct : Set.
        Parameter fct_of_incr_fct : incr_fct -> fct.
        Fail Coercion fct_of_incr_fct : incr_fct >-> Funclass.
        (* The command has indeed failed with message:
        Found target class Funclass instead of fct. *)

        Coercion fct_of_incr_fct : incr_fct >-> fct.
        Parameter f' : incr_fct.
        Check f' : fct. (* f' : fct : fct *)
        Fail Check f' 0. (*
                            The command has indeed failed with message:
                            Illegal application (Non-functional construction): 
                            The expression "f'" of type "incr_fct" cannot be applied to
                            the term "0" : "nat"*)

        Identity Coercion Id_fct_Funclass : fct >-> Funclass.
        Check f' 0. (* f' 0 : nat *)


        Print Coercion Paths  fct Funclass. 
            (* [fct_of_incr_fct; Id_fct_Funclass] : incr_fct >-> Funclass *)
        Print Coercion Paths  incr_fct Funclass.
            (* [fct_of_incr_fct; Id_fct_Funclass] : incr_fct >-> Funclass *)

End Example8.

(* Move to the Typeclass section of the Manual *)
Section ExampleTC1.

Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y }.
(*    This typeclass implements a boolean equality test which is compatible 
      with Leibniz equality on some type. An example implementation is:
*)

Instance unit_EqDec : EqDec unit :=
  { eqb x y := true ;
    eqb_leibniz x y H := match x, y return x = y with
                            | tt, tt => eq_refl tt
                         end }.

(* Using the refine attribute, if the term is not sufficient to finish the
  definition (e.g. due to a missing field or non-inferable hole) it must be 
  finished in proof mode. If it is sufficient a trivial proof mode with no open
 goals is started.
*)

#[refine] Instance unit_EqDec' : EqDec unit := { eqb x y := true }.
Proof. intros [] []. reflexivity. Defined.
(* Note that if you finish the proof with Qed the entire instance will be opaque,
  including the fields given in the initial term. *)


End ExampleTC1.