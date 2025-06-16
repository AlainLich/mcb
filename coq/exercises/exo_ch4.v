From mathcomp Require Import all_ssreflect.

Require Import libSsr.LibNat.
Require Import libSsr.LibLogic.
Set Implicit Arguments.

(* Idea: try to do these without cheating, these are all in ssreflect's
   library.
   Implementation: still a TBD.....
*)

(* 4.2.1 Primes, a never ending story *)
Section Chap_4_2_1.

(* Inductive ex2 A P Q : Prop := ex_intro2 x of P x & Q x. *)
(* Notation "exists2 x , p & q" := (ex2 (fun x => p) (fun x => q)). *)

(* Notation "n ` !" := (factorial n). *)
(* Lemma fact_gt0 n : 0 < n`!. *)
(* Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!. *)
(* Lemma pdivP n : 1 < n -> exists2 p, prime p & p %| n, *)
(* Lemma dvdn_addr m d n : d %| m -> (d %| m + n) = (d %| n). *)
(* Lemma gtnNdvd n d : 0 < n -> n < d -> (d %| n) = false. *)
End Chap_4_2_1.


(* 4.2.2 Order and max, a matter of symmetry *)
Section Chap_4_2_3.

(* Lemma orP {a b : bool} : a || b -> a \/ b. *)
(* Lemma orb_idr (a b : bool) : (b -> a) -> (a || b) = a. *)
(* Lemma orbC a b : a || b = b || a. *)
(* Lemma maxn_idPl {m n} : n <= m -> maxn m n = m. *)
(* Lemma maxnC m n : maxn m n = maxn n m. *)
(* Lemma leq_total m n : (m <= n) || (n <= m). *)
End Chap_4_2_3.
