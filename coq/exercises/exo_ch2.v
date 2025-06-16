From mathcomp Require Import all_ssreflect.

Require Import libSsr.LibNat.
Require Import libSsr.LibLogic.
Set Implicit Arguments.

(* Idea: try to do these without cheating, these are all in ssreflect's
   library.
*)

(* 2.1.2 Identities *)

(* associativity*)
Lemma addnA (m n k : nat) : m + (n + k) = m + n + k.
Proof.
by move :  n k;
 elim m => [ // | l IH n k]; rewrite /addn //= -/addn IH. 
Qed.

Lemma orbT b : b || true = true. 
Proof.
by case: b => //.
Qed.

Lemma orbA b1 b2 b3 : b1 || (b2 || b3) = b1 || b2 || b3. 
Proof.
case :b1 =>//. (* apparently this is sufficient, the rest is computed*)
Qed.

Lemma orbA' b1 b2 b3 : b1 || (b2 || b3) = b1 || b2 || b3. 
Proof.
by move: b1 b2 b3; do 3!case. (* this looks like the library file's
                                 and results in a larger proof term!*)
Qed.

Lemma implybE a b : (a ==> b) = ~~ a || b. 
Proof.
case: a =>//.
Qed. 

Lemma negb_and (a b : bool) : ~~ (a && b) = ~~ a || ~~ b.
Proof.
case: a =>//.
Qed.


(* 2.1.3 From boolean predicates to formal statements *)

Lemma leq0n (n : nat) : 0 <= n = true.
Proof.
by move => //.
Qed.

Lemma eqn_leq m n : (m == n) = (m <= n) && (n <= m). 
Proof.
Locate Datatypes_nat__canonical__eqtype_Equality.
(* m,n have type "Constant
     mathcomp.ssreflect.ssrnat.Datatypes_nat__canonical__eqtype_Equality"
*)
elim: m n =>[ | n IH] []; move =>//.  
Qed.

Lemma neq_ltn m n : (m != n) = (m < n) || (n < m). 
Proof.
elim: m n =>[ | n IH] []; move =>//. 
Qed.

Lemma leqn0' n : (n <= 0) = (n == 0). 
Proof.
case: n =>//.
Qed.

Lemma dvdn1 d : (d %| 1) = (d == 1).
Proof.
case : d =>[// | d']. 
by rewrite /dvdn; case : d'.
Qed.

(* get (redo) some tools *)
Lemma oddS n : odd n.+1 = ~~ odd n. Proof. by []. Qed.

Lemma oddb (b : bool) : odd b = b. Proof. by case: b. Qed.

Lemma oddD m n : odd (m + n) = odd m (+) odd n.
Proof.
by move: n; elim:m => [// | n IH l]; 
            rewrite  addSnnS IH 2!oddS addbN addNb.  
Qed.

Lemma odd_mul m n : odd (m * n) = odd m && odd n. 
Proof.
move: n; elim: m => [ // |n  IH m].
by rewrite mulSn oddD IH oddS; case: (odd n); case (odd m)=> // . 
Qed. 

Lemma leq_pmull m n : n > 0 -> m <= n * m. 
Proof. 
by case: n => [// | n IH ]; rewrite mulSn;  apply: leq_addr.
Qed.

Lemma odd_gt0 n : odd n -> n > 0. 
Proof.
by case : n.
Qed.


Lemma dvd0nF: forall n, 0 %| n == ( n == 0).
Proof.
move => n. by rewrite dvd0n. 
Qed.

 Lemma dvdn_mul d1 d2 m1 m2 : d1 %| m1 -> d2 %| m2 
                                       -> d1 * d2 %| m1 * m2. 
 Proof.
 (* Need to eliminate corner cases with 0 divisors *)
 elim: (PosNatDec d1) => [Hd1| ]. 
  { rewrite Hd1 mul0n => H' H''; rewrite (eqP  (dvd0nF (m1*m2))).   
    move: H';  rewrite (eqP  (dvd0nF m1)) => Hz; by rewrite (eqP Hz).
  }
 move => HPosd1. 
 elim: (PosNatDec d2) => [Hd2| ]. 
  { rewrite Hd2 muln0 => H' H''; rewrite (eqP  (dvd0nF (m1*m2))).   
    move: H''; rewrite (eqP  (dvd0nF m2)) => Hz; by rewrite (eqP Hz) muln0.
  }
 move => HPosd2. 

(* Here comes the useful part *)
 rewrite (dvdn_eq d1 m1) (dvdn_eq d2 m2); move => H1 H2.
 rewrite -(eqP H1)  -(eqP H2).
 rewrite mulnA dvdn_pmul2r. rewrite [_%/_ *_]mulnC. 
 by apply: dvdn_mulr; apply: dvdn_mulr .
 by [].
Qed.

Lemma dvdn_addr m d n : d %| m -> (d %| m + n) = (d %| n).
Proof.
elim: (PosNatDec d) => [Hd| ]. 
  {rewrite Hd (eqP  (dvd0nF m)) => Hm.
   by rewrite (eqP Hm) add0n.  
  }
move => H'. rewrite /dvdn => H''. by rewrite -modnDml (eqP H'') add0n.
Qed.


Lemma dvdn_fact m n : 0 < m <= n -> m %| n `!. 
Proof.
move:m.
elim: n => [ m H| n IH m H']. {
    exfalso. 
   elim: (andP H) => H1 H2 //=.
   have Hcontra:=(ltn_leq_trans H1 H2).
   by [].
}
rewrite factS.
have Hcase:=  leq_eqVlt m (n.+1).
elim: (andP H') => H0 HNZ; move: Hcase; rewrite HNZ => // H1.
have H1':= Bool.Is_true_eq_true _ (Bool.Is_true_eq_right _ H1).
case: (orP H1') => Hc; first by rewrite (eqP Hc); apply: dvdn_mulr => //.
have Hbound: 0 <m <= n; first by apply/andP.
apply: (dvdn_mull _ ((IH m) Hbound)).
Qed.

Lemma prime_gt0 p : prime p -> 0 < p.
Proof.
elim: (PosNatDec p) => [H | H H' ]; [rewrite H | ]=>//. 
Qed.

Lemma gtnNdvd n d : 0 < n -> n < d -> (d %| n) = false. 
Proof.
elim: (PosNatDec d) => [Hd| Hd Hn H]; first by rewrite Hd => Hcontra H //=.
by apply/eqP ; rewrite modn_small => [|//];  move => Hneg; rewrite Hneg in Hn.
Qed.


Lemma prime_gt1 p : prime p -> 1 < p.
Proof.
move =>H.
have Hyp: forall p, p <= 1 -> ~~ prime p; first by move => q Hp;
                                          case : (lt2_0_1 Hp) => Hr; rewrite Hr.

case: (EqNat.eq_nat_decide p 1) => Hc.  
   {have Hc':= EqNat.eq_nat_eq _ _ Hc.
    have Hc'': p<= 1; first by rewrite Hc'.
    have Hcontra:= Hyp _  Hc''; by exfalso; apply: (negP Hcontra) H .
   }
   { case:(orP (lt_or_geq p 2)) => HC.
     have Hcontra:= Hyp _ HC; first by exfalso; apply: (negP Hcontra) H . 
     by [].
   }
Qed.


 (* Induction on sequences, this is an induction principle adapted to r-consing! *)
Lemma last_ind A (P : list A -> Prop): 
        P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s .
Proof.
 move => Hnil Hlast s; rewrite -(cat0s s).
 (* The clever part is in cooking the induction hypothesis *)
 elim: s [::] Hnil  => [|x s2 IHs] s1 Hs1; first by rewrite cats0.  
 by rewrite -cat_rcons; apply/IHs/Hlast.
Qed.

Fixpoint foldl T R (f : R -> T -> R) z s := 
   if s is x :: s' then foldl f (f z x) s' else z. 
(* foldl is defined
   foldl is recursively defined (guarded on 5th argument *)

(* surprisingly the straightforward induction principle works !*)
Lemma cats1 T s (z : T) : s ++ [:: z] = rcons s z.
Proof.
by elim: s => //=  a l  -> .
Qed.

(* surprisingly simple, Induction Hyp does not not require parms and compute does
   most of the rest. *)
Lemma foldr_cat T R f (z0 : R) (s1 s2 : seq T) : 
   foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
Proof.
  elim s1 => [// |  a l IH] //= ; by rewrite IH =>//.  
Qed.

(* From seq.v !!!*)
Lemma rev_rcons T s (x : T) : rev (rcons s x) = x :: rev s.
Proof.
 rewrite -cats1 rev_cat =>//=.  
Qed.

  