From mathcomp Require Import all_ssreflect.

Require Import libSsr.LibNat.
Require Import libSsr.LibLogic.
Set Implicit Arguments.

(* Idea: try to do these without cheating, these are all in ssreflect's
   library.
*)

Section Check_Reflect.

Inductive reflect1 (P : Prop) (b : bool) : Prop :=
| ReflectT1 (p : P) (e : b = true)
| ReflectF1 (np : ~ P) (e : b = false).


Lemma reflect_equiv (P: Prop) (b:bool): 
   reflect1 P b <-> (P <-> b).
Proof.
split; move => Rstmt; [split| case: Rstmt => HP Hb];
 first by move : Rstmt; case b => Hr HP; case Hr.
 move : Rstmt; case b => Hr HP; case Hr => // .
 elim E: b.
 { apply  ReflectT1. 
  by move: Hb HP; rewrite E => H1 H2; apply: H1 => // .
  by [].
 }
 { apply  ReflectF1.
  move => Hcontra. have:= (HP Hcontra); rewrite E =>//.
  by [].
 }
Qed.

Lemma reflect_EM b P : reflect1 P b -> P \/ ~ P.
Proof. case => H; by  [left|right]. 
Qed.

End Check_Reflect.

Section More_reflect_lemmas.

Lemma andP1 (b1 b2 : bool) : reflect (b1 /\ b2) (b1 && b2).
Proof. by case: b1; case: b2; [ left | right => //= [[l r]] ..]. Qed.

Lemma orP1 (b1 b2 : bool) : reflect (b1 \/ b2) (b1 || b2).
Proof.
  case: b1; case: b2; [ left; by [ move | left | right ] .. |].
  by right=> // [[l|r]].
Qed.

Lemma implyP1 (b1 b2 : bool) : reflect (b1 -> b2) (b1 ==> b2).
Proof.
  by case: b1; case: b2; [ left | right | left ..] => //= /(_ isT).
Qed.

End More_reflect_lemmas.

Section Reflections_1.

Lemma eqnP1 (n m : nat) : reflect (n = m) (eqn n m).
Proof.
apply: (iffP idP) => [|<-]; last by elim n. 
(* double induction !! *)
 by elim: n m => [ | n IH]  [|m] //= /IH ->.
   (* This is not equivalent to [ | n IH m] 
                         nor to  [ | n IH  [|m]] !!  *)
   (* NOTE: The effect of /IH can be replaced by::
            move=>z; have Z:=IH _ z; rewrite Z. *)
Qed.

Lemma idP1 {b : bool} : reflect b b. 
Proof.
   by elim Eb: b =>//=; constructor.
Qed.

Lemma eqnP2'1 {n m : nat} : reflect (n = m) (eqn n m).
Proof.
   apply: (iffP idP) => H. 
   (* Now the book says it is an easy induction *)
   elim: n m H => [ n  | n H ] //=; first by elim :n =>//=.
   move => l.  elim : l => [ | p H1 H2] //=. 
   elim Hel: (eq_dec_nat (n.+1) (p.+1)). by apply/eqP => //=. by auto.
   by rewrite H => //=; elim m.
Qed.

(* The above solution is not elegant!, here comes the ssrnat technique *)
Lemma eqnP2 {n m : nat} : reflect (n = m) (eqn n m).
Proof.
   apply: (iffP idP) => [|<-]; last by elim: n. (* Should have looked at Goal 2*)  
   (* Now the book says it is an easy induction *)
   (* In first case stack mgt is rather sophistated! *)
   by elim: n m =>  [ | n H]  [ | m] //= /H ->.  
   (* here look at what /H does: it applies with the TOS as arg and 
      substitutes to TOS
    *)
   
Qed.
(* This is the file'd version *)
Lemma eqnP2'  {n m : nat} : reflect (n = m) (eqn n m).
Proof.
apply: (iffP idP) => [|<-]; last by elim n.
by elim: n m => [|n IHn] [|m] //= /IHn->.
Qed.



Lemma nat_inj_eq1 T (f : T -> nat) x y :
  injective f -> reflect (x = y) (eqn (f x) (f y)).
Proof.
  move=> f_inj.
  apply: (iffP eqnP) => [ |->] //=.
  apply:f_inj.
Qed.

End Reflections_1.


Section View_Intro_Patterns.

Lemma elimTF1 (P : Prop) (b c : bool) :
  reflect P b -> b = c -> if c then P else ~ P. 
Proof.
(* Proof from coq.ssr.ssrbool, there it is in a section with definitions *)
by move => HH <-; case HH.
Qed.

Lemma elimTF0 (P : Prop) (b  : bool) :
  reflect P b -> if b then P else ~ P. 
Proof.
by case.
Qed.

Remark eq_by_3_ineq: forall n m k, k <= n -> (n <= m) && (m <= k) -> n = k.
Proof.
  move => n m k lekn /andP [lenm lemk].
  have Hin1:= (leq_trans lemk lekn).
  have Heq1: m == n; first by rewrite eqn_leq; apply/andP. 
  rewrite (eqP Heq1) in lekn lenm lemk. 
  by apply/eqP; rewrite eqn_leq; apply/andP.
 Qed.
  
(* despite use of /eqnP on first line, does not seem simpler *)
Lemma  eq_by_3_ineq': forall n m k,k <= n -> (n <= m) && (m <= k) -> n = k.
Proof.
  move=> n m k lekn /andP[/eqnP lenm lemk].
  have lemn:= (leq_trans lemk lekn).
  have eqmn: m == n; first rewrite eqn_leq. 
  by apply/andP; split; first by []; rewrite /leq; apply /eqP.
  by rewrite (eqP eqmn) in lemk; apply/eqP; rewrite eqn_leq;
      apply/andP; split. 
Qed.


End View_Intro_Patterns.


Section Inductive_specs.

(* Obtain the strong induction principle:
*)
Inductive ubn_geq_spec m : nat -> Type := UbnGeq n of n <= m : ubn_geq_spec m n.
(* UBN stands for upper bound, and we get the strong induction principle: 
ubn_geq_spec_ind: forall (m : nat) (P : forall n : nat, ubn_geq_spec m n -> Prop), 
                  (forall (n : nat) (i : n <= m),vP n (UbnGeq m n i)) ->  
                    forall (n : nat) (u : ubn_geq_spec m n),  P n u
*)

Lemma ubnPgeq m : ubn_geq_spec m m.
Proof. by []. Qed.

Lemma test_ubnP (G : nat -> Prop) m : G m.
Proof.
  case: (ubnPgeq m).
  (* We obtain the goal: forall n : nat, n <= m -> G n *)
Abort.

End Inductive_specs.

Section Euclidean_Division.

Definition edivn_rec d :=
  fix loop m q := if m - d is m'.+1 then loop m' q.+1 else (q, m).
  (* returns the (quotient, ramainder) pair , where d is the divisor.-1 *)

Definition edivn m d := if d > 0 then edivn_rec d.-1 m 0 else (0, m).
  (* regular division extended for the case d==0 *)

(* This is more general and compute oriented than with SSR_euclid_div ! *)
Lemma edivn_recE d m q :
  (* Unroll once lemma *)
  edivn_rec d m q = if m - d is m'.+1 then edivn_rec d m' q.+1 else (q,m).
Proof. by case: m. Qed.

(* This is identical except for the 'let in' construct *)
Lemma edivnP' m d (* (ed := edivn m d) *):
  let ed:= edivn m d 
  in  ((d > 0) ==> (ed.2 < d)) && (m == ed.1 * d + ed.2).
Proof.
  set ed:=  edivn m d; simpl. (* get rid of the let ...*)
  rewrite -[m]/(0 * d + m).
  case: d => [//= | d /=] in ed *.
  rewrite -[edivn m d.+1]/(edivn_rec d m 0) in ed *.
  case: (ubnPgeq m) @ed; elim: m 0 => [|m IHm] q [/=|n] leq_nm //.
  rewrite edivn_recE subn_if_gt; case: ifP => [le_dm ed|lt_md]; last first.
    by rewrite /= ltnS ltnNge lt_md eqxx.
  rewrite -ltnS in le_dm; rewrite -(subnKC le_dm) addnA -mulSnr subSS.
  by apply: IHm q.+1 (n-d) _; apply: leq_trans (leq_subr d n) leq_nm.
Qed.

Lemma edivnP'' m d (ed := edivn m d) :
  ((d > 0) ==> (ed.2 < d)) && (m == ed.1 * d + ed.2).
Proof.
                                    (* deal with d = 0 case*)
  rewrite -[m]/(0 * d + m).
  case: d => [//= | d /=] in ed *.  (* sophisticated 'in' clause *)

  rewrite -[edivn m d.+1]/(edivn_rec d m 0) in ed *.  (* Unfold once, there is an hidden goal
                                                         Therefore editing in the goal consistently*)

  case: (ubnPgeq m) @ed.       (*Note that the case analysis on (ubnPgeq m) needs to grab also
                                      the occurrence ofm in the body of ed. To do so we push 
                                      ed on the goal stack prior the case analysis. 
                                      The @ modifier tells Small Scale Reflection to keep the
                                      body of the let-in, which would be otherwise deleted.*)
  
  elim: m 0 => [|m IHm]  q  [/=|n] leq_nm //.

  rewrite edivn_recE subn_if_gt;  case: ifP => [le_dm ed|lt_md]; last first.
                                      (* Unfold the recursive function, subn_if_gt refolds the 
                                         'match' into an 'if' *)                                        
  by rewrite /= ltnS ltnNge lt_md eqxx.  (* How did eqxx get here ?
                                            Notation eqxx := eq_refl
                                            Expands to: Notation mathcomp.ssreflect.eqtype.eqxx
                                            eq_refl : forall [T : eqType] (x : T), x == x

  *)

  rewrite -ltnS in le_dm; rewrite -(subnKC le_dm) addnA -mulSnr subSS.
  apply: (IHm q.+1 (n-d) _); apply: leq_trans (leq_subr d n) leq_nm.
Qed.


Lemma edivnP m d (ed := edivn m d) :
  ((d > 0) ==> (ed.2 < d)) && (m == ed.1 * d + ed.2).
Proof.
  rewrite -[m]/(0 * d + m).
  case: d => [//= | d /=] in ed *.
  rewrite -[edivn m d.+1]/(edivn_rec d m 0) in ed *.
  case: (ubnPgeq m) @ed; elim: m 0 => [|m IHm] q [/=|n] leq_nm //.
  rewrite edivn_recE subn_if_gt; case: ifP => [le_dm ed|lt_md]; last first.
    by rewrite /= ltnS ltnNge lt_md eqxx.
  rewrite -ltnS in le_dm; rewrite -(subnKC le_dm) addnA -mulSnr subSS.
  by apply: IHm q.+1 (n-d) _; apply: leq_trans (leq_subr d n) leq_nm.
Qed.

End Euclidean_Division.


Section Coercions.

Definition is_true b := b = true. (* is_true: bool -> Prop *)

Coercion is_true : bool >-> Sortclass. (* Prop *)

Fixpoint count (a : pred nat) (s : seq nat) :=
  if s is x :: s' then a x + count a s' else 0.

Lemma count_uniq_mem (s : seq nat) x :
  uniq s -> count (pred1 x) s = has (pred1 x) s.
Proof.
elim: s => //= y s IHs /andP[/negbTE s'y /IHs-> {IHs}].
by case:  (eqVneq y x) =>  // <-; rewrite has_pred1 s'y //. 
Qed.
(* Differs slightly from ssreflect/seq.v
    elim: s => //= y s IHs /andP[/negbTE s'y /IHs-> {IHs}].
    by rewrite in_cons; case: (eqVneq y x) => // <-; rewrite s'y.
which fails "The LHS of in_cons (_  \in _ :: _)
             does not match any subterm of the goal"
*)

Search [ is:Coercion [ head:option | headconcl:nat]].

Definition zerolist n := mkseq (fun _ => 0) n.
Coercion zerolist : nat >-> seq.
Check 2 :: true == [:: 2; 0].
Fail Check [:: 2; true ] == [:: 2; 0]. (* This does not attempt coercion*)

(* Here we do it by hand *)
Print Coercion Paths bool nat. 

Check 2::true.
Check [:: 2; 0].
Check [:: 2; nat_of_bool true ] == [:: 2; 0].

Set Printing Coercions.
Check 2::true.
Check [:: 2; 0].
Check [:: 2; nat_of_bool true ] == [:: 2; 0].
Eval simpl in  [:: 2; nat_of_bool false ] == [:: 2; 0].
Eval cbv in  [:: 2; nat_of_bool false ] == [:: 2; 0].


Eval cbn in  iota 2 5. 

End Coercions.
