From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra all_fingroup. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Exercises on pages 149- Chap 7.6-7.7 *)

Lemma example (T : finType) (x : T) (A : {set T}) :
   (A \subset x |: A) && (A :==: A :&: A) && (x \in [set y | y == x]).
Proof.
repeat  (apply/andP; split). 
  - by  apply subsetU1.
  - by rewrite setIid.
  - by rewrite in_set; apply /eqP.
Qed.

Lemma subsets_disjoint (T : finType) (A B : {set T}): (A \subset B) = [disjoint A & ~: B].
Proof.
rewrite subset_disjoint. (* in fintype.v*)
apply: eq_disjoint_r => x.
by rewrite !inE.
Qed.

Lemma card_powerset (T : finType) (A : {set T}) : #|powerset A| = 2 ^ #|A|.
Proof.
(* This has a not so simple proof in finset.v, using partial functions and a set of construct *)
rewrite -card_bool. (* 2 is card bool ... *)
rewrite -(card_pffun_on false). (* in finfun.v 
                                Lemma card_pffun_on y0 D R : #|pffun_on y0 D R| = #|R| ^ #|D|. *)
rewrite -(card_imset _ val_inj).
        (* Lemma pffun_onP y D R f : reflect (y.-support f \subset D /\ {subset image f D <= R})
                                            (f \in pffun_on_mem y (mem D) (mem R)).
           (uses a partial function definition) *)
apply: eq_card => f.     (* eliminates #|.| for set equality *)
pose sf := false.-support f; pose D := finset sf.

have sDA: (D \subset A) = (sf \subset A); first by apply: eq_subset; apply: in_set.
have eq_sf x : sf x = f x; first by rewrite /= negb_eqb addbF.

have valD: val D = f; first by rewrite /D unlock; apply/ffunP=> x; rewrite ffunE eq_sf.
apply/imsetP/pffun_onP=> [[B] | [sBA _]]; last by exists D; rewrite // inE ?sDA.
by rewrite inE -sDA -valD => sBA /val_inj->.
Qed.

(* Now we move on to Chap 7.7 and permutation generation or counting. *)
(* requires  mathcomp.fingroup *)

Lemma card_perm (T : finType) (A : {set T}) : #|perm_on A| = #|A|`!.
Proof.
(* Tried by copying the librarie's solution... FAILS (scope/contexte) *)
pose ffA := {ffun {x | x \in A} -> T}.
rewrite -ffactnn. 
        (*     n ^_ m == the falling (or lower) factorial of n with m terms, i.e.,    *)
        (*               the product n * (n - 1) * ... * (n - m + 1).                 *)
        (*               Note that n ^_ m = 0 if m > n, and 'C(n, m) = n ^_ m %/ m`!. *)

rewrite -{2}(card_sig [in A]) /= -card_inj_ffuns_on.

pose fT (f : ffA) := [ffun x => oapp f x (insub x)].
             (* ISSUE: had to add scope %g for 1, which is the identity, see fingroup.v
                Apparently "Open Scope group_scope" does not suffice!
              *)
pose pfT f := insubd (1%g : {perm T}) (fT f).
pose fA s : ffA := [ffun u => s (val u)].

Fail rewrite -!sum1dep_card -sum1_card (reindex_onto fA pfT) => [|f].
 (* apply: eq_bigl => p; rewrite andbC; apply/idP/and3P=> [onA | []]; first split.

rewrite -!sum1dep_card -sum1_card (reindex_onto fA pfT) => [|f].
  apply: eq_bigl => p; rewrite andbC; apply/idP/and3P=> [onA | []]; first split.


  - apply/eqP; suffices fTAp: fT (fA p) = pval p.
      by apply/permP=> x; rewrite -!pvalE insubdK fTAp //; apply: (valP p).
    apply/ffunP=> x; rewrite ffunE pvalE.
    by case: insubP => [u _ <- | /out_perm->] //=; rewrite ffunE.
  - by apply/forallP=> [[x Ax]]; rewrite ffunE /= perm_closed.
  - by apply/injectiveP=> u v; rewrite !ffunE => /perm_inj; apply: val_inj.
  move/eqP=> <- _ _; apply/subsetP=> x; rewrite !inE -pvalE val_insubd fun_if.
  by rewrite if_arg ffunE; case: insubP; rewrite // pvalE perm1 if_same eqxx.
case/andP=> /forallP-onA /injectiveP-f_inj.
apply/ffunP=> u; rewrite ffunE -pvalE insubdK; first by rewrite ffunE valK.
apply/injectiveP=> {u} x y; rewrite !ffunE.
case: insubP => [u _ <-|]; case: insubP => [v _ <-|] //=; first by move/f_inj->.
  by move=> Ay' def_y; rewrite -def_y [_ \in A]onA in Ay'.
by move=> Ax' def_x; rewrite def_x [_ \in A]onA in Ax'.
*)
Abort.

(* Look at Matrix ... for Chap 7.8*)

(* Trace of product and commuted product *)
Section ComMatrix.
(* Lemmas for matrices with coefficients in a commutative ring *)
Variable R : comPzSemiRingType.


Open Scope ring_scope.
Lemma mxtrace_mulC m n (A : 'M[R]_(m, n))  (B : 'M[R]_(n, m)) : \tr (A *m B) = \tr (B *m A).
Proof.
    have expand_trM C D: \tr (C *m D) = \sum_i \sum_j C i j * D j i;
        first by apply: eq_bigr => i _; rewrite mxE.
    rewrite !{}expand_trM exchange_big /=.

    (* need to apply twice to get to scalar multiplication, lifting summations *)
    do 2!apply: eq_bigr => ? _ ; apply: GRing.mulrC.
Qed.
Close Scope ring_scope.
End ComMatrix.

Section SizeCast.
  Variable R : comPzSemiRingType.
  Variables (n n1 n2 n3 m m1 m2 m3 : nat).
  Fail Lemma row_mxA (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)) :
                  row_mx A1 (row_mx A2 A3) = row_mx (row_mx A1 A2) A3.
  (* (cannot unify "n1 + n2 + n3" and "n1 + (n2 + n3)") *)                


  Lemma row_mxA (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)) :
  let cast := (erefl m, esym (addnA n1 n2 n3)) in
         row_mx A1 (row_mx A2 A3) = @castmx R _ _ _ _ cast (row_mx (row_mx A1 A2) A3).
  Proof.
  by move => Hc; rewrite row_mxA /Hc. 
  Qed.

  Lemma castmxKV (eq_m : m1 = m2) (eq_n : n1 = n2) :
  cancel (@castmx R _ _ _ _ (esym eq_m, esym eq_n)) (@castmx R _ _ _ _ (eq_m, eq_n)).
  Proof.  by case: m2 / eq_m; case: n2 / eq_n.  
             (* this would also work: by case: _/eq_m; case: _/eq_n. *)
  Qed.

  Lemma castmx_id l k erefl_lk (A : 'M_(l, k)) : @castmx R _ _ _ _ erefl_lk A = A.
  Proof.
     by case: erefl_lk => Heql Heqk;  rewrite [Heql]eq_axiomK [Heqk]eq_axiomK.
  Qed.

  Definition conform_mx (B : 'M_(m1, n1)) (A : 'M_(m, n)) :=
  match m =P m1, n =P n1 with
  | ReflectT eq_m, ReflectT eq_n => @castmx R _ _ _ _ (eq_m, eq_n) A
  | _, _ => B
  end.
  End SizeCast.


  Section SizeCast_1.
  Variable R : comPzSemiRingType.
  Variables (n m m1 n1 m2 n2 m3 n3 : nat).

  Lemma conform_mx_id (B A : 'M_(m, n)) : @conform_mx R _ _ _ _ B A = A.
  Proof.
    rewrite /conform_mx; first elim: eqP => Heq; first elim: eqP => Heq'; 
      first apply: castmx_id =>//=;  by [].
  Qed.

  Lemma nonconform_mx (B : 'M_(m1, n1)) (A : 'M_(m, n)) :
  (m != m1) || (n != n1) -> @conform_mx R _ _ _ _ B A = B.
  Proof.
  move/orP => [Hineq | Hineq ] ; rewrite /conform_mx;
    first elim: eqP => Heq //=; first elim: eqP => Heq' =>//=. 
  by rewrite Heq in Hineq; exfalso; by apply: (negP Hineq). 
  by case :eqP => H //=; case : eqP => H' //=; exfalso; rewrite H' in Hineq;
     apply : (negP Hineq).
  Qed.
  
  (* The wrong/hard way *)
  Lemma conform_castmx' (e_mn : (m2 = m3) * (n2 = n3))
                       (B : 'M_(m1, n1)) (A : 'M_(m2, n2)) :
  conform_mx B (castmx e_mn A) = @conform_mx R _ _ _ _ B A.
  Proof.
  elim e_mn => {e_mn} H1 H2.
  rewrite/conform_mx;  elim: eqP => Heq. elim: eqP => Heq1 =>//=;  
       elim: eqP => Heq2 =>//=.
       elim: eqP => Heq3 =>//=. 
       {
       rewrite castmx_comp.
       have Ht1: etrans H1 Heq = Heq2; first by apply nat_irrelevance.
       rewrite Ht1.
       have Ht2: etrans H2 Heq1 = Heq3; first by apply nat_irrelevance.
       by rewrite Ht2.
       }
       by rewrite (etrans H2 Heq1) in Heq3.
       by rewrite (etrans H1 Heq) in Heq2.
       elim: eqP => H.
       by rewrite (etrans (esym H) H2) in Heq1.
       by [].
       elim:  eqP => H.
      by rewrite (etrans (esym H1) H) in Heq.
      by [].
  Qed.

  (* The librarie's solution*)
  Lemma conform_castmx (e_mn : (m2 = m3) * (n2 = n3))
                       (B : 'M_(m1, n1)) (A : 'M_(m2, n2)) :
                   conform_mx B (castmx e_mn A) = @conform_mx R _ _ _ _ B A.
  Proof.     
     by do [case: e_mn; case: m3 /; case: n3 /] in A *.
  Qed.

End  SizeCast_1.