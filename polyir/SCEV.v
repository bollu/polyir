Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** We will follow the development from this paper:
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf*)

Open Scope list_scope.
Import ListNotations.

Module LISTTHEOREMS.
  Open Scope nat_scope.

  Lemma seq_peel_begin: forall (n l: nat) (LPOS: l > 0),
      n :: seq (S n) (l - 1) = seq n l.
  Proof.
    intros.
    induction l.
    - inversion LPOS.
    - simpl.
      replace (l - 0) with l.
      reflexivity.
      omega.
  Qed.

  Lemma cons_append: forall {A: Type} (a: A) (l l': list A),
      (cons a l) ++ l' = cons a (l ++ l').
  Proof.
    intros.
    generalize dependent a.
    generalize dependent l.
    induction l'.
    - auto.
    - intros.
      replace ((a0 :: a :: l) ++ l') with (a0 :: ((a:: l) ++ l')).
      reflexivity.
      apply IHl' with (a := a0) (l := (a::l)).
  Qed.
  
  Lemma seq_peel_end: forall (n l: nat) (L_GT_0: l > 0),
      seq n l = (seq n (l - 1)) ++ [ n + l - 1].
  Proof.
    intros until l.
    generalize dependent n.
    induction l.
    - intros. omega.
    - intros.
      assert (LCASES: l = 0 \/ l > 0).
      omega.

      destruct LCASES as [LEQ0 | LGT0].
      + subst.
        simpl.
        replace (n + 1 - 1) with n; auto; omega.

      +  simpl.
         replace (l - 0) with l.
         assert (SEQ_S_N: seq (S n) l = seq (S n) (l - 1) ++ [S n + l - 1]).
         apply IHl; auto.

         rewrite SEQ_S_N.

         assert (n :: seq (S n) (l - 1) = seq n l).
         apply seq_peel_begin; auto.

         replace ( n :: seq (S n) (l - 1) ++ [S n + l - 1]) with
             ((n :: seq (S n) (l - 1)) ++ [S n + l - 1]).
         rewrite H.
         replace (S n + l) with (n + S l).
         reflexivity.
         omega.
         apply cons_append.
         omega.
  Qed.
  Close Scope nat_scope.
End LISTTHEOREMS.

(** You can build the theory of SCEV over any ring, actually *)
Module RECURRENCE.
  Import LISTTHEOREMS.
  Parameter R: Type.
  Variable (zero one : R).
  Variable (plus mult minus : R -> R-> R).
  Variable (sym : R -> R).

  Variable rt : ring_theory zero one plus mult minus sym (@eq R).
  Add Ring Rring : rt.

  Notation "0" := zero.  Notation "1" := one.
  Notation "x + y" := (plus x y).
  Notation "x * y " := (mult x y).

  (* Section LOOPVARIANT. *)

  (* A class for objects that vary over loop iterations *)
  Class LoopVariant (A R : Type) :=
    {
      evalAtIx: A -> nat -> R
    }.
  Infix "#" := evalAtIx (at level 60).

  Instance loopVariantFn (R: Type): LoopVariant (nat -> R) (R : Type) :=
    {
      evalAtIx (f: nat -> R) (n: nat) := f n
    }.

  Definition scaleLoopVariantFn  (r: R) (f: nat -> R): nat -> R :=
    fun n => r * (f n).


  

  (* Const function *)
  Definition const {A B: Type} (x: A) (y: B) := x.
  
  Definition RBinop := R -> R -> R.
  
  (** How do I ask that R is a ring? *)

  Section BR.

    Inductive BR :=
    | mkBR : R -> (R -> R -> R) -> (nat -> R) -> BR.

    (** semantics of evaluating a BR *)
    Definition evalBR (br: BR) (n: nat): R :=
      match br with
      | mkBR r0 binop f =>
        let
          vals : list R := map f (seq 1 n)
        in
        fold_left binop vals r0
      end.


    Instance loopVariantBR : LoopVariant BR R :=
      {
        evalAtIx (br: BR) (n: nat) := evalBR br n
      }.

    Class LiftToBR A : Type  :=
      {
        liftToBR : A -> BR
      }.

    Instance liftConstantToBR : LiftToBR R :=
      {
        liftToBR (c: R) := mkBR c plus (const zero)
      }.

    Instance liftBRToBR: LiftToBR BR :=
      {
        liftToBR br := br
      }.


    Lemma liftConstant_eval: forall (n: nat) (r: R),
        evalAtIx (liftToBR r)  n = r.
    Proof.
      intros.
      simpl.

      induction n.
      - auto.
      - rewrite seq_peel_end.
        rewrite map_app.
        rewrite fold_left_app.
        replace (S n - 1)%nat with n; try omega.
        rewrite IHn.
        simpl.
        unfold const; auto; ring.
        omega.
    Qed.

    Hint Resolve liftConstant_eval.
    Hint Rewrite liftConstant_eval.

    Lemma BReval_step: forall `{Ring R} (r0: R) (bop: R -> R -> R) (f: nat -> R) (n : nat),
        (mkBR r0 bop f) # (S n) = bop ((mkBR r0 bop f) # n)  (f # (S n)).
    Proof.
      Open Scope nat_scope.
      intros until n.
      generalize dependent r0.
      generalize dependent bop.
      generalize dependent f.
      simpl.
      induction n.
      - auto.
      - intros.

        assert (STRIP_LAST: seq 2 (S n) = seq 2 (S n - 1) ++ [2 + (S n) - 1]).
        apply seq_peel_end; omega.

        rewrite STRIP_LAST.
        simpl.

        rewrite map_app.
        rewrite fold_left_app.
        simpl.
        replace (n - 0) with n.
        reflexivity.
        omega.
        Close Scope nat_scope.
    Qed.



    Section BR_CONSTANTS.
      Variable f : nat -> R.
      Variable r0 c: R.

      Definition br := mkBR r0 plus f.

      (* Lemma 6 from paper *)
      Lemma add_constant_add_br: forall `{Ring R}  (n: nat),
          ((liftToBR c) # n) +
          ((mkBR r0 plus f) # n) = 
          (mkBR (r0 + c) plus f) # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite BReval_step.
          ring_simplify in IHn.
          ring_simplify.

          replace (liftToBR c # S n) with
              (liftToBR c # n).
          rewrite IHn.
          rewrite <- BReval_step.
          reflexivity.

          repeat (rewrite liftConstant_eval).
          auto.
      Qed.

      (* Lemma 7 *)
      (* Here is where I need a module :( nat -> R forms a module over R *)
      Lemma mul_constant_add_br: forall `{Ring R} (n: nat),
          ((liftToBR c) # n) * ((mkBR r0 plus f) # n) =
          (mkBR (c * r0) plus (scaleLoopVariantFn c f)) # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite BReval_step.

          replace (liftToBR c # S n) with
              (liftToBR c # n).
          ring_simplify.
          rewrite IHn.
          rewrite BReval_step.
          
          replace ((liftToBR c # n) * (f # S n)) with
              ((scaleLoopVariantFn c f) # S n).
          reflexivity.

          rewrite liftConstant_eval.
          auto.

          repeat (rewrite liftConstant_eval).
          reflexivity.
      Qed.
      
      Check (pow_N).
      (*
    (* Lemma 8 *)
    Lemma pow_constant_add_br: forall `{Ring R} (n: nat),
        pow_N c ((mkBR r0 plus f) # n) =
        (mkBR (pow_N c r0) mult (fun n => pow_N c (f # n))) # n.
       *)

      Lemma mul_constant_mul_br: forall `{Ring R} (n:  nat),
          c * ((mkBR r0 mult f ) # n) =
          ((mkBR (r0 * c) mult f) # n).
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite BReval_step.
          rewrite BReval_step.
          ring_simplify.
          rewrite IHn.
          ring.
      Qed.
    End BR_CONSTANTS.

    Section BR_BR.
      Variable c1 c2: R.
      Variable f1 f2: nat -> R.
      Let br1_add := mkBR c1 plus f1.
      Let br1_mul := mkBR c1 mult f1.

      Let br2_add := mkBR c2 plus f2.
      Let br2_mul := mkBR c2 mult f2.


      (* Lemma 12 *)
      Definition add_add_br_add_br: forall `{Ring R} (n: nat),
          (br1_add # n) + (br2_add # n) = (mkBR (c1 + c2) plus
                                                (fun n => f1 n + f2 n)) # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - unfold br1_add in *.
          unfold br2_add in *.
          rewrite BReval_step.
          rewrite BReval_step.
          rewrite BReval_step.
          ring_simplify.
          replace ((mkBR c1 plus f1 # n) +
                   (f1 # S n) +
                   (mkBR c2 plus f2 # n) +
                   (f2 # S n)) with
              ((mkBR c1 plus f1 # n) +
               (mkBR c2 plus f2 # n) +
               (f1 # S n) +
               (f2 # S n)); try ring.
          rewrite IHn.
          simpl.
          ring.
      Qed.

      
      (* Lemma 13 *)
      (* Definition in paper is WRONG. They index both br1, br2 and the
    functions with the _same index_. It should be one minus *)
      Definition mulCRFn (n: nat): R:=  ((br1_add # (n - 1)) * (f2 # n) +
                                       (br2_add # (n - 1)) * (f1 # n) +
                                       (f1 # n) * (f2 # n)).

      Lemma mul_add_br_add_br: forall `{Ring R} (n: nat),
          (br1_add # n) * (br2_add # n) = ((mkBR (c1 * c2) plus (mulCRFn)) # n).
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - unfold br1_add, br2_add in *.
          rewrite BReval_step.
          rewrite BReval_step.

          ring_simplify.
          rewrite IHn.
          Opaque evalBR.
          simpl.
          ring_simplify.

          remember (evalBR (mkBR c1 plus f1) n * f2 (S n)) as BR1F2.
          remember ( f1 (S n) * evalBR (mkBR c2 plus f2) n) as BR2F1.
          remember (f2 (S n) * f1 (S n)) as F1F2.
          replace (evalBR (mkBR (c1 * c2) plus mulCRFn) n + BR1F2 + F1F2 + BR2F1)
            with (evalBR (mkBR (c1 * c2) plus mulCRFn) n + (mulCRFn (S n))).

          rewrite BReval_step.
          simpl.
          auto.

          ring_simplify.
          
          cut (mulCRFn (S n) = BR1F2 + F1F2 + BR2F1).
          intros EQ. rewrite EQ. ring.

          
          unfold mulCRFn.

          rewrite HeqBR1F2.
          rewrite HeqBR2F1.
          rewrite HeqF1F2.
          simpl.
          unfold br1_add.
          unfold br2_add.
          simpl.
          replace (n - 0)%nat with n.
          ring.
          omega.
          Transparent evalBR.
      Qed.

      
      (* Lemma 14 *)
      Lemma mul_mul_br_mul_br: forall `{Ring R} (n: nat),
          (br1_mul # n) * (br2_mul # n) =
          ((mkBR (c1 * c2) mult (fun n => (f1 n * f2 n))) # n).
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - unfold br1_mul, br2_mul in *.
          rewrite BReval_step.
          rewrite BReval_step.
          ring_simplify.
          replace ((mkBR c1 mult f1 # n) * (f1 # S n) *
                   (mkBR c2 mult f2 # n) * (f2 # S n)) with
              ((mkBR c1 mult f1 # n) * (mkBR c2 mult f2 # n) *
               (f1 # S n) * (f2 # S n)); try ring.
          rewrite IHn.
          rewrite BReval_step.
          Opaque evalBR.
          simpl.
          ring.
          Transparent evalBR.
      Qed.
      


    End BR_BR.

    
  End BR.

  
  (* I need to do this outside to declare BR over Nats
 Section BR_NatBR.
    Variable c1:R.
    Variable c2: nat.
                  
    Variable f1: nat -> R.
    Variable f2: nat -> nat.

    Let br1_add := mkBR c1 plus f1.
    Let br2_add := mkBR c2 Nat.add f2.


      (* Lemma 15 *)
      Lemma pow_mul_br_mul_br: forall `{Ring R} (n: nat) ,
          pow_R (br1_mul # n)
    End BR_NatBR.
   *)
  


  Section CR.
    Inductive CR :=
    | liftBRToCR: BR -> CR
    | recurCR: R -> (R -> R -> R) -> CR -> CR
    .
    

    
    Class LiftToCR A : Type  :=
      {
        liftToCR : A -> CR
      }.


    Instance liftToBR_to_liftToCR `{A: Type} `{LiftToBR A} : LiftToCR A :=
      {
        liftToCR (prebr: A) :=   liftBRToCR (liftToBR prebr)
                               
      }.

    (* Interpret a CR as nested BRs as described in section 2 -
       Chains of Recurrences *)
    Fixpoint CR_to_BR (cr: CR): BR :=
      match cr with
      | liftBRToCR br =>  br
      | recurCR r0 bop cr' => mkBR r0 bop (evalBR (CR_to_BR cr'))
      end.

    Instance liftCRToBR : LiftToBR CR :=
      {
        liftToBR := CR_to_BR
      }.
      


    (* Define what it means to evaluate a CR *)
    Fixpoint CReval (cr: CR) (n: nat) := evalBR (liftToBR cr) n.

    Instance LoopVariantCr : LoopVariant CR R :=
      {
        evalAtIx (cr: CR) (n: nat) := CReval cr n                                          
      }.
      

    Inductive PureCR (bop: R -> R -> R): CR -> Prop :=
    | PureBR : forall (c0: R) (fn: nat -> R),
        PureCR bop (liftBRToCR (mkBR c0 bop fn))
    |  PureCRRec: forall (c0: R) (cr: CR),
        PureCR bop cr ->
        PureCR bop (recurCR c0 bop cr)
    .

    (* Define pure-sum and pure-product CRs *)
    Definition PureSumCR := PureCR plus.
    Definition PureProdSR := PureCR mult.


    (* Lemma 16 *)
    Lemma add_const_to_CR:  forall (r c0: R) (cr: CR) (n: nat),
        r + ((recurCR c0 plus cr) # n) =
        ((recurCR (c0 + r) plus cr) # n).
    Proof.
      intros.
      simpl.
      induction n.
      - simpl. ring.
      - rewrite seq_peel_end; try omega.
        replace (1 + S n - 1)%nat with (S n); try omega.
        replace (S n - 1)%nat with n; try omega.
        repeat (rewrite map_app).
        repeat (rewrite fold_left_app).
        rewrite <- IHn.
        simpl.
        ring.
    Qed.

    (* Lemma 17 *)
    Lemma mul_const_to_CR:  forall (r c0: R) (cr: CR) (n: nat),
        r * ((recurCR c0 mult cr) # n) =
        ((recurCR (c0 * r) mult cr) # n).
    Proof.
      intros.
      simpl.
      induction n.
      - simpl. ring.
      - rewrite seq_peel_end; try omega.
        replace (1 + S n - 1)%nat with (S n); try omega.
        replace (S n - 1)%nat with n; try omega.
        repeat (rewrite map_app).
        repeat (rewrite fold_left_app).
        rewrite <- IHn.
        simpl.
        ring.
    Qed.

    Fixpoint rewrite_PureSumCr_on_mul_const (cr: CR) (c: R): CR :=
      match cr with
      | liftBRToCR br => match br with
                        | mkBR c0 _ f => (liftBRToCR (mkBR (c0 + c) plus f))
                        end
      | recurCR c0 _ cr' =>
        recurCR (c0 + c) plus (rewrite_PureSumCr_on_mul_const cr' c)
      end.

    (*  Lemma 18 *)
    Lemma mul_const_to_pure_sum: forall (c: R) (cr: CR) (n: nat),
        PureSumCR cr ->
        c * (cr # n) = (rewrite_PureSumCr_on_mul_const cr c) # n.
    Proof.
      intros until cr.
      generalize dependent c.
      induction cr.
      - intros.
        inversion H; subst.
        Opaque evalBR.
        simpl.
        (* 
        replace c with (evalBR (liftToBR c)  n).
        rewrite mul_b
         *)
    Admitted.
        
      
      

    
    
  End CR.
  

  
End RECURRENCE.

