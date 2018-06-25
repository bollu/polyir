Require Import ZArith.
Require Import Maps.
Require Export PolyIRDefinition.
Require Export SCEV.


(* SSReflect usage *)
From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Print Module SCEV.

Import SCEV.RECURRENCE.
Print Module RECURRENCE.


Definition combineAddCR (lhs: CR) (rhs: CR): option CR := None.
Definition combineSubCR (lhs: CR) (rhs: CR): option CR := None.
Definition combineConstantMutltCR (const: Z) (lhs: CR): option CR := None.
Definition CRforConst (const: Z) : option CR := None.

Definition bindoption2 {A B C: Type}
           (f: A -> B -> option C)
           (oa: option A)
           (ob: option B): option C :=
  match oa with
  | None => None
  | Some a => match ob with
             | None => None
             | Some b => (f a b)
             end
  end.

Definition IndvarToCRMap := ZMap.t (option CR).

Check (ZMap.set).

Definition mkIndvarCR (iv: Indvar): CR. Admitted.
     (* := liftToCR (liftToBR 0). *)


Fixpoint mkCRForIndvarsFix (prevmap: IndvarToCRMap) (previndvar: CR) (s: PolyStmt) : IndvarToCRMap :=
  match s with
  | Sseq s1 s2  =>
    (* Would be nice to be able to write this as union of maps... *)
    (mkCRForIndvarsFix
       (mkCRForIndvarsFix prevmap previndvar s1)
       previndvar
       s2)
  | Sloop ivname _ loop => let cr := (mkIndvarCR ivname) in
                              mkCRForIndvarsFix (ZMap.set ivname (Some cr) prevmap) cr loop
  |  _ => prevmap
  end.

Definition zeroCR: CR. Admitted.
Definition mkCRForIndvars (s: PolyStmt) : IndvarToCRMap  :=
  mkCRForIndvarsFix (ZMap.init None) zeroCR s.

Fixpoint findSCEVForAffineExpr (s: PolyStmt) (expr: AffineExpr) (ivCRs: IndvarToCRMap): option CR :=
  match expr with
  | Aindvar iv => ZMap.get iv ivCRs
  | Abinop  binop lhs rhs => match binop with
                            | Add =>  bindoption2 combineAddCR
                                      (findSCEVForAffineExpr s lhs ivCRs)
                                      (findSCEVForAffineExpr s rhs ivCRs)
                            | Sub => bindoption2 combineSubCR
                              (findSCEVForAffineExpr s lhs ivCRs)
                              (findSCEVForAffineExpr s rhs ivCRs)
                            end
  | Amul const ae => match (findSCEVForAffineExpr s ae ivCRs) with
                    | Some cr => combineConstantMutltCR const cr
                    | None => None
                    end
  | Aconst z => CRforConst z
  end.

Definition match_env (e: Environment) (ivtocr: IndvarToCRMap): Prop.
  Admitted.

  (*
Theorem mkCRForIndvarsConsistent: forall (s: PolyStmt)
                          (ivtocr: IndvarToCRMap)
                          (MKCRFORINDVARS: ivtocr = mkCRForIndvars s)
                          (env: Environment)
                          (v: Value)
                          (id: Ident)
                          (EVALAE: evalAffineExprFn env (AIndvar id) = Some v)
                          (MATCHENV: match_env env ivtocr),
    
    v = CReval 
    *)
    
