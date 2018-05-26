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
Require Import Maps.



(** We will follow the development from this paper:
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf*)


Open Scope list_scope.
Import ListNotations.

Module PolyIR.
  Parameter MemoryValue : Type.

Inductive BinopType :=
| Add : BinopType
| Sub: BinopType.
            

(** Syntax of PolyIR **)
Notation IndvarIndex := nat.
Inductive PolyExpr :=
| EIndvar: IndvarIndex -> PolyExpr
| EBinop: BinopType -> PolyExpr -> PolyExpr -> PolyExpr
| EMul: Z -> PolyExpr -> PolyExpr.

Definition IdentIndex := nat.
Inductive PolyStmt :=
| SStore: IdentIndex
          -> PolyExpr (* Ix *)
          -> PolyExpr (* Store val *)
          -> PolyStmt
| Sload: IdentIndex
         -> PolyExpr (* Load Ix *)
         -> PolyStmt
| Sseq: PolyStmt
        -> PolyStmt
        -> PolyStmt
| Sskip: PolyStmt.
                  

Notation MemoryIndex := nat.
Definition MemoryChunk := MemoryIndex -> MemoryValue.
Definition Memory := NMap IdentIndex MemoryChunk.

Record PolyLoop :=
  mkPolyLoop {
      loopLowerBound: PolyExpr;
      loopUpperBound: PolyExpr;
      loopBody: PolyStmt;
    }.

Record PolyEnvironment :=
  mkPolyEnvironment {
      
    }.
Fixpoint evalExprFn (pe: PolyExpr) :=
  match pe with
    | EIndvar
  

End PolyIR.


