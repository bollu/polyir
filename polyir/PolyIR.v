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

Local Notation "a # b" := (ZMap.get b a) (at level 1).

(** We will follow the development from this paper:
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf*)


Open Scope list_scope.
Import ListNotations.

Module PolyIR.
  Import NatMap.

Inductive BinopType :=
| Add : BinopType
| Sub: BinopType.
            


(* Value that expressions can take *)
Notation Value := Z.
    

(* Identifiers *)
Definition Ident := Z.

(** Syntax of PolyIR **)
Definition Indvar := Z.
Inductive AffineExpr :=
| Aindvar:  Indvar -> AffineExpr
| Abinop: BinopType -> AffineExpr -> AffineExpr -> AffineExpr
| Amul: Z -> AffineExpr -> AffineExpr
| Aconst: Z -> AffineExpr
.
Inductive PolyExpr :=
| Eaffine: AffineExpr -> PolyExpr
| Eload: Ident
         -> PolyExpr (* Load Ix *)
         -> PolyExpr
.
         
    
Inductive PolyStmt :=
| Sstore: Ident
          -> PolyExpr (* Ix *)
          -> PolyExpr (* Store val *)
          -> PolyStmt
| Sseq: PolyStmt
        -> PolyStmt
        -> PolyStmt
| Sskip: PolyStmt
| Sloop: Indvar  (* Current loop induction variable index *)
         -> PolyExpr (* expression for upper bound *)
         -> PolyStmt (* loop body *)
         -> PolyStmt
.


                  

(* Memory chunk *)
Notation ChunkNum := Z.
Notation MemoryChunk := (ZMap.t (option Value)).
(* Memory is a map indexed by naturals to disjoint memory chunks *)
Notation Memory := (ZMap.t (option MemoryChunk)).


Check (PMap.set).
Definition setMemory (chunknum: Z)
           (chunkix: Z)
           (val: Value)
           (mem: Memory) : Memory :=
  let memchunk := mem # chunknum in
  let memchunk' := option_map (fun chk => ZMap.set chunkix (Some val) chk)
                              memchunk
  in ZMap.set chunknum memchunk' mem.

  

Definition option_bind
  {A B: Type}
    (oa: option A)
    (f: A -> option B) : option B :=
      match oa with
      | None => None
      | Some a => f a
      end.

Infix ">>=" := option_bind (at level 100).
                            
                            
  
Definition getMemory (chunknum: Z)
           (chunkix: Z)
           (mem: Memory) : option Value :=
  (mem # chunknum) >>= (fun chk => chk # chunkix).
  
                                                                                         
Definition liftoption3 {a b c d: Type} (f: a -> b -> c -> d)
           (oa: option a) (ob: option b) (oc: option c): option d :=
  oa >>= (fun a => ob >>= (fun b => oc >>= (fun c => Some (f a b c)))).


Record PolyLoop :=
  mkPolyLoop {
      loopLowerBound: PolyExpr;
      loopUpperBound: PolyExpr;
      loopBody: PolyStmt;
    }.

(* Mapping from indexing expressions to environments *)
Record PolyEnvironment :=
  mkPolyEnvironment {
      polyenvIndvarToValue: ZMap.t (option Value);
      polyenvIdentToChunkNum: ZMap.t (option ChunkNum);
      polyenvLoopDepth: Z;
    }.

(** Get the induction variable of the "current" loop **)
Definition evalLoopIndvar (env: PolyEnvironment)
           (indvar: Indvar): option Value :=
  (polyenvIndvarToValue env) # indvar.

(** Increase the induction variable by 1 **)
Definition bumpLoopIndvar (env: PolyEnvironment)
           (indvar: Indvar) : PolyEnvironment :=
  let ivToValue : ZMap.t (option Value) := polyenvIndvarToValue env in
  let option_oldiv := ivToValue # indvar in
  match option_oldiv with
  | None => env
  | Some oldiv => let newIvToValue := ZMap.set indvar (Some (1 + oldiv)%Z) ivToValue in
                 {|
                   polyenvIndvarToValue := newIvToValue; 
                   polyenvIdentToChunkNum := polyenvIdentToChunkNum env;
                   polyenvLoopDepth := polyenvLoopDepth env;
                 |}
  end.



Definition addLoopToEnv (env: PolyEnvironment)
                        (indvar: Indvar): PolyEnvironment :=
  let oldLoopDepth := polyenvLoopDepth env in
  let newLoopDepth := (oldLoopDepth + 1)%Z in
  let ivToValue : ZMap.t (option Value) := polyenvIndvarToValue env in
  let newIvToValue := ZMap.set indvar (Some (0%Z)) ivToValue in
  {|
      polyenvIndvarToValue := newIvToValue; 
      polyenvIdentToChunkNum := polyenvIdentToChunkNum env;
      polyenvLoopDepth := newLoopDepth
  |}.

Definition removeLoopFromEnv (env: PolyEnvironment)
                        (indvar: Indvar): PolyEnvironment :=
  let oldLoopDepth := polyenvLoopDepth env in
  let newLoopDepth := (oldLoopDepth + 1)%Z in
  let ivToValue : ZMap.t (option Value) := polyenvIndvarToValue env in
  let newIvToValue := ZMap.set indvar (None) ivToValue in
  {|
      polyenvIndvarToValue := newIvToValue; 
      polyenvIdentToChunkNum := polyenvIdentToChunkNum env;
      polyenvLoopDepth := newLoopDepth
  |}.



Fixpoint evalAffineExprFn (env: PolyEnvironment) 
         (ae: AffineExpr) :=
  match ae with
  | Aindvar i => ((polyenvIndvarToValue env) # i)
  | Aconst c => Some c
  | _ => None
  end .

Fixpoint evalExprFn (pe: PolyExpr)
         (env: PolyEnvironment)
         (mem: Memory): option Value :=
  match pe with
  | Eaffine ae => evalAffineExprFn env ae
  | Eload id ixe => let ochunknum := (polyenvIdentToChunkNum env) # id in
                   let oix := evalExprFn ixe env mem in
                   ochunknum >>=
                             (fun chunknum => oix >>=
                                               fun ix =>
                                                 getMemory chunknum ix mem)
  end.
    

Inductive exec_stmt : PolyEnvironment -> Memory 
                      -> PolyStmt
                      -> Memory -> PolyEnvironment -> Prop:=
| exec_Sstore: forall (chunknum ix: Z)
                  (storeval: Z)
                  (storevale ixe: PolyExpr)
                  (env: PolyEnvironment)
                  (mem mem': Memory)
                  (ident: Ident),
    evalExprFn storevale env mem = Some storeval ->
    evalExprFn ixe env mem = Some ix ->
    ((polyenvIdentToChunkNum env) # ident = Some chunknum) ->
    setMemory chunknum ix storeval mem = mem' ->
    exec_stmt env mem (Sstore ident ixe storevale) mem' env
| exec_SSeq: forall (env env' env'': PolyEnvironment)
               (mem mem' mem'': Memory)
               (s1 s2: PolyStmt),
    exec_stmt env mem s1 mem' env' ->
    exec_stmt env' mem' s2 mem'' env'' ->
    exec_stmt env mem (Sseq s1 s2) mem'' env''
| exec_Sskip: forall (mem : Memory) (env: PolyEnvironment),
    exec_stmt env mem Sskip mem env
| exec_Sloop_start: forall (mem: Memory)
                      (indvar: Indvar)
                      (ube: PolyExpr)
                      (env: PolyEnvironment)
                      (inner: PolyStmt),
    evalLoopIndvar env indvar = None (* We don't have the indvar *)
    -> exec_stmt env mem (Sloop indvar ube inner) mem (addLoopToEnv env indvar)
| exec_Sloop_loop: forall (mem mem': Memory)
                    (env env': PolyEnvironment)
                    (indvar: Indvar)
                    (ube: PolyExpr)
                    (ub ivval: Value)
                    (inner: PolyStmt),
    evalExprFn ube env mem = Some ub ->
    evalLoopIndvar env indvar = Some ivval ->
    (ivval < ub)%Z ->
    exec_stmt env mem inner mem' env' ->
    exec_stmt env mem (Sloop indvar ube inner) mem' (bumpLoopIndvar env' indvar)
| exec_Sloop_end: forall (mem: Memory)
                    (env: PolyEnvironment)
                    (indvar: Indvar)
                    (ube: PolyExpr)
                    (ub ivval: Value)
                    (inner: PolyStmt),
    evalExprFn ube env mem = Some ub ->
    evalLoopIndvar env indvar = Some ivval ->
    (ivval >= ub)%Z ->
    exec_stmt env mem (Sloop indvar ube inner) mem (removeLoopFromEnv env indvar)
.
       


Lemma exec_stmt_deterministic: forall (mem mem1 mem2: Memory)
                                 (env env1 env2: PolyEnvironment)
                                 (s: PolyStmt),
    exec_stmt env mem s mem1 env1 ->
    exec_stmt env mem s mem2 env2 ->
    mem1 = mem2 /\
    env1 = env2.
Proof.
  intros until s.
  intros EXECS1.
  generalize dependent env2.
  generalize dependent mem2.
  induction EXECS1;
    intros mem2 env2 EXECS2;
    inversion EXECS2; subst; auto;
      (* Dispatch cases which require simple rewrites *)
      repeat (match goal with
            | [H1: ?X = ?Y, H2: ?X = ?Z |- _ ] =>  rewrite H1 in H2;
                                                 inversion H2;
                                                 clear H1; clear H2
              end); auto;
        (* dispatch cases that are resolved by indvar mutual exclusion *)
        try omega.


    
    - assert (S1_EQ: mem' = mem'0 /\ env' = env'0).
      apply IHEXECS1_1; auto.
      destruct S1_EQ as [MEMEQ ENVEQ].
      subst.

    - assert (EQ: mem'' = mem2 /\ env'' = env2).
      apply IHEXECS1_2. auto.

      destruct EQ as [MEMEQ ENVEQ]. subst.
      auto.

    - assert (EQ: mem' = mem2 /\ env' = env'0).
      apply IHEXECS1. auto.

      
      destruct EQ as [MEMEQ ENVEQ]. subst.
      auto.
Qed.

(* A schedule is a multi-dimensional timepoint that is a function of
its inputs *)
Notation MultidimAffineExpr := (list AffineExpr).

Fixpoint option_traverse {A: Type} (lo: list (option A)): option (list A) :=
  match lo with
  | [] => Some []
  | oa::lo' => oa >>= (fun a => option_map (cons a) (option_traverse lo'))
  end.


(* define semantics for evaluating a schedule *)
Fixpoint evalMultidimAffineExpr (env: PolyEnvironment)
         (s: MultidimAffineExpr): option (list Value) :=
  option_traverse (List.map (evalAffineExprFn env) s).


Inductive ScopStmtType :=  SSTstore | SSTload.
(** Note that for now, we don't care what is stored or loaded, because
conceptually, we don't actually care either. We just want to make sure
that the reads/writes are modeled *)
Record ScopStmt :=
 mkScopStmt {
     scopStmtArrayIdent : Ident;
     (** The induction variables this scopstmt had originally **)
     scopStmtIndvars: list Indvar;
      (** The domain of the scop statement. That is, interpreted as
          0 <= <indvars[i]> <= <domain[i]> **)
      scopStmtDomain: MultidimAffineExpr;
      (** Function from the canonical induction variables to the schedule
         timepoint. That is, interpreted as the output dimensions when
         invoked against the input **)
      scopStmtExecSchedule : MultidimAffineExpr;
      (** Access function to model where to read or write from **)
      scopStmtAccessFunction: MultidimAffineExpr;
      (** Type of the scop statement: store or load **)
      scopStmtType: ScopStmtType
   }.

Record Scop :=
  mkScop {
      (** The statements in this scop **)
      scopStmts := list ScopStmt;
      (** Induction variables in this scop **)
      indvars := list Indvar;
    }.

Fixpoint all (bs: list bool): bool :=
  List.fold_right andb true bs.

Fixpoint zipWith {X Y Z: Type} (f: X -> Y -> Z)
         (xs: list X)
         (ys: list Y) : list Z :=
  match xs  with
  | [] => []
  | x::xs' => match ys with
             | [] => []
             | y::ys' => (f x y)::zipWith f xs' ys'
             end
  end.


(* Check if the current value of the induction variables is within
the scop stmts domain *)
Definition isScopStmtActive (ss: ScopStmt) (env: PolyEnvironment): bool :=
  let oevalDom := evalMultidimAffineExpr env (scopStmtDomain ss) in
  let oevalIvs := option_traverse (List.map (evalLoopIndvar env)
                                       (scopStmtIndvars ss)) in

  if length (scopStmtDomain ss) =? length (scopStmtIndvars ss)
  then
    match oevalDom with
    | Some evalDom => match oevalIvs with
                     | Some evalIvs => all (zipWith (Z.leb) evalIvs evalDom )
                     | None => false
                     end
    | None => false
    end
  else false
  .
                                  
                                  
  






End PolyIR.


