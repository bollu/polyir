Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
Require Import Maps.
(** Import VPL for polyhedral goodness **)
From Vpl Require Import PedraQ DomainInterfaces.
Require Import VplTactic.Tactic.
Add Field Qcfield: Qcft (decidable Qc_eq_bool_correct, constants [vpl_cte]).

Import PedraQ.FullDom.


(* Equalities stuff *)
Require Import EquivDec.
Require Import Equalities.

Locate "=?".

(** Cool, VPLTactic works **)
Example demo1 (A:Type) (f: Qc -> A) (v1: Qc):
  v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1.
Proof.
  vpl_auto.
Qed.


(* 
From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
 *)

Local Notation "a ## b" := (ZMap.get b a) (at level 1).

(** We will follow the development from this paper:
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf*)


Open Scope list_scope.
Import ListNotations.

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




(** Memory chunk: allows multidimensional reads and writes **)
Notation ChunkNum := Z.
Record MemoryChunk :=
  mkMemoryChunk {
      memoryChunkDim: nat;
      memoryChunkModel: list Z -> option Value
    }.

Definition const {A B : Type} (a: A) (_: B) : A := a.

Definition initMemoryChunk (n: nat): MemoryChunk :=
  mkMemoryChunk n (const None).

(* Need this to perform == on list of Z *)
Program Instance Z_eq_eqdec : EqDec Z eq := Z.eq_dec.

(** Only allows legal stores, so the length of six "store index"
must be equal to the dimension of the memory chunk *)
Definition storeMemoryChunk (six: list Z)
           (v: Value) (mc: MemoryChunk): MemoryChunk :=
  let dim := memoryChunkDim mc in
  {| memoryChunkDim := dim;
     memoryChunkModel := if  Nat.eqb (List.length six)  dim
                         then (fun ix => if ix  == six
                                      then Some v
                                      else (memoryChunkModel mc) ix)
                         else memoryChunkModel mc
                                               
                                               
  |}.

Definition loadMemoryChunk (lix: list Z)(mc: MemoryChunk): option Value :=
  if Nat.eqb (List.length lix) (memoryChunkDim mc)
  then (memoryChunkModel mc lix)
  else None.

(* Memory is a map indexed by naturals to disjoint memory chunks *)
Notation Memory := (ZMap.t (option MemoryChunk)).


Check (PMap.set).
Definition storeMemory (chunknum: Z)
           (chunkix: list Z)
           (val: Value)
           (mem: Memory) : Memory :=
  let memchunk := mem ## chunknum in
  let memchunk' := option_map (fun chk => storeMemoryChunk chunkix val chk )
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



Definition loadMemory (chunknum: Z)
           (chunkix: list Z)
           (mem: Memory) : option Value :=
  (mem ## chunknum) >>= (fun chk => loadMemoryChunk chunkix chk).


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
(* Called environment because it is shared between poly an scop*)
Record Environment :=
  mkEnvironment {
      envIndvarToValue: ZMap.t (option Value);
      envIdentToChunkNum: ZMap.t (option ChunkNum);
      envLoopDepth: Z;
    }.

(** Get the induction variable of the "current" loop **)
Definition evalLoopIndvar (env: Environment)
           (indvar: Indvar): option Value :=
  (envIndvarToValue env) ## indvar.

(** Increase the induction variable by 1 **)
Definition bumpLoopIndvar (env: Environment)
           (indvar: Indvar) : Environment :=
  let ivToValue : ZMap.t (option Value) := envIndvarToValue env in
  let option_oldiv := ivToValue ## indvar in
  match option_oldiv with
  | None => env
  | Some oldiv => let newIvToValue := ZMap.set indvar (Some (1 + oldiv)%Z) ivToValue in
                  {|
                    envIndvarToValue := newIvToValue; 
                    envIdentToChunkNum := envIdentToChunkNum env;
                    envLoopDepth := envLoopDepth env;
                  |}
  end.



Definition addLoopToEnv (env: Environment)
           (indvar: Indvar): Environment :=
  let oldLoopDepth := envLoopDepth env in
  let newLoopDepth := (oldLoopDepth + 1)%Z in
  let ivToValue : ZMap.t (option Value) := envIndvarToValue env in
  let newIvToValue := ZMap.set indvar (Some (0%Z)) ivToValue in
  {|
    envIndvarToValue := newIvToValue; 
    envIdentToChunkNum := envIdentToChunkNum env;
    envLoopDepth := newLoopDepth
  |}.

Definition removeLoopFromEnv (env: Environment)
           (indvar: Indvar): Environment :=
  let oldLoopDepth := envLoopDepth env in
  let newLoopDepth := (oldLoopDepth + 1)%Z in
  let ivToValue : ZMap.t (option Value) := envIndvarToValue env in
  let newIvToValue := ZMap.set indvar (None) ivToValue in
  {|
    envIndvarToValue := newIvToValue; 
    envIdentToChunkNum := envIdentToChunkNum env;
    envLoopDepth := newLoopDepth
  |}.



Fixpoint evalAffineExprFn (env: Environment) 
         (ae: AffineExpr) : option Value :=
  match ae with
  | Aindvar i => ((envIndvarToValue env) ## i)
  | Aconst c => Some c
  | _ => None
  end .

Fixpoint evalExprFn (pe: PolyExpr)
         (env: Environment)
         (mem: Memory): option Value :=
  match pe with
  | Eaffine ae => evalAffineExprFn env ae
  | Eload id ixe => let ochunknum := (envIdentToChunkNum env) ## id in
                    let oix := evalExprFn ixe env mem in
                    ochunknum >>=
                              (fun chunknum => oix >>=
                                                   fun ix =>
                                                     loadMemory chunknum [ix] mem)
  end.


Inductive exec_stmt : Environment -> Memory 
                      -> PolyStmt
                      -> Memory -> Environment -> Prop:=
| exec_Sstore: forall (chunknum ix: Z)
                      (storeval: Z)
                      (storevale ixe: PolyExpr)
                      (env: Environment)
                      (mem mem': Memory)
                      (ident: Ident),
    evalExprFn storevale env mem = Some storeval ->
    evalExprFn ixe env mem = Some ix ->
    ((envIdentToChunkNum env) ## ident = Some chunknum) ->
    storeMemory chunknum [ix] storeval mem = mem' ->
    exec_stmt env mem (Sstore ident ixe storevale) mem' env
| exec_SSeq: forall (env env' env'': Environment)
                    (mem mem' mem'': Memory)
                    (s1 s2: PolyStmt),
    exec_stmt env mem s1 mem' env' ->
    exec_stmt env' mem' s2 mem'' env'' ->
    exec_stmt env mem (Sseq s1 s2) mem'' env''
| exec_Sskip: forall (mem : Memory) (env: Environment),
    exec_stmt env mem Sskip mem env
| exec_Sloop_start: forall (mem: Memory)
                           (indvar: Indvar)
                           (ube: PolyExpr)
                           (env: Environment)
                           (inner: PolyStmt),
    evalLoopIndvar env indvar = None (* We don't have the indvar *)
    -> exec_stmt env mem (Sloop indvar ube inner) mem (addLoopToEnv env indvar)
| exec_Sloop_loop: forall (mem mem': Memory)
                          (env env': Environment)
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
                         (env: Environment)
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
                                      (env env1 env2: Environment)
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
    apply IHEXECS1_2; auto.

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

Module Type POLYHEDRAL_THEORY.
  Parameter PointT: Type.
  Parameter PolyT: Type.
  Parameter AffineFnT: Type.
  Parameter AffineRelT: Type.
  Parameter ParamsT: Type.
  (* Some way to specify a dimension *)
  Parameter DimensionT: Type.
  (* Some way to map a point with an affine function *)
  Parameter mapPoint: AffineFnT -> PointT -> option (PointT).
  (* Has some way to fill in the free variables *)
  Parameter evalPoint: ParamsT -> PointT -> option (list Z).
  (* Have some way to compose affine functions *)
  Parameter composeAffineFunction: AffineFnT -> AffineFnT -> option AffineFnT.
  (* Compute the inverse of an affine function *)
  Parameter invertAffineFunction: AffineFnT -> option AffineFnT.
  (* Have some way to check if two points are related *)
  Parameter arePointsRelated: PointT -> PointT -> AffineRelT -> bool.
  (* Check if a point is within a polyhedra *)
  Parameter isPointInPoly: PointT -> PolyT -> bool.

  (* Returns whether one point is lex smaller than the other *)
  Parameter isLexSmaller: PointT -> PointT -> option (bool).

  (* Find the next point that is within the polyhedra which is
    one larger in terms of lex order. return Nothing if not possible *)
  Parameter getNextLexLargerPoint: ParamsT ->
                                   PolyT ->
                                   PointT ->
                                   option (PointT).

  Parameter getOverapproximationNumPointsInPoly: ParamsT ->
                                                 PolyT ->
                                                 option (nat).
  (* Definition of an empty polyhedra *)
  Parameter emptyPoly: PolyT.

  (* Empty affine relation *)
  Parameter emptyAffineRel: AffineRelT.

  (* Take a union of two relations *)
  Parameter unionAffineRel:  AffineRelT -> AffineRelT -> AffineRelT.

  (* Weaken an affine function into an affine relation *)
  Parameter affineFnToAffineRel: AffineFnT -> AffineRelT.


  (* Definition of union of polyhedra *)
  Parameter unionPoly:  PolyT -> PolyT -> option PolyT.

  (** Defines what it means to be a dependence relation. This is the
        over-approximate definition. In particular, it does not ask for
        exact dependence relations .
        t1 --R1--> p 
        t2 --R2--> p
        t1 < t2
        ===============
          t1 --D--> t2
   **)
  Definition relationIsDependenceBetweenRelations
             (r1 r2: AffineRelT)
             (dep: AffineRelT): Prop :=
    forall (tp1 tp2 ixp1 ixp2: PointT)
           (TP1_MAPSTO_IXP1: arePointsRelated  tp1 ixp1 r1 = true)
           (TP2_MAPSTO_IXP2: arePointsRelated tp2 ixp2 r2 = true)
           (IXEQ: ixp1 = ixp2)
           (TP_LEX_ORDERED: isLexSmaller tp1 tp2 = Some true),
      arePointsRelated tp1 tp2 dep = true.

  (* A function to compute the dependence polyhedra of two relations *)
  Parameter getDependenceRelation: AffineRelT -> AffineRelT -> option AffineRelT.
  
  
End POLYHEDRAL_THEORY.

Module SCOP(P: POLYHEDRAL_THEORY).

  (* define semantics for evaluating a schedule *)
  (* 
    Fixpoint evalMultidimAffineExpr (env: Environment)
             (s: MultidimAffineExpr):  option (list Value) :=
      option_traverse (List.map (evalAffineExprFn env) s).
   *)


  Inductive ScopStmtType :=
  | SSTstore: (list Value -> Value) (* Value to store; this is temporary *)
              -> ScopStmtType
  | SSTload: ScopStmtType.

  Record ScopEnvironment :=
    mkScopEnvironment {
        (* VIV = virtual induction variable *)
        scopenvVIV: P.PointT;
        scopenvParams: P.ParamsT;
        scopenvIdentToChunkNum: ZMap.t (option ChunkNum);
      }.

  (** Note that for now, we don't care what is stored or loaded, because
conceptually, we don't actually care either. We just want to make sure
that the reads/writes are modeled *)
  Record ScopStmt :=
    mkScopStmt {
        (** Identifier of the scop statement *)
        scopStmtArrayIdent : Ident;
        (** The domain of the scop statement. That is, interpreted as
          0 <= <indvars[i]> <= <domain[i]> **)
        scopStmtDomain: P.PolyT;
        (** Function from the canonical induction variables to the schedule
         timepoint. That is, interpreted as the output dimensions when
         invoked against the input **)
        (** Note that the schedule dimensions can be larger than the input
      dimension **)
        scopStmtSchedule : P.AffineFnT;
        (** Access function to model where to read or write from **)
        scopStmtAccessFunction: P.AffineFnT;
        (** Type of the scop statement: store or load **)
        scopStmtType: ScopStmtType
      }.

  Record Scop :=
    mkScop {
        (** The statements in this scop **)
        scopStmts : list ScopStmt;
        (** Induction variables in this scop **)
        scopIndvars : list P.DimensionT;
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

  Definition zip {X Y : Type}
             (xs: list X)
             (ys: list Y): list (X * Y) :=
    @zipWith X Y (X * Y) (fun x y => (x, y)) xs ys.

  (* Check if the current value of the induction variables is within
the scop stmts domain *)
  Definition isScopStmtActive (se: ScopEnvironment) (ss: ScopStmt) : bool :=
    P.isPointInPoly (scopenvVIV se) (scopStmtDomain ss).

  (* Build on the abstraction of memory to store into an array *)
  Definition storeArray (arrayIdent: Ident)
             (ix: list Value)
             (val: Value)
             (se: ScopEnvironment)
             (mem: Memory) : Memory :=
    match (scopenvIdentToChunkNum se) ## arrayIdent with
    | Some chnk => storeMemory chnk ix val mem
    | None => mem
    end.
  
  

  (** TODO: make loads an actual statement in the PolyIR language **)
  Definition runScopStmt (ss: ScopStmt)
             (se: ScopEnvironment)
             (mem: Memory) : Memory :=
    (* let oaccessfn : option P.AffineFnT := P.composeAffineFunction
                                   (scopStmtAccessFunction ss)
                                   (scopStmtSchedule ss) in *)
    
    let oaccessfn : option P.AffineFnT := 
        Some (scopStmtAccessFunction ss) in

    let viv : P.PointT := scopenvVIV se in
    
    let oiv : option P.PointT := oaccessfn >>= fun f => P.mapPoint f viv in
    let oaccessix : option (list Z) :=
        oiv >>= fun iv => P.evalPoint (scopenvParams se) iv in
    match (oaccessix, scopStmtType ss)  with
    | (Some accessix, SSTstore val) => storeArray
                                         (scopStmtArrayIdent ss)
                                         accessix
                                         (val accessix)
                                         se
                                         mem
    | (Some accessix, SSTload) => mem
    | (None, _) => mem
    end.


  (* 
    (* Add a new induction varible into the environment, replacing
the previous value of the induction variable (if it existed ) *)
    Definition setIndvarInEnv (env: Environment)
               (indvar: Indvar)
               (val: Value) : Environment :=
      let ivToValue : ZMap.t (option Value) := envIndvarToValue env in
      let newIvToValue := ZMap.set indvar (Some (val%Z)) ivToValue in
      {|
        envIndvarToValue := newIvToValue; 
        envIdentToChunkNum := envIdentToChunkNum env;
        envLoopDepth := envLoopDepth env
      |}.
   *)

  (* 
    (* If the list of affine expressions are valid: that is, expression at index J only refers to variables in indeces 0 <= i < J,
then this will return a valid list of bounds. Note that usually,
 domain expressions need to be evaluated this way to find domains.
 However, objects such as general affine expressions should not be
 evaluated this way! *)
    Fixpoint getMultidimAffineExprExtent
             (env: Environment)
             (ivs: list Indvar)
             (aes: MultidimAffineExpr)
      :  list (option Value) :=
      match (ivs, aes) with
      | (_, []) =>  []
      | ([], _) => []
      | (iv::ivs', ae::aes') =>
        let oval := evalAffineExprFn env ae in
        match oval with
        | None => []
        | Some val =>
          let env' := setIndvarInEnv env iv val in
          (Some val)::(getMultidimAffineExprExtent env' ivs' aes')
        end
      end.
   *)
  
  

  (** Get the statements whose domain is contained in the current environment **)
  Definition getActiveScopStmtsInScop (s: Scop)
             (se: ScopEnvironment): list ScopStmt :=
    List.filter (isScopStmtActive se) (scopStmts s).

  (** Run a scop for a step with some given environment and memory. **)
  Definition runScopStepWithEnvAndMem (s: Scop)
             (se: ScopEnvironment)
             (mem: Memory) : Memory :=
    List.fold_left (fun m ss => runScopStmt ss se m)
                   (getActiveScopStmtsInScop s se) mem.




  (* 
    (** Numbers represented with highest position to the _right_. So, 100 would be "0 0 1"
    Essentially, the input is "flipped" from the normal human order.
   **)
    (** Find a way to signal "no more" without also erroring out**)
    Fixpoint findLexNextValue_ (vs: list Value)
             (limits: list Value): option (list Value) :=
      match (vs,limits) with
      | ([], []) => None
      | (v::vs', l::ls') => if true
                           then Some ((v+1)%Z::vs')
                           else option_map (cons 0%Z) (findLexNextValue_ vs' ls')
      | (_, _) => None
      end.
   *)
  

  (** Numbers represented with highest position to the _left_. So, 100 would be "1 0 0"
    Limits represent the "base" of that given digit. If the number exceeds the base,
    it rolls over. If a number is not possible, then it returns a None

    Definition findLexNextValue (vs: list Value) (limits: list Value): option (list Value) :=
      findLexNextValue_ (List.rev vs) (List.rev limits).

    (* Set all the given induction variables in the environment *)
    Definition setIndvarsInEnv (ebegin: Environment) (ivs: list Ident) (vs: list Value): Environment :=
      List.fold_left
        (fun e iv_v => setIndvarInEnv e (fst iv_v) (snd iv_v))
        (zip ivs vs) ebegin.
   *)

  
  Definition setVIVInScopEnv (vivs: P.PointT)
             (se: ScopEnvironment):ScopEnvironment :=
    {|
      scopenvVIV := vivs;
      scopenvParams := scopenvParams se;
      scopenvIdentToChunkNum := scopenvIdentToChunkNum se;
    |}.
  

  (* Try to bump up the induction variable values, and give up
    if it is not possible *)
  Definition bumpScopenvVIV
             (scopDomain: P.PolyT)
             (se: ScopEnvironment)
    : option ScopEnvironment :=
    option_map (fun viv' => setVIVInScopEnv viv' se)
               (P.getNextLexLargerPoint (scopenvParams se)
                                        (scopDomain)
                                        (scopenvVIV se)).
  
  (** update all the environment induction variables to their next value **)
  (** This is separate from bumpEnvindvarvalues for conceptual clarity.
Could be merged later... **)
  Definition stepScopenv
             (scopDomain: P.PolyT)
             (se: ScopEnvironment) : option ScopEnvironment
    := bumpScopenvVIV scopDomain se.


  (* Note that the fuel is OK, we can calculate how much fuel to provide
based on the domain extent *)
  Fixpoint runScop_
           (fuel: nat)
           (scopDomain: P.PolyT)
           (se: ScopEnvironment)
           (mem: Memory)
           (s: Scop)
           {struct fuel}: ScopEnvironment * Memory :=
    let mem' := runScopStepWithEnvAndMem s se mem in
    let ose' := stepScopenv scopDomain se in
    match fuel with
    | O => (se, mem)
    | S fuel' => 
      match ose' with
      | None => (se, mem)
      | Some se' => runScop_ fuel' scopDomain se' mem' s
      end
    end.
  

  (* 
    Definition maxListPointwise (l1 l2: list Value): list Value :=
      zipWith Z.max l1 l2.

    Check (fold_left).
    Definition fold_left_1 {X: Type} (f: X -> X -> X) (xs: list X): option X :=
      match xs with
      | [] => None
      | x:: xs => Some (fold_left f xs x)
      end.


    (* Get the union of the domains of all the individual scops *)
    Definition getScopDomainExtent (initenv: Environment) (s: Scop):
      option (list Value) :=
      let odoms : option (list (list Value)) :=
          option_traverse (List.map
                             (fun ss => option_traverse
                                       ((getMultidimAffineExprExtent
                                           initenv
                                           (scopStmtIndvars ss)
                                           (scopStmtDomain ss)))) (scopStmts s))
      in match odoms with
         | None => None
         | Some doms => fold_left_1 maxListPointwise doms
         end.

    Definition getNumPointsInExtent (extent: list Value): Value :=
      fold_left Z.mul extent 1%Z.
   *)

  Check (List.fold_left).
  Definition getScopDomain  (s: Scop) : option P.PolyT :=
    let domains: list (P.PolyT) := List.map scopStmtDomain (scopStmts s) in
    fold_left (fun op q => op >>= fun p => P.unionPoly p q) domains (Some P.emptyPoly) .
  
  
  Definition runScop (s: Scop)
             (se: ScopEnvironment)
             (initmem: Memory): option (ScopEnvironment * Memory) :=
    getScopDomain s >>=
                  fun dom => P.getOverapproximationNumPointsInPoly
                               (scopenvParams se)
                               dom >>= fun fuel =>
                                         Some (runScop_ fuel dom se initmem s).


  
  Definition getScopStmtLoads (ss: ScopStmt): P.AffineRelT :=
    match scopStmtType ss with
    | SSTstore _ => P.emptyAffineRel
    | SSTload =>  P.affineFnToAffineRel (scopStmtAccessFunction ss)
    end.

  Definition getScopStmtStores (ss: ScopStmt): P.AffineRelT :=
    match scopStmtType ss with
    | SSTload => P.emptyAffineRel
    | SSTstore _ =>  P.affineFnToAffineRel (scopStmtAccessFunction ss)
    end.
  
  Definition getScopStores(s: Scop): P.AffineRelT :=
    List.fold_left (fun rel ss =>
                      P.unionAffineRel rel
                                       (getScopStmtStores ss))
                   (scopStmts s)
                   P.emptyAffineRel.
  
  Definition getScopLoads(s: Scop): P.AffineRelT :=
    List.fold_left (fun rel ss =>
                      P.unionAffineRel rel
                                       (getScopStmtLoads ss))
                   (scopStmts s)
                   P.emptyAffineRel.



  (* Given a dependence relation and a schedule, we define what it means
    for a schedule to respect a dependence relation *)
  Definition scheduleRespectsDependence (schedule: P.AffineFnT)
             (dep: P.AffineRelT) : Prop :=
    forall (p1 q1: P.PointT), (P.arePointsRelated p1 q1 dep) = true ->
                              exists (p2 q2: P.PointT),
                                P.mapPoint schedule p1 = Some q1 ->
                                P.mapPoint schedule p2 = Some q2 ->
                                P.arePointsRelated (q1) (q2) dep = true.

  Definition scheduleRespectsRAW (schedule: P.AffineFnT) (s: Scop) : Prop :=
    exists (rel: P.AffineRelT),
      (P.getDependenceRelation (getScopStores s)
                               (getScopLoads s) = Some rel) /\
      scheduleRespectsDependence schedule rel.

  Definition scheduleRespectsWAW (schedule: P.AffineFnT) (s: Scop) : Prop :=
    exists (rel: P.AffineRelT),
      (P.getDependenceRelation (getScopStores s)
                               (getScopStores s) = Some rel) /\
      scheduleRespectsDependence schedule rel.


  Definition applyScheduleToScopStmt
             (schedule: P.AffineFnT)
             (ss: ScopStmt): option ScopStmt :=
    option_map (fun newschedule => {|
                    scopStmtArrayIdent := scopStmtArrayIdent ss;
                    scopStmtDomain:= scopStmtDomain ss;
                    scopStmtSchedule := newschedule;
                    scopStmtAccessFunction := scopStmtAccessFunction ss;
                    scopStmtType := scopStmtType ss
                  |}) (P.composeAffineFunction (scopStmtSchedule ss) schedule).

  Definition applyScheduleToScop
             (schedule: P.AffineFnT)
             (scop: Scop): option Scop :=
    option_map (fun newScopStmts => {|
                    scopStmts :=  newScopStmts;
                    scopIndvars := scopIndvars scop;
                  |})
               (option_traverse
                  (List.map (applyScheduleToScopStmt schedule)
                            (scopStmts scop))).

  (** =============PROOF============= **)
  
  Lemma applyScheduleToScopStmt_preserves_scop_stmt_domain:
    forall (ss ss': ScopStmt)
           (schedule: P.AffineFnT)
           (MAPPED: applyScheduleToScopStmt schedule ss = Some ss'),
      scopStmtDomain ss = scopStmtDomain ss'.
  Proof.
    intros.
    unfold applyScheduleToScopStmt in MAPPED.
    simpl.

    destruct (P.composeAffineFunction (scopStmtSchedule ss) schedule);
      simpl; auto; inversion MAPPED; auto.
  Qed.

  Hint Resolve applyScheduleToScopStmt_preserves_scop_stmt_domain.
  Hint Rewrite applyScheduleToScopStmt_preserves_scop_stmt_domain.

  Lemma getScopDomain_cons: forall (ss : ScopStmt)
                                   (sslist: list ScopStmt)
                                   sindvar,
      getScopDomain {| scopStmts := ss :: sslist; scopIndvars := sindvar |} =
      getScopDomain {| scopStmts := sslist; scopIndvars := sindvar; |}.
  Proof.
  Abort.

  Lemma applyScheduleToScopStmt_access_fn_eq:
    forall (ss ss': ScopStmt)
           (schedule: P.AffineFnT)
           (MAPPED: applyScheduleToScopStmt schedule ss = Some ss'),
      scopStmtAccessFunction ss = scopStmtAccessFunction ss'.
  Proof.
    intros.
    unfold applyScheduleToScopStmt in *.
    destruct (P.composeAffineFunction (scopStmtSchedule ss) schedule);
      simpl in MAPPED;
      inversion MAPPED;
      auto.
  Qed.

  Hint Resolve applyScheduleToScopStmt_access_fn_eq.
  Hint Rewrite applyScheduleToScopStmt_access_fn_eq.

  
  
  Lemma applyScheduleToScop_scop_domain_eq:
    forall (scop scop': Scop)
           (schedule: P.AffineFnT)
           (MAPPED: applyScheduleToScop schedule scop = Some scop'),
      getScopDomain scop = getScopDomain scop'.
  Proof.
    intros.
    destruct scop as [ss sindvar].
    induction ss; simpl in *.
    - (* base case *)
      unfold applyScheduleToScop in MAPPED.
      inversion MAPPED.
      auto.

    - simpl in MAPPED.
  Admitted.
  
  Hint Resolve applyScheduleToScop_scop_domain_eq.
  Hint Rewrite applyScheduleToScop_scop_domain_eq.

  
  Lemma isScopStmtActive_eq: forall (se: ScopEnvironment)
                                    (ss ss': ScopStmt)
                                    (schedule: P.AffineFnT)
                                    (MAPPEDSS: Some ss' =
                                               applyScheduleToScopStmt schedule ss),
      isScopStmtActive se ss = isScopStmtActive se ss'.
  Proof.
    intros.
    unfold isScopStmtActive.
    eauto.
  Qed.
  Hint Resolve isScopStmtActive_eq.
  Hint Rewrite isScopStmtActive_eq.
  
  
  
  
  
  Section SEMANTICS_PRESERVATION_PROOF.
    (** Preservation properties of applyScheduleToScop **)
    Variable schedule: P.AffineFnT.
    Variable scop scop': Scop.

    Variable RESPECTRAW: scheduleRespectsRAW schedule scop.
    Variable RESPECTWAW: scheduleRespectsWAW schedule scop.
    Variable MAPPED: applyScheduleToScop schedule scop = Some scop'.


    
    Lemma getActiveScopStmtsInScop_eq:
      forall (se: ScopEnvironment),
      exists (ss': list ScopStmt),
        option_traverse (List.map (applyScheduleToScopStmt schedule)
                                  (getActiveScopStmtsInScop scop se)) = Some ss' /\
        getActiveScopStmtsInScop scop' se = ss'.
    Proof.
      intros.
      unfold getActiveScopStmtsInScop.
    Admitted.
    
    
    Lemma runScopStepWithEnvAndMem_eq:
      forall (se: ScopEnvironment)
             (mem: Memory),
        runScopStepWithEnvAndMem scop se mem = runScopStepWithEnvAndMem
                                                 scop' se mem.
    Proof.
      intros.
      unfold runScopStepWithEnvAndMem.

      assert (ACTIVE_STMTS_IN_SCOP': exists ss': list ScopStmt,
                 option_traverse
                   (List.map (applyScheduleToScopStmt schedule)
                             (getActiveScopStmtsInScop scop se)) =
                 Some ss' /\
                 getActiveScopStmtsInScop scop' se = ss'
             ).
      admit.

      destruct ACTIVE_STMTS_IN_SCOP' as [ss' [SS' ACTIVE_IN_SCOP']].
      rewrite ACTIVE_IN_SCOP'.

      remember (getActiveScopStmtsInScop scop se) as ss eqn:ACTIVE_IN_SCOP.

      (* Induction on the scop statements themseleves *)
      induction ss.

      - simpl in *. inversion SS'. auto.
      - 
    Admitted.

    Hint Resolve runScopStepWithEnvAndMem_eq.

    
    Theorem runScop_eq:
      forall (fuel: nat)
        (se: ScopEnvironment)
        (initmem: Memory)
        (scopdom: P.PolyT)
        (SCOPDOMAIN: Some scopdom = getScopDomain scop'),
        runScop_ fuel scopdom se initmem scop =
        runScop_ fuel scopdom se initmem scop'.
    Proof.
      intros fuel.
      induction fuel; intros; auto.
      - simpl.
        destruct (stepScopenv scopdom se) eqn:SCOPENV'; auto.
        rewrite runScopStepWithEnvAndMem_eq.
        apply IHfuel; auto.
    Qed.

    Hint Resolve runScop_eq.


    (* Main theorem: Applying a valid schedule on a scop preserves
    the semantics of the scop *)
    Theorem applying_valid_schedule_preserves_semantics:
      forall (se: ScopEnvironment)
        (initmem: Memory),
        runScop scop se initmem = runScop scop' se initmem.
    Proof.
      intros.
      unfold runScop.
      
      erewrite applyScheduleToScop_scop_domain_eq; eauto.
      destruct (getScopDomain scop') eqn:SCOPDOMAIN;  auto.
      rename p into scopdom.
      simpl.

      destruct (P.getOverapproximationNumPointsInPoly (scopenvParams se) scopdom)
               eqn:FUEL; auto.
      rename n into fuel.
      simpl; auto.
    Qed.

  End SEMANTICS_PRESERVATION_PROOF.

  
End SCOP.

