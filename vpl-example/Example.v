Require Import ZArith.

Require Vpl.PedraZ.
Import Vpl.PedraZ.FullDom.

Import BinNums.
Import NumC.
Import ASCond.
Import ZCond.
Import Term.
Import String.
Import Annot.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope impure_scope.

Bind Scope cond_scope with cond.
Bind Scope term_scope with term.
Delimit Scope cond_scope with cond.
Delimit Scope term_scope with term.

Definition sub (x y: term) := Add x (Opp y).

Infix "+" := Add: term_scope.
Infix "-" := sub: term_scope.
Infix "*" := Mul: term_scope.
Infix "<=" := (Atom Le): cond_scope.
Infix "<" := (Atom Lt): cond_scope.
Infix "=" := (Atom Eq): cond_scope.
Infix "<>" := (Atom Neq): cond_scope.
Infix "/\" := (BinL AND): cond_scope.
Infix "\/" := (BinL OR): cond_scope.

Local Notation var:=ProgVar.PVar.t.
Coercion Var: var >-> term.
Definition idZ (x:Z) : ZNum.t := x.
Coercion idZ: Z >-> ZNum.t.
Coercion Cte: ZNum.t >-> term.
Coercion Annot: topLevelAnnot >-> Funclass.
Definition idTerm (x:term): ASTerm.ZTerm.term := x.
Coercion idTerm: term >-> ASTerm.ZTerm.term.


Module Tests.

Definition x: var := 1%positive.

Local Definition top := PedraZ.FullDom.top.

Definition test1 := 
   BIND p <- assume (x=3) top -;
   assert (x <= 2) p.

Lemma test1_returns_false:
  WHEN b <- test1 THEN b=false.
Proof.
  VPLAsimplify.
  destruct exta0; simpl in * |- *; auto.
  intros X; assert (ZNum.Le 3 2).
  + apply (X (fun _ => 3)). auto with vpl.
  + unfold ZNum.Le in * |-. omega.
Qed.


Definition test2 :=
   BIND p <- assume (x=3) top -;
   assert (2 <= x) p.

(* NB: Here, we can not prove that test2 returns true !

Returning "false" would be a bug of completeness in the VPL, 
but not a bug of correctness.

*)

Definition y: var := 2%positive.
Definition a: var := 3%positive.
Definition b: var := 4%positive.
Definition r: var := 5%positive.

(* example with a (non-linear) barycentric computation in "r" *)
Definition test3 :=
  BIND p1 <- assume (x <= y /\ 0 <= a /\ a <= 100) top -;
  BIND p2 <- assume (r = a*x + (100-a)*y) p1 -;
  assert (100*x  <= r /\ r <= 100*y) p2.

(* example with a (non-linear) parabola computation in "r" *)
Definition test4 :=
  BIND p1 <- assume (a=2 /\ b=100 /\ y=10 /\ y <= x /\ x <= b) top -;
  BIND p2 <- assume (r = a*x*x) p1 -;
  assert (a*y*y  <= r /\ r <= a*b*b /\ r <= a*((b+y)*x-b*y)) p2.


End Tests.
