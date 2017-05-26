(*
Calculus of construcctions
Set - type of sets
Type - type of type constructors
A -> B - type of functions from A to B
(forall x:T, U) family of types indexed on T
(fun (x:T) => U) - function from x of type T of body U (in CoC: [x:U] U)
( T U ) - T applied to U

Tactics to use
cbv flag1 flag2
	- call by value rewrite of term using flag1 and flag2 reductions (beta or delta for now)
lazy flag1 flag2
	- lazy evaluation rewrite of term using flag1 and flag2 reductions (beta or delta for now)
compute
	- alias for cbv beta iota
simpl
	- performs β-reductions and expands transparent constants (non lemmas)
Infix 
	- defines infix syntax 
*)

Section E4.
Variable A : Set.

Definition composition { A B C } := fun (x:B->C)(y:A->B)(z:A)=>(x (y z)).
Infix "o" := composition (left associativity, at level 94).


Definition id { A } := ....

Theorem e4 : forall x:A, (id o id) x = id x.
Proof.

Qed.

End E4.


Section E6.
(* Church encoded naturals *)
Definition N := forall X : Set, X -> (X -> X) -> X.
Definition Zero (X : Set) (o : X) (f : X -> X) := o.
Definition One  (X : Set) (o : X) (f : X -> X) := f (Zero X o f).

(* 6.1 *)
Definition Two  ...

(* 6.2 *)
Definition Succ ...

Lemma succOne : Succ One = Two.
Proof.

Qed.

(* 6.3 *)
Definition Plus (n m : N) : N
                := fun (X : Set) (o : X) (f : X -> X) => n X (m X o f) f.


Infix "++" := Plus (left associativity, at level 94).

Lemma sum1: (One ++ Zero) = One.
Proof.

Qed.

Lemma sum2: (One ++ One) = Two.
Proof.

Qed.

(* 6.4 *)
Definition Prod (n m : N) : N
                := fun (X:Set) (o:X) (f:X->X) => m X o (fun y:X => n X y f).


Infix "**" := ...

(* 6.5 *)
Lemma prod1 : (One ** Zero) = Zero.
Proof.

Qed.

Lemma prod2: (One ** Two) = Two.
Proof.

Qed.

End E6.


