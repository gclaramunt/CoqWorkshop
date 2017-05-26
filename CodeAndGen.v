(* Practico 6 *)
(*
http://coq.inria.fr/distrib/8.2/stdlib/Coq.Arith.Wf_nat.html
http://coq.inria.fr/distrib/8.2/stdlib/Coq.Wellfounded.Inverse_Image.html
http://coq.inria.fr/distrib/8.2/stdlib/
*)
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.omega.Omega.

Section Pred.
Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}.
Proof.
Qed.
End Pred.
Extraction Language Haskell.
Extraction "predecesor" predspec.

Section Trees.

Inductive bintree(A:Set):Set :=...

Inductive mirror (A:Set): bintree A -> bintree A -> Prop :=
  empty_mirror: mirror A (nil_tree A) (nil_tree A)
  | req_mirror: forall x:A, forall a b a' b': bintree A, 
mirror A a a' /\ mirror A b b' ->
mirror A (cons_tree A x a b) (cons_tree A x b' a').

Lemma MirrorC: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t')}.

Proof.
...
Qed.

Fixpoint inverse (A: Set)(t: bintree A){struct t}: bintree A := ...

Lemma MirrorInv: forall (A:Set) (t:bintree A),
{t':bintree A| mirror A t t'}.
Proof.
...
Qed.

End Trees.
Extraction Language Haskell.
Extraction "mirror_function" MirrorInv.
