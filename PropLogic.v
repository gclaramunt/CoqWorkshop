(* 
Use intro/intros, apply, assumption, split, left, right, absurd, elim, unfold, exact, cut 
*)

(* Propositional logic *)

Section P1.
Variables A B C:Prop.

(* PROVE I K S *)
(*  
"for all things you could prove,
   if you have a proof of it, then you have a proof of it."
 *)
(* I *)
Theorem e11: A->A.

(* K *)
Theorem e12: A->B->A.

(* S *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).



(*
Use split , left , right , absurd , elim , unfold (among others).
Remember  ∼A is A→False, and A↔B is (A→B)∧(B→A).
*)

Theorem e21: A -> ~~A.

Theorem e22: A -> B -> (A /\ B).

Theorem e24: A->(A\/B).

Theorem e25: B->(A\/B).

Theorem e26: (A \/ B) -> (B \/ A).

Theorem e28: False->A.




Theorem e31: (A\/B) -> ~(~A/\~B).

Theorem e32: A\/B <-> B\/A.

Theorem e33: A\/B -> ((A->B)->B).

End P1.
