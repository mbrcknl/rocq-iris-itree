From Coq.Logic Require Import ChoiceFacts EqdepFacts.
From stdpp Require Import tactics.

Module Ax : EqdepElimination.

(* Invariance by Substitution of Reflexive Equality Proofs (already implied XM), UIP (`Eq_rect_eq` from `Coq.Logic.EqdepFacts`) *)
Axiom eq_rect_eq :
    forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
      x = eq_rect p Q x p h.

End Ax.

Module Export UIPM := EqdepTheory Ax.

Ltac simplify_K :=
  repeat match goal with
  | H : existT _ _ = existT _ _ |- _ =>
     apply UIPM.inj_pair2 in H
  end; simplify_eq.
