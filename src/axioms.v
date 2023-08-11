From Coq.Logic Require Import ChoiceFacts EqdepFacts.
From stdpp Require Import tactics.

Module Ax : EqdepElimination.
  (** Invariance by Substitution of Reflexive Equality Proofs. This is implied by
  XM. Also, it is equivalent to UIP. See [1].
  [1] https://github.com/coq/coq/wiki/The-Logic-of-Coq#what-axioms-can-be-safely-added-to-coq. *)
  Axiom eq_rect_eq :
    ∀ (U : Type) (p : U) (Q : U → Type) (x : Q p) (h : p = p),
      x = eq_rect p Q x p h.
End Ax.

Module Export UIPM := EqdepTheory Ax.

Ltac simplify_K :=
  repeat match goal with
  | H : existT _ _ = existT _ _ |- _ =>
     apply UIPM.inj_pair2 in H
  end; simplify_eq.
