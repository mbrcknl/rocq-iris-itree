From stdpp Require Import prelude.
From ITree Require Import ITree.

(* TODO: Hint modes and arguments. Look in ITree library. *)

Class SubeventF (EF1 EF2 : (Type → Type) → Type → Type) :=
  incl : ∀ preE, EF1 preE ~> EF2 preE.

Notation "E --< F" := (SubeventF E F)
  (at level 92, left associativity) : type_scope.

Definition subeventF {EF1 EF2 : (Type → Type) → Type → Type} {preE : Type → Type} `{EF1 --< EF2}
  : EF1 preE ~> EF2 preE := incl preE.

Global Instance subeventF_id EF : SubeventF EF EF := { incl := λ preE A, id }.

Global Instance subeventF_subevent E `{!SubeventF EF1 EF2} : Subevent (EF1 E) (EF2 E) :=
  { resum := incl E }.

(* TODO: Replace by isofixpoint. *)
Class EventFixpoint (EF : (Type → Type) → Type → Type) (E : Type → Type) :=
  eq_fix : E = EF E.

Import EqNotations.
Global Instance subevent_fixpoint `{!EventFixpoint EF E} : Subevent E (EF E) :=
  { resum := λ A e, rew [λ T, T A] eq_fix in e }.
Global Instance subevent_fixpoint' `{!EventFixpoint EF E} : Subevent (EF E) E :=
  { resum := λ A e, rew [λ T, T A] (eq_sym eq_fix) in e }.

Definition visF `{!EventFixpoint EF2 E2} `{!EF1 --< EF2} {A R} (e : EF1 E2 A) (k : A → itree E2 R) : itree E2 R :=
  Vis (rew [λ T, T A] eq_sym eq_fix in subevent A e) k.
