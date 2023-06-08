From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From ITree Require Import ITree.

(** An [iHandler] is the used-specified "recipe" used to define a custom
weakest [WPi]. It specifies how to interpret an event logically, given weakest
preconditions for continuations of the itree.

An [iHandler] is a function that takes an event [E A] with answer type [A],
as well as continuations [k : A → iProp Σ], and produces a new logical
expression [iProp Σ]. Given an itree [Vis e t], [ihandle e k] should be
thought of as a verification condition for this itree, assuming that
[k a : iProp Σ] is a verification condition for the itree [t a]. We refer
the reader to [WPi] for a precise meaning of this intuition.
*)
Record iHandler Σ (E : Type → Type) := IHandler {
  ihandle : ∀ A, E A → (A → iProp Σ) → iProp Σ;
}.
Arguments IHandler {_ _} _.
Coercion ihandle : iHandler >-> Funclass.

Import EqNotations.
(** Convenient helper for constructing [iHandler]s that treat only events with
a particular, fixed answrer tytpe [A]. *)
Definition IHandlerT {Σ} {E : Type → Type} {A : Type}
  (H : (E A → (A → iProp Σ) → iProp Σ)) : iHandler Σ E :=
  IHandler (λ A' e Φ, ∃ x : A' = A, H
    (rew [λ A, E A] x in e)
    (rew [λ A, (A → iProp Σ)%type] x in Φ))%I.

(** Maps events along a morphism of event types. *)
Definition liftE {E1} E2 `{f : E1 -< E2} {T} (e : E1 T) : E2 T :=
  (@resum _ _ _ _ f) _ e.
(** Restricts a handler along a morphism of event types. *)
Definition restrictH {Σ E2} E1 (H1 : iHandler Σ E2) `{!E1 -< E2} : iHandler Σ E1 :=
  IHandler (λ T e Φ, H1 T (liftE E2 e) Φ)%I.

(** Asserts that the [iHandler] [H1] is stronger than [H2]. *)
Definition subH {Σ E} (H1 H2 : iHandler Σ E) : iProp Σ :=
  ∀ T e Φ, H1 T e Φ -∗ H2 T e Φ.
(** [inH H1 H2] means that, on events [E1], [H1] is stronger than [H2]. *)
Class inH {Σ E1 E2} `{!E1 -< E2} (H1 : iHandler Σ E1) (H2 : iHandler Σ E2) :=
  is_inH : ⊢ subH H1 (restrictH E1 H2).

(** Disjunction of two [iHandler]s. *)
Global Instance iHandler_union Σ E : Union (iHandler Σ E) :=
  λ H1 H2, IHandler (λ T e Φ, H1 T e Φ ∨ H2 T e Φ)%I.

Lemma subH_union_l Σ E H1 H2 :
  ⊢ subH (Σ:=Σ) (E:=E) H1 (H1 ∪ H2).
Proof. iIntros (???) "HH". by iLeft. Qed.
Lemma subH_union_r Σ E H1 H2 :
  ⊢ subH (Σ:=Σ) (E:=E) H2 (H1 ∪ H2).
Proof. iIntros (???) "HH". by iRight. Qed.
Global Instance in_union_l {Σ E} (H1 : iHandler Σ E) (H2 : iHandler Σ E) : inH H1 (H1 ∪ H2).
Proof. apply subH_union_l. Qed.
Global Instance in_union_r {Σ E} (H1 : iHandler Σ E) (H2 : iHandler Σ E) : inH H2 (H1 ∪ H2).
Proof. apply subH_union_r. Qed.
