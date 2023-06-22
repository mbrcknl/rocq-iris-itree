From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From ITree Require Import ITree.
From ITree Require Import Eq.
From ITree Require Import TranslateFacts.
From iris.itree Require Import event.

(** An [iHandler] is the used-specified "recipe" used to define a custom
weakest [WPi]. It specifies how to interpret an event logically, given weakest
preconditions for continuations of the itree.
*)
Record iHandler Σ (EF : (Type → Type) → Type → Type) := IHandler {
  ihandle :> ∀ preE A,
      (* Event [e] *)
      EF preE A
      (* Continuation conditions [λ a, ▷ WPi k a @ H; ∅ {{ Φ }}] *)
    → (A → iProp Σ)
      (* Conditions for spawning threads [λ a, ▷ WPi t @ H; ⊤ {{ True }}] *)
    → (itree preE unit → iProp Σ)
      (* Condition [WPi Vis e k @ H; M {{ Φ }}] *)
    → iProp Σ;
}.
Arguments IHandler {_ _} _.

Import EqNotations.
(** Convenient helper for constructing [iHandler]s that treat only events with
a particular, fixed answrer type [A]. *)
Definition IHandlerT {Σ} {EF : (Type → Type) → Type → Type} {A : Type}
  (H : ∀ preE, (EF preE A → (A → iProp Σ) → (itree preE unit → iProp Σ) → iProp Σ)) :
  iHandler Σ EF :=
  IHandler (λ preE A' e Φ s, ∃ x : A' = A, H preE
    (rew [λ A, EF preE A] x in e)
    (rew [λ A, (A → iProp Σ)%type] x in Φ)
    s)%I.

(** Restricts a handler along a morphism of event types. *)
Definition restrictH {Σ EF2} EF1 (H1 : iHandler Σ EF2) `{EF1 --< EF2} : iHandler Σ EF1 :=
  IHandler (λ preE A e Φ s, H1 preE A (subevent A e) Φ s)%I.

(** Asserts that the [iHandler] [H1] is stronger than [H2]. *)
Definition subH {Σ EF} (H1 H2 : iHandler Σ EF) : iProp Σ :=
  ∀ preE A e Φ s, H1 preE A e Φ s -∗ H2 preE A e Φ s.

Lemma subH_transitive {Σ EF} (H1 H2 H3 : iHandler Σ EF) :
  subH H1 H2 -∗
  subH H2 H3 -∗
  subH H1 H3.
Proof.
  iIntros "Hsub1 Hsub2" (preE A e Φ s) "HH1". iApply "Hsub2". by iApply "Hsub1".
Qed.

(** [inH H1 H2] means that, on events [E1], [H1] is stronger than [H2]. *)
Class inH {Σ EF1 EF2} `{f : EF1 --< EF2} (H1 : iHandler Σ EF1) (H2 : iHandler Σ EF2) :=
  is_inH : ⊢ subH H1 (restrictH EF1 H2).

(** Disjunction of two [iHandler]s. *)
Global Instance iHandler_union Σ E : Union (iHandler Σ E) :=
  λ H1 H2, IHandler (λ preE A e Φ s, H1 preE A e Φ s ∨ H2 preE A e Φ s)%I.

Lemma subH_union_l Σ EF H1 H2 :
  ⊢ subH (Σ:=Σ) (EF:=EF) H1 (H1 ∪ H2).
Proof. iIntros (?????) "HH". by iLeft. Qed.
Lemma subH_union_r Σ EF H1 H2 :
  ⊢ subH (Σ:=Σ) (EF:=EF) H2 (H1 ∪ H2).
Proof. iIntros (?????) "HH". by iRight. Qed.
Global Instance in_union_l {Σ EF} (H1 : iHandler Σ EF) (H2 : iHandler Σ EF) : inH H1 (H1 ∪ H2).
Proof. apply subH_union_l. Qed.
Global Instance in_union_r {Σ E} (H1 : iHandler Σ E) (H2 : iHandler Σ E) : inH H2 (H1 ∪ H2).
Proof. apply subH_union_r. Qed.
