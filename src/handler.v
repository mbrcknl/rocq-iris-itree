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
      (* Condition [WPi Vis e k @ H; ∅ {{ Φ }}] *)
    → iProp Σ;
    mono : ∀ preE A e Φ Φ' s s',
        (∀ a, Φ a -∗ Φ' a) -∗
      □ (∀ t, s t -∗ s' t) -∗
      ihandle preE A e Φ s -∗ ihandle preE A e Φ' s';
}.
Arguments IHandler {_ _} _.

Global Instance handler_ne Σ EF n (H : iHandler Σ EF) preE A :
  Proper ((=) ==> ((=) ==> dist n) ==> ((=) ==> dist n) ==> dist n) (ihandle _ _ H preE A).
Proof.
  intros e1 e2 <- Φ1 Φ2 HΦ s1 s2 Hs.
  assert (Hmon : ∀ Φ s, (H preE A e1 Φ s ⊣⊢ ∃ Φ' s', (∀ a, Φ' a -∗ Φ a) ∗ □ (∀ a, s' a -∗ s a) ∗ H preE A e1 Φ' s')).
  - iIntros (Φ s). iSplit.
    * iIntros "HH". iExists Φ, s. iSplitR; first eauto. iSplitR; first eauto. done.
    * iIntros "[%Φ' [%s' [HmonΦ [Hmons HH]]]]". iApply (mono with "[HmonΦ] [Hmons]"); eauto.
  - rewrite !Hmon. repeat f_equiv.
    * by apply HΦ.
    * by apply Hs.
Qed.

(** Restricts a handler along a morphism of event types. *)
Program Definition restrictH {Σ EF2} EF1 (H1 : iHandler Σ EF2) `{EF1 --< EF2} : iHandler Σ EF1 :=
  IHandler (λ preE A e Φ s, H1 preE A (subevent A e) Φ s)%I _.
Next Obligation.
  iIntros (????????????) "HΦ Hs". by iApply (mono with "[HΦ]").
Qed.

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
