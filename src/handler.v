From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From ITree Require Import ITree.
From ITree Require Import Eq.

(** An [iHandler] is the used-specified "recipe" used to define a custom
weakest [WPi]. It specifies how to interpret an event logically, given weakest
preconditions for continuations of the itree.
*)
Record iHandler Σ (E : Type → Type) := IHandler {
  ihandle :> ∀ A,
      (* Event [e] *)
      E A
      (* Continuation conditions [λ a, ▷ WPi k a @ H; ∅ {{ Φ }}] *)
    → (A → iProp Σ)
      (* Conditions for spawning threads [λ a, ▷ WPi k a @ H; ⊤ {{ False }}] *)
    → (A → iProp Σ)
      (* Condition [WPi Vis e k @ H; ∅ {{ Φ }}] *)
    → iProp Σ;
    (* TODO: Rename (scope is global). *)
    mono : ∀ A e Φ Φ' s s',
        (∀ a, Φ a -∗ Φ' a) -∗
      □ (∀ t, s t -∗ s' t) -∗
      ihandle A e Φ s -∗ ihandle A e Φ' s';
}.
Arguments IHandler {_ _} _.

Global Instance handler_ne Σ E n (H : iHandler Σ E) A :
  Proper ((=) ==> ((=) ==> dist n) ==> ((=) ==> dist n) ==> dist n) (ihandle _ _ H A).
Proof.
  intros e1 e2 <- Φ1 Φ2 HΦ s1 s2 Hs.
  assert (Hmon : ∀ Φ s, (H A e1 Φ s ⊣⊢ ∃ Φ' s', (∀ a, Φ' a -∗ Φ a) ∗ □ (∀ a, s' a -∗ s a) ∗ H A e1 Φ' s')).
  - iIntros (Φ s). iSplit.
    * iIntros "HH". iExists Φ, s. iSplitR; first eauto. iSplitR; first eauto. done.
    * iIntros "[%Φ' [%s' [HmonΦ [Hmons HH]]]]". iApply (mono with "[HmonΦ] [Hmons]"); eauto.
  - rewrite !Hmon. repeat f_equiv.
    * by apply HΦ.
    * by apply Hs.
Qed.

(** [inH H1 H2] means that, on events [E1], [H1] is equivalent to [H2]. *)
Class inH {Σ E1 E2} `{f : E1 -< E2} (H1 : iHandler Σ E1) (H2 : iHandler Σ E2) :=
  is_inH : ∀ A e Φ s, H1 A e Φ s ⊣⊢ H2 A (subevent A e) Φ s.
