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
    ihandler_mono : ∀ A e Φ Φ' s s',
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
    * iIntros "HH". iExists Φ, s. iSplitR; first eauto. by iSplitR; first eauto.
    * iIntros "[%Φ' [%s' [HmonΦ [Hmons HH]]]]". iApply (ihandler_mono with "[HmonΦ] [Hmons]"); eauto.
  - rewrite !Hmon. repeat f_equiv.
    * by apply HΦ.
    * by apply Hs.
Qed.

(** [inH H1 H2] means that, on events [E1], [H1] is equivalent to [H2]. *)
Class inH {Σ E1 E2} `{f : E1 -< E2} (H1 : iHandler Σ E1) (H2 : iHandler Σ E2) :=
  is_inH : ∀ A e Φ s, H1 A e Φ s ⊣⊢ H2 A (subevent A e) Φ s.

(** An [iHandler] for sum events [E1 +' E2] delegating to respective [iHandler]s. *)
Program Definition sumH {Σ E1 E2} (H1 : iHandler Σ E1) (H2 : iHandler Σ E2)
  : iHandler Σ (E1 +' E2) :=
  IHandler (λ A e,
    match e with
    | inl1 e1 => H1 A e1
    | inr1 e2 => H2 A e2
    end
  ) _.
Next Obligation.
  iIntros (?????? e ????) "HΦwand #Hswand HH".
  destruct e; by iApply (ihandler_mono with "HΦwand Hswand").
Qed.
Notation "H1 ⊕ H2" := (sumH H1 H2)
  (at level 59, right associativity) : type_scope.

Global Instance sumH_inH_l {Σ E1 E2} (H1 : iHandler Σ E1) (H2 : iHandler Σ E2) :
  inH H1 (H1 ⊕ H2).
Proof.
  intros ????. iSplit.
  - by iIntros "?".
  - by iIntros "?".
Qed.
Global Instance sumH_inH_r {Σ E1 E2} (H1 : iHandler Σ E1) (H2 : iHandler Σ E2) :
  inH H2 (H1 ⊕ H2).
Proof.
  intros ????. iSplit.
  - by iIntros "?".
  - by iIntros "?".
Qed.

(** This class covers "sequential" [iHandler]s which are insensitive to the
thread spawning continuation, that is, [iHandler]s that do not do concurrency. *)
Class Sequential {Σ E} (H : iHandler Σ E) :=
  is_seq : ∀ A e Φ s s', H A e Φ s -∗ H A e Φ s'.
Global Instance sumH_Sequential {Σ E1 E2} (H1 : iHandler Σ E1) (H2 : iHandler Σ E2)
  `{!Sequential H1} `{!Sequential H2} :
  Sequential (H1 ⊕ H2).
Proof.
  iIntros (A e Φ s s') "HH". destruct e.
  - by iApply Sequential0.
  - by iApply Sequential1.
Qed.
