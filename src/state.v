From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import event.
From ITree Require Import ITree.

Class stateHPreG (Σ : gFunctors) (S : Type) := StateHPreG {
  stateH_pre_ghost_varG :> ghost_varG Σ S;
}.
Class stateHGS (Σ : gFunctors) (S : Type) := StateHGS {
  stateH_ghost_varG :> ghost_varG Σ S;
  stateH_name : gname;
}.
Definition stateHΣ S : gFunctors :=
  #[ ghost_varΣ S ].
Global Instance subG_stateHΣ Σ S :
  subG (stateHΣ S) Σ → stateHPreG Σ S.
Proof. solve_inG. Qed.

(** An event type for stateful programs with concurrency. *)
Inductive stateEF (S : Type) (preE : Type → Type) : Type → Type :=
  (** Get the global state. *)
  | EGetState : stateEF S preE S
  (** Set the global state. *)
  | ESetState (x : S) : stateEF S preE unit
  (** Yield control to another (demonically chosen) thread in the thread-pool. *)
  | EYield : stateEF S preE unit
  (** Split the thread into two threads corresponding to the answers [true]
  and [false]. *)
  | EFork (t : itree preE unit) : stateEF S preE unit.
Arguments EGetState {_}.
Arguments ESetState {_} _.
Arguments EYield {_}.
Arguments EFork {_} _.

(** State interpretation predicate which is enforced at every [EYield], [EGet]
and [ESet]. *)
Class stateInterp (Σ : gFunctors) (S : Type) := state_interp : S → iProp Σ.

(** Proposition asserting read-only access to the state interpretation. *)
Definition state_ro {S} `{!stateInterp Σ S} (s : S) : iProp Σ :=
  ∀ s', state_interp s' -∗ state_interp s' ∗ ⌜ s = s' ⌝.

Program Definition stateH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HasNoLc Σ} : iHandler Σ (stateEF S) :=
  IHandler (λ preE A e,
    match e with
    | EGetState _    => λ Φ s, (∀ s, state_interp s -∗ (state_interp s ∗ Φ s))
    | ESetState _ s' => λ Φ s, (∀ s, state_interp s ={∅}=∗ (state_interp s' ∗ Φ tt))
    | EYield _       => λ Φ s, |={∅, ⊤}=> |={⊤, ∅}=> Φ tt
    | EFork _ t      => λ Φ s, Φ tt ∗ s t
    end
  )%I _.
Next Obligation.
  iIntros (??????? e ????) "HΦwand Hswand". destruct e.
  - iIntros "Hget" (?) "Hstate". iDestruct ("Hget" with "Hstate") as "[$ HΦ]". by iApply "HΦwand".
  - iIntros "Hset" (?) "Hstate". iDestruct ("Hset" with "Hstate") as ">[$ HΦ]". by iApply "HΦwand".
  - iIntros "HΦfupd". by iApply "HΦwand".
  - iIntros "[HΦ Hs]". iSplitL "HΦ HΦwand".
    * by iApply "HΦwand".
    * by iApply "Hswand".
Qed.

Section wp_state.
  Context {S : Type} `{!stateHGS Σ S} `{!EventFixpoint EF E} `{!invGS_gen HasNoLc Σ}.
  Context `{!stateInterp Σ S}.
  Context {H : iHandler Σ EF} `{stateEF S --< EF} `{inH Σ (stateEF S) EF (stateH S) H}.

  Lemma wpi_get {R} (k : S → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s -∗ state_interp s ∗ ▷ WPi (k s) @ H; M {{ Φ }}) -∗
    WPi (visF (EGetState E) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". iDestruct ("Hwp" with "Hs") as "[Hs Hwp]". iFrame.
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_set {R} (s' : S) (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s ={M}=∗ state_interp s' ∗ ▷ WPi (k tt) @ H; M {{ Φ }}) -∗
    WPi (visF (ESetState E s') k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". simpl. iMod "Hfupd" as "_".
    iDestruct ("Hwp" with "Hs") as ">[Hs Hwp]". iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_fork {R} (t : itree E unit) (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (▷ WPi (k tt) @ H; M {{ Φ }} ∗ ▷ WPi t @ H; ⊤ {{ _, True }}) -∗
    WPi (visF (EFork E t) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "[Hwp1 Hwp2]". iApply wpi_vis.
    iApply is_inH. rewrite /stateH. iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp1".
  Qed.

  (** Note here crucially that the mask has to be full for the rule to apply.
  This means that you cannot step over an [EYield] if there are open
  invariants. It amounts to the typical requirement of atomicity in the
  invariant opening rule known from "normal Iris". *)
  Lemma wpi_yield {R} (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (▷ WPi (k tt) @ H; ⊤ {{ Φ }}) -∗
    WPi (visF (EYield E) k) @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis. iApply is_inH.
    rewrite /stateH. simpl. iApply fupd_mask_intro_subseteq; first done.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.
End wp_state.
