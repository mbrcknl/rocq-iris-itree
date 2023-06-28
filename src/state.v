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

(* Handlers for [stateE]. *)
Definition get_stateH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} : iHandler Σ (stateEF S) :=
  IHandlerT (λ preE e Φ s,
      ⌜e = EGetState preE⌝ ∗ (∀ s, state_interp s -∗ (state_interp s ∗ Φ s)))%I.
Definition set_stateH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HasNoLc Σ} : iHandler Σ (stateEF S) :=
  IHandlerT (λ preE e Φ s, ∃ s',
    ⌜e = ESetState preE s'⌝ ∗ (∀ s, state_interp s ={∅}=∗ (state_interp s' ∗ Φ tt)))%I.
(** At each [EYield], we re-assert all invariants as well as the [state_interp]. *)
Definition yieldH {Σ} (S : Type) `{!stateHGS Σ S} `{!invGS_gen HasNoLc Σ} `{!stateInterp Σ S} : iHandler Σ (stateEF S) :=
  IHandlerT (λ preE e Φ s, ⌜e = EYield preE⌝ ∗
    |={∅, ⊤}=> |={⊤, ∅}=> Φ tt)%I.
Definition forkH {Σ} (S : Type) `{!stateHGS Σ S} : iHandler Σ (stateEF S) :=
  IHandlerT (λ preE e Φ s, ∃ t, ⌜e = EFork preE t⌝ ∗ Φ tt ∗ s t)%I.

Definition stateH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HasNoLc Σ} : iHandler Σ (stateEF S) :=
  get_stateH S ∪ set_stateH S ∪ yieldH S ∪ forkH S.

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
    do 3 iLeft. iExists eq_refl. iSplit; first done.
    iIntros (s) "Hs". iDestruct ("Hwp" with "Hs") as "[Hs Hwp]". iFrame. iNext.
    rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_set {R} (s' : S) (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s ={M}=∗ state_interp s' ∗ ▷ WPi (k tt) @ H; M {{ Φ }}) -∗
    WPi (visF (ESetState E s') k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    do 2 iLeft. iRight. iExists eq_refl. iExists _.
    iSplit; first done. iIntros (s) "Hs". simpl. iMod "Hfupd" as "_".
    iDestruct ("Hwp" with "Hs") as ">[Hs Hwp]". iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_fork {R} (t : itree E unit) (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (▷ WPi (k tt) @ H; M {{ Φ }} ∗ ▷ WPi t @ H; ⊤ {{ _, True }}) -∗
    WPi (visF (EFork E t) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "[Hwp1 Hwp2]". iApply wpi_vis.
    iApply is_inH. iRight. iExists eq_refl, t. iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iSplit; first done.
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
    iLeft. iRight. iExists eq_refl.
    iApply fupd_frame_l. iSplit; first done.
    iApply fupd_mask_intro_subseteq; first done.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.
End wp_state.
