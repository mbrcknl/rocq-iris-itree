From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
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

(** An event type for stateful programs. *)
Inductive stateE (S : Type) : Type → Type :=
  (** Get the global state. *)
  | EGetState : stateE S S
  (** Set the global state. *)
  | ESetState (x : S) : stateE S unit.
Arguments EGetState {_}.
Arguments ESetState {_} _.

(** State interpretation predicate which is enforced at every [EYield], [EGet]
and [ESet]. *)
Class stateInterp (Σ : gFunctors) (S : Type) := state_interp : S → iProp Σ.

(** Proposition asserting read-only access to the state interpretation. *)
Definition state_ro {S} `{!stateInterp Σ S} (s : S) : iProp Σ :=
  ∀ s', state_interp s' -∗ state_interp s' ∗ ⌜ s = s' ⌝.

(** [iHandler] for [stateE]. *)
Program Definition stateH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HasNoLc Σ} : iHandler Σ (stateE S) :=
  IHandler (λ A e,
    match e with
    | EGetState    => λ Φ s, (∀ s, state_interp s -∗ (state_interp s ∗ Φ s))
    | ESetState s' => λ Φ s, (∀ s, state_interp s ={∅}=∗ (state_interp s' ∗ Φ tt))
    end
  )%I _.
Next Obligation.
  iIntros (?????? e ????) "HΦwand Hswand". destruct e.
  - iIntros "Hget" (?) "Hstate". iDestruct ("Hget" with "Hstate") as "[$ HΦ]". by iApply "HΦwand".
  - iIntros "Hset" (?) "Hstate". iDestruct ("Hset" with "Hstate") as ">[$ HΦ]". by iApply "HΦwand".
Qed.

Section wp_state.
  Context {S : Type} `{!stateHGS Σ S} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.
  Context `{!stateInterp Σ S}.
  Context {H : iHandler Σ E} `{stateE S -< E} `{inH Σ (stateE S) E (stateH S) H}.

  Lemma wpi_get {R} (k : S → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s -∗ state_interp s ∗ ▷ WPi (k s) @ H; M {{ Φ }}) -∗
    WPi (vis EGetState k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". iDestruct ("Hwp" with "Hs") as "[Hs Hwp]". iFrame.
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_set {R} (s' : S) (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s ={M}=∗ state_interp s' ∗ ▷ WPi (k tt) @ H; M {{ Φ }}) -∗
    WPi (vis (ESetState s') k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". simpl. iMod "Hfupd" as "_".
    iDestruct ("Hwp" with "Hs") as ">[Hs Hwp]". iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.
End wp_state.

(** An event type transformer for adding concurrency. *)
CoInductive threadpoolE (E : Type → Type) : Type → Type :=
  | EEmit (A : Type) (e : E A) : threadpoolE E A
  (** Yield control to another (demonically chosen) thread in the thread-pool. *)
  | EYield : threadpoolE E unit
  (** Split the thread into two threads corresponding to the answers [true]
  and [false]. *)
  | EFork (t : itree (threadpoolE E) unit) : threadpoolE E unit.
Arguments EYield {_}.
Arguments EFork {_} _.

Global Instance E_threadpoolE (E : Type → Type) : Subevent E (threadpoolE E) :=
  { resum := λ A e, EEmit _ A e }.

(** [iHandler] transformer for [threadpoolE]. *)
Program Definition threadpoolH {Σ E} `{!invGS_gen HasNoLc Σ} (H : iHandler Σ E) : iHandler Σ (threadpoolE E) :=
  IHandler (λ A e,
    match e with
    | EEmit _ _ e' => λ Φ s, H _ e' Φ (λ t, s (translate (EEmit _) t))
    | EYield       => λ Φ s, |={∅, ⊤}=> |={⊤, ∅}=> Φ tt
    | EFork t      => λ Φ s, Φ tt ∗ s t
    end
  )%I _.
Next Obligation.
  iIntros (??????????) "HΦwand #Hswand". destruct e.
  - iIntros "HH". iApply (mono with "[HΦwand] [Hswand]"); last done.
    * exact.
    * iModIntro. iIntros (t) "Hs". by iApply "Hswand".
  - iIntros "HΦfupd". by iApply "HΦwand".
  - iIntros "[HΦ Hs]". iSplitL "HΦ HΦwand".
    * by iApply "HΦwand".
    * by iApply "Hswand".
Qed.

Section wp_threadpool.
  Context {S : Type} `{!invGS_gen HasNoLc Σ} {E : Type → Type} {H : iHandler Σ E}.

  Lemma wpi_fork {R} (t : itree (threadpoolE E) unit) (k : unit → itree (threadpoolE E) R) (M : coPset) (Φ : R → iProp Σ) :
    (▷ WPi (k tt) @ threadpoolH H; M {{ Φ }} ∗ ▷ WPi t @ threadpoolH H; ⊤ {{ _, True }}) -∗
    WPi (Vis (EFork t) k) @ threadpoolH H; M {{ Φ }}.
  Proof.
    iIntros "[Hwp1 Hwp2]". iApply wpi_vis.
    rewrite /threadpoolH. iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp1".
  Qed.

  (** Note here crucially that the mask has to be full for the rule to apply.
  This means that you cannot step over an [EYield] if there are open
  invariants. It amounts to the typical requirement of atomicity in the
  invariant opening rule known from "normal Iris". *)
  Lemma wpi_yield {R} (k : unit → itree (threadpoolE E) R) (M : coPset) (Φ : R → iProp Σ) :
    (▷ WPi (k tt) @ threadpoolH H; ⊤ {{ Φ }}) -∗
    WPi (Vis EYield k) @ threadpoolH H; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    rewrite /threadpoolH. simpl. iApply fupd_mask_intro_subseteq; first done.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.
End wp_threadpool.
