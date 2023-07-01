From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From ITree Require Import ITree.
From ITree Require Import Eq.
From stdpp Require Import list.
From Paco Require Import paco.
From Paco Require Import paco3.
Import EqNotations.

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
  Context `{!invGS_gen HasNoLc Σ} {E : Type → Type} {H : iHandler Σ E}.

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

Section interleaving.
  Context `{!invGS_gen HasNoLc Σ} {E : Type → Type} {H : iHandler Σ E}.

  Variant interleavesF
    (interleaves : list (itree (threadpoolE E) unit) -> itree (threadpoolE E) unit -> itree E unit -> Prop)
    :  list (itree (threadpoolE E) unit)
    -> itree' (threadpoolE E) unit
    -> itree' E unit
    -> Prop :=
  | Terminates :
    interleavesF interleaves [] (RetF tt) (RetF tt)
  | ThreadEnds tp new_current interleaving' :
    new_current < length tp →
    interleaves (delete new_current tp) (nth new_current tp (Ret tt)) interleaving' →
    interleavesF interleaves tp (RetF tt) (TauF interleaving')
  | Steps current' tp interleaving' :
    interleavesF interleaves tp (TauF current') (TauF interleaving')
  | Emits tp A e k k' :
    (∀ a, interleaves tp (k' a) (k a)) →
    interleavesF interleaves tp (VisF (EEmit E A e) k') (VisF e k)
  | Yields tp k new_current interleaving' :
    new_current < length tp →
    interleaves (cons (k tt) (delete new_current tp)) (nth new_current tp (Ret tt)) interleaving' →
    interleavesF interleaves tp (VisF EYield k) (TauF interleaving')
  | Forks tp t k interleaving' :
    interleaves (cons t tp) (k tt) interleaving' →
    interleavesF interleaves tp (VisF (EFork t) k) (TauF interleaving').
  Hint Constructors interleavesF : iris_itree.
  Definition interleaves_
    (interleaves : list (itree (threadpoolE E) unit) -> itree (threadpoolE E) unit -> itree E unit -> Prop)
    :  list (itree (threadpoolE E) unit)
    -> itree (threadpoolE E) unit
    -> itree E unit
    -> Prop :=
    fun tp current interleaving =>
    interleavesF interleaves tp (observe current) (observe interleaving).

  Lemma interleavesF_mono interleaves interleaves' tp current interleaving :
    interleaves <3= interleaves' →
    interleavesF interleaves tp current interleaving →
    interleavesF interleaves' tp current interleaving.
  Proof.
    intros Hleq HinterleavesF. destruct HinterleavesF; eauto with iris_itree.
  Qed.
  Lemma interleaves__mono :
    monotone3 interleaves_.
  Proof.
    rewrite /monotone3 /interleaves_. intros. by eapply interleavesF_mono; last done.
  Qed.
  Hint Resolve interleaves__mono : paco.

  Definition interleaves :
    list (itree (threadpoolE E) unit) -> itree (threadpoolE E) unit -> itree E unit -> Prop :=
    paco3 interleaves_ bot3.

  Theorem interleaving
    (tp : list (itree (threadpoolE E) unit))
    (current : itree (threadpoolE E) unit)
    (interleaving : itree E unit) :
    interleaves tp current interleaving →
    ([∗ list] thread ∈ tp, WPi thread @ threadpoolH H; ⊤ {{ _, True }}) -∗
    WPi current @ threadpoolH H; ∅ {{ _, |={∅, ⊤}=> True }} -∗
    WPi interleaving @ H; ⊤ {{ _, True }}.
  Proof.
    iIntros "%Hinter Htp Hcurrent".
    punfold Hinter. induction Hinter.
  Admitted.

  Corollary interleaving_simple (concurrent : itree (threadpoolE E) unit) (interleaving : itree E unit) :
    interleaves [] concurrent interleaving →
    WPi concurrent @ threadpoolH H; ⊤ {{ _, True }} -∗
    WPi interleaving @ H; ⊤ {{ _, True }}.
End interleaving.
