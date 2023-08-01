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

(** Thread continuation. *)
Variant thread :=
 | CurrentThread
 | NewThread.
(** An event type for concurrency. *)
Variant threadpoolE : Type → Type :=
  (** Unix-style fork that splits the thread (copying its stack) into two
  threads, distinguished by the answer value of type [[thread]]. Execution
  continues in the thread with answer [CurrentThread] until a [EYield] is
  emitted. *)
  | EFork : threadpoolE thread
  (** Yield control to another (demonically chosen) thread in the thread-pool. *)
  | EYield : threadpoolE unit
  (** (Safely) kill the current thread and yield. *)
  | EKillThread : threadpoolE Empty_set.
Arguments EYield.
Arguments EFork.
Arguments EKillThread.

(** [iHandler] for [threadpoolE]. *)
Program Definition threadpoolH {Σ} `{!invGS_gen HasNoLc Σ} : iHandler Σ threadpoolE :=
  IHandler (λ A e,
    match e with
    (** We define the iHandler in a way that imposes a semantic restriction on
    [EFork] disallowing returning in the [NewThread] continuation, even
    though it is possible to define [itree]s that do so. From the point of view
    of [WPi], we are thus declaring such returns as unsafe. This
    overapproximation is justified from our applications. *)
    | EFork      => λ Φ s, Φ CurrentThread ∗ s NewThread
    | EYield     => λ Φ _, |={∅, ⊤}=> |={⊤, ∅}=> Φ tt
    | EKillThread => λ _ _, |={∅, ⊤}=> True
    end
  )%I _.
Next Obligation.
  iIntros (????????) "HΦwand #Hswand". destruct e.
  - iIntros "[HΦ Hs]". iSplitL "HΦwand HΦ".
    * by iApply "HΦwand".
    * by iApply "Hswand".
  - iIntros "HΦ". by iApply "HΦwand".
  - by iIntros "?".
Qed.

Section wp_threadpool.
  Context `{!invGS_gen HasNoLc Σ} {E : Type → Type} {H : iHandler Σ E}.
  Context `{threadpoolE -< E} `{inH Σ threadpoolE E threadpoolH H}.

  Lemma wpi_fork {R} (k : thread → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (▷ WPi (k CurrentThread) @ H; M {{ Φ }} ∗ ▷ WPi (k NewThread) @ H; ⊤ {{ _, False }}) -∗
    WPi (vis EFork k) @ H; M {{ Φ }}.
  Proof.
    iIntros "[Hwpcur Hwpnew]". iApply wpi_vis.
    rewrite /threadpoolH. iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply is_inH. simpl. iSplitL "Hwpcur Hfupd".
    - iNext. iMod "Hfupd". by iApply wpi_update_post_emp_mask.
    - done.
  Qed.

  (** Note here crucially that the mask has to be full for the rule to apply.
  This means that you cannot step over an [EYield] if there are open
  invariants. It amounts to the typical requirement of atomicity in the
  invariant opening rule known from "normal Iris". *)
  Lemma wpi_yield {R} (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (▷ WPi (k tt) @ H; ⊤ {{ Φ }}) -∗
    WPi (vis EYield k) @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis. iApply is_inH. simpl.
    iApply fupd_mask_intro_subseteq; first done.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_kill {R} (k : Empty_set → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (|={∅, ⊤}=> True) -∗
    WPi (vis EKillThread k) @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis. iApply is_inH. simpl.
    by iApply fupd_mask_intro_subseteq; first done.
  Qed.
End wp_threadpool.

Lemma ret_observe_eqit {E R} (r : R) (t : itree E R) :
  RetF r = observe t →
  Ret r ≅ t.
Proof.
  intros Heq. rewrite /eq_itree /eqit. pfold. rewrite /eqit_ -Heq. by constructor.
Qed.

Lemma tau_observe_eqit {E R} (t t' : itree E R) :
  TauF t' = observe t →
  Tau t' ≅ t.
Proof.
  intros Heq. rewrite /eq_itree /eqit. pfold. rewrite /eqit_ -Heq. constructor.
  rewrite /upaco2 /bot2. left. by apply Reflexive_eqit.
Qed.

Lemma vis_observe_eqit {E A R} (e : E A) (k : A → itree E R) (t : itree E R) :
  VisF e k = observe t →
  Vis e k ≅ t.
Proof.
  intros Heq. rewrite /eq_itree /eqit. pfold. rewrite /eqit_ -Heq. constructor.
  rewrite /upaco2 /bot2. left. by apply Reflexive_eqit.
Qed.

Lemma big_sepL_delete' {Σ} A (Φ : A → iProp Σ) l i x :
  l !! i = Some x →
  ([∗ list] y ∈ l, Φ y) ⊣⊢
  Φ x ∗ [∗ list] y ∈ (delete i l), Φ y.
Proof.
  intros Hidx. rewrite -(take_drop_middle l i x) // !big_sepL_app.
  rewrite assoc -!(comm _ (Φ _)) -assoc -big_sepL_app. do 2 f_equiv.
  rewrite -delete_take_drop. f_equiv. rewrite take_drop_middle //.
Qed.

Section interleaving.
  Context `{!invGS_gen HasNoLc Σ} {E : Type → Type} {H : iHandler Σ E}.

  Variant interleavesF
    (interleaves : list (itree (threadpoolE +' E) unit) -> itree (threadpoolE +' E) unit -> itree E unit -> Prop)
    :  list (itree (threadpoolE +' E) unit)
    -> itree' (threadpoolE +' E) unit
    -> itree' E unit
    -> Prop :=
  | Terminate :
    interleavesF interleaves [] (RetF tt) (RetF tt)
  | EndThread tp new_current_tid new_current interleaving' :
    tp !! new_current_tid = Some new_current →
    interleaves (delete new_current_tid tp) new_current interleaving' →
    interleavesF interleaves tp (RetF tt) (TauF interleaving')
  | KillThread tp k new_current_tid new_current interleaving' :
    tp !! new_current_tid = Some new_current →
    interleaves (delete new_current_tid tp) new_current interleaving' →
    interleavesF interleaves tp (VisF (inl1 EKillThread) k) (TauF interleaving')
  | Step current' tp interleaving' :
    interleaves tp current' interleaving' →
    interleavesF interleaves tp (TauF current') (TauF interleaving')
  | Yield tp k new_current_tid new_current interleaving' :
    tp !! new_current_tid = Some new_current →
    interleaves (cons (Tau (k tt)) (delete new_current_tid tp)) new_current interleaving' →
    interleavesF interleaves tp (VisF (inl1 EYield) k) (TauF interleaving')
  | Fork tp k interleaving' :
    interleaves (cons (k NewThread) tp) (k CurrentThread) interleaving' →
    interleavesF interleaves tp (VisF (inl1 EFork) k) (TauF interleaving').
  Hint Constructors interleavesF : iris_itree.
  Definition interleaves_
    (interleaves : list (itree (threadpoolE +' E) unit) -> itree (threadpoolE +' E) unit -> itree E unit -> Prop)
    :  list (itree (threadpoolE +' E) unit)
    -> itree (threadpoolE +' E) unit
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
    list (itree (threadpoolE +' E) unit) -> itree (threadpoolE +' E) unit -> itree E unit -> Prop :=
    paco3 interleaves_ bot3.

  Theorem wpi_interleaving'
    (tp : list (itree (threadpoolE +' E) unit))
    (current : itree (threadpoolE +' E) unit)
    (interleaving : itree E unit) :
    interleaves tp current interleaving →
    ([∗ list] thread ∈ tp, WPi thread @ threadpoolH ⊕ H; ⊤ {{ _, True }}) -∗
    WPi current @ threadpoolH ⊕ H; ∅ {{ _, |={∅, ⊤}=> True }} -∗
    WPi interleaving @ H; ∅ {{ _, |={∅, ⊤}=> True }}.
  Proof.
    iIntros "%Hinter Htp Hcurrent".
    iLöb as "IH" forall (tp current interleaving Hinter). punfold Hinter.
    inversion Hinter as
      [Heqtp Heqcurrent Heqinterleaving
      |tp' new_current_tid new_current interleaving' Hidx Hinter' Heqtp Heqcurrent Heqinterleaving
      |tp' k new_current_tid new_current interleaving' Hidx Hinter' Heqtp Heqcurrent Heqinterleaving
      |current' tp' interleaving' Hinter' Heqtp Heqcurrent Heqinterleaving
      |tp' k new_current_tid new_current interleaving' Hidx Hinter' Heqtp Heqcurrent Heqinterleaving
      |tp' k interleaving' Hinter' Heqtp Heqcurrent Heqinterleaving
      ].
    - apply ret_observe_eqit in Heqcurrent as <-. apply ret_observe_eqit in Heqinterleaving as <-.
      by rewrite -!wpi_ret'.
    - apply ret_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      iApply wpi_tau. iNext.
      iDestruct (big_sepL_delete' _ _ _ new_current_tid with "Htp") as "[Hcurrent' Htp']"; first done.
      destruct Hinter' as [Hinter'|]; last contradiction. iApply ("IH" with "[] [Htp']").
      * done.
      * done.
      * rewrite -wpi_ret'. iMod "Hcurrent". iMod "Hcurrent".
        iDestruct (wpi_clear_mask with "Hcurrent'") as "Hcurrent'". by do 2 iMod "Hcurrent'".
    - apply vis_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      rewrite -wpi_vis'. simpl. iApply wpi_tau. iNext.
      iDestruct (big_sepL_delete' _ _ _ new_current_tid with "Htp") as "[Hcurrent' Htp']"; first done.
      destruct Hinter' as [Hinter'|]; last contradiction.
      iApply ("IH" with "[] [Htp']").
      * done.
      * done.
      * iMod "Hcurrent". simpl. iMod "Hcurrent".
        iDestruct (wpi_clear_mask with "Hcurrent'") as "Hcurrent'". by do 2 iMod "Hcurrent'".
    - apply tau_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      rewrite -!wpi_tau'. iMod (fupd_mask_subseteq ∅) as "Hfupd"; first done. iMod "Hcurrent".
      iModIntro. iNext. iMod "Hfupd".
      iEval (rewrite wpi_update_post). iApply ("IH" with "[] [Htp]").
      * by destruct Hinter'.
      * done.
      * rewrite !wpi_update_post //.
    - apply vis_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      iApply wpi_tau'. rewrite -wpi_vis'. simpl. do 2 iMod "Hcurrent".
      rewrite wpi_update_post wpi_tau'.
      iDestruct (big_sepL_delete' _ _ _ new_current_tid with "Htp") as "[Hcurrent' Htp']"; first done.
      iMod (fupd_mask_subseteq ∅) as "Hfupd"; first done. iModIntro. iNext.
      iApply wpi_update_post. iApply ("IH" with "[] [Hcurrent Htp']").
      * by destruct Hinter'.
      * iApply big_sepL_cons.
        iSplitL "Hcurrent".
        + iMod (fupd_mask_subseteq ∅) as "Hfupd"; first done. by iMod "Hfupd".
        + done.
      * iDestruct (wpi_clear_mask with "Hcurrent'") as "Hcurrent'".
        iApply wpi_update. by iMod "Hfupd".
    - apply vis_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      iApply wpi_tau'. rewrite -wpi_vis'. simpl. iMod "Hcurrent" as "[Hforked Hcurrent']".
      iModIntro. iNext. iApply wpi_update_post. iApply ("IH" with "[] [Hcurrent' Htp]").
      * by destruct Hinter'.
      * iApply big_sepL_cons. iFrame. iApply wpi_wand; last done. by iIntros (?) "?".
      * rewrite wpi_update_post //.
  Qed.
  Corollary wpi_interleaving
    (concurrent : itree (threadpoolE +' E) unit)
    (interleaving : itree E unit) :
    interleaves [] concurrent interleaving →
    WPi concurrent @ threadpoolH ⊕ H; ⊤ {{ _, True }} -∗
    WPi interleaving @ H; ⊤ {{ _, True }}.
  Proof.
    iIntros "%Hinter Hwp". iApply wpi_clear_mask.
    iMod (fupd_mask_subseteq ∅) as "Hfupd"; first done. iModIntro.
    iApply (wpi_interleaving' []).
    - done.
    - by iApply big_sepL_nil.
    - iDestruct (wpi_clear_mask with "Hwp") as "Hwp". iApply wpi_update. by iMod "Hfupd".
  Qed.
End interleaving.
