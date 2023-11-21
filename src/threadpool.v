From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Import fixpoint.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From ITree Require Import ITree.
From ITree Require Import Eq.
From stdpp Require Import list.
From Paco Require Import paco.
From Paco Require Import paco3.

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

(** [iHandler] for [threadpoolE]. *)
Program Definition threadpoolH {Σ} `{!invGS_gen hlc Σ} : iHandler Σ threadpoolE :=
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
  iIntros (?????????) "HΦwand #Hswand". destruct e.
  - iIntros "[HΦ Hs]". iSplitL "HΦwand HΦ".
    * by iApply "HΦwand".
    * by iApply "Hswand".
  - iIntros "HΦ". by iApply "HΦwand".
  - by iIntros "?".
Qed.

Section wp_threadpool.
  Context `{!invGS_gen hlc Σ} {E : Type → Type} {H : iHandler Σ E}.
  Context `{threadpoolE -< E} `{inH Σ threadpoolE E threadpoolH H}.

  Lemma wpi_fork {R} (k : thread → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    WPi (k CurrentThread) @ H; M {{ Φ }} ∗ WPi (k NewThread) @ H; ⊤ {{ _, False }} -∗
    WPi (vis EFork k) @ H; M {{ Φ }}.
  Proof.
    iIntros "[Hwpcur Hwpnew]". iApply wpi_vis.
    rewrite /threadpoolH. iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply is_inH. simpl. iSplitL "Hwpcur Hfupd".
    - rewrite -wpi_clear_mask. iApply wpi_update. iMod "Hfupd". iMod "Hwpcur". by iModIntro.
    - done.
  Qed.

  (** Note here crucially that the mask has to be full for the rule to apply.
  This means that you cannot step over an [EYield] if there are open
  invariants. It amounts to the typical requirement of atomicity in the
  invariant opening rule known from "normal Iris". *)
  Lemma wpi_yield {R} (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    WPi (k tt) @ H; ⊤ {{ Φ }} -∗
    WPi (vis EYield k) @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis. iApply is_inH. simpl.
    iApply fupd_mask_intro_subseteq; first done.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    rewrite -wpi_clear_mask. iApply wpi_update. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_kill {R} (k : Empty_set → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    ⊢ WPi (vis EKillThread k) @ H; ⊤ {{ Φ }}.
  Proof.
    iApply wpi_vis. iApply is_inH. simpl.
    by iApply fupd_mask_intro_subseteq; first done.
  Qed.
End wp_threadpool.

Section interleaving.
  Context `{!invGS_gen hlc Σ} {E : Type → Type} {H : iHandler Σ E} {R : Type}.
  (** This sequentiality assumption is used for the [Emit] case in the adequacy
  proof below. *)
  Context `{!Sequential H}.

  (** The interleaving relation, prior to taking the fixpoint. This relation
  encodes what it means for an [itree E R] to refine an itree
  [itree (threadpoolE +' E) R] that can emit events [threadpoolE] regarding
  concurrency. *)
  Variant interleavesF
    (interleaves : list (itree (threadpoolE +' E) R) → itree (threadpoolE +' E) R → itree E R → Prop)
    : list (itree (threadpoolE +' E) R)
    → itree' (threadpoolE +' E) R
    → itree' E R
    → Prop :=
  (** If a thread returns, the interleaved [itree] ends. *)
  | Return tp r :
    interleavesF interleaves tp (RetF r) (RetF r)
  (** If the current thread steps, so does the interleaved [itree]. *)
  | Step current' tp interleaving' :
    interleaves tp current' interleaving' →
    interleavesF interleaves tp (TauF current') (TauF interleaving')
  (** If an event of type [E] is emitted, the interleaved [itree] also
  emits this event. *)
  | Emit tp A (e : E A) k k' :
    (∀ a, interleaves tp (k a) (k' a)) →
    interleavesF interleaves tp (VisF (inr1 e) k) (VisF e k')
  (** If a thread emits the [EKillThread] event, the thread ends and control is
  yielded to some other thread in the threadpool. The interleaved [itree] takes
  a silent step in place of the [EKillThread]. *)
  | KillThread tp k new_current_tid new_current interleaving' :
    tp !! new_current_tid = Some new_current →
    interleaves (delete new_current_tid tp) new_current interleaving' →
    interleavesF interleaves tp (VisF (inl1 EKillThread) k) (TauF interleaving')
  (** The [EYield] event yields control to another thread placing the current
  thread in the threadpool to be resumed. Resumption costs a step. The
  interleaved [itree] takes a silent step in place of the [EYield]. *)
  | Yield tp k new_current_tid new_current interleaving' :
    tp !! new_current_tid = Some new_current →
    interleaves (cons (Tau (k tt)) (delete new_current_tid tp)) new_current interleaving' →
    interleavesF interleaves tp (VisF (inl1 EYield) k) (TauF interleaving')
  (** The [EYield] event yields control to the current thread, thus effectively
  just doing a silent step. *)
  | YieldSelf tp k interleaving' :
    interleaves tp (k tt) interleaving' →
    interleavesF interleaves tp (VisF (inl1 EYield) k) (TauF interleaving')
  (** The [EFork] event adds a new thread to the threadpool and continues
  executing the current thread. The interleaved [itree] takes a silent step in
  place of the [EFork]. *)
  | Fork tp k interleaving' :
    interleaves (cons (k NewThread) tp) (k CurrentThread) interleaving' →
    interleavesF interleaves tp (VisF (inl1 EFork) k) (TauF interleaving').
  Hint Constructors interleavesF : iris_itree.
  Definition interleaves_
    (interleaves : list (itree (threadpoolE +' E) R) → itree (threadpoolE +' E) R → itree E R → Prop)
    : list (itree (threadpoolE +' E) R)
    → itree (threadpoolE +' E) R
    → itree E R
    → Prop :=
    λ tp current interleaving, interleavesF interleaves tp (observe current) (observe interleaving).

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

  (** The interleaving relation. (See comments above.) *)
  Definition interleaves :
    list (itree (threadpoolE +' E) R) → itree (threadpoolE +' E) R → itree E R → Prop :=
    paco3 interleaves_ bot3.
End interleaving.

(* To prove adequacy for the threadpool handler, we need an induction principle
for an entire threadpool as opposed to for a weakest precondition of a
single thread. Therefore, it is necessary to define a weakest precondition for
threadpools. However, this is only a necessity for the proof. It does not
affect the statement of adequacy. *)
Section wptp.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.

  (** An intermediate definition to placate Coq's dependent pattern matching mechanism. *)
  Definition handle_threadpoolE
    (t : itree (threadpoolE +' E) R)
    (tp : list (itree (threadpoolE +' E) R))
    (Φ : leibnizO R -> iPropO Σ)
    (wptp : leibnizO (itree (threadpoolE +' E) R) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (leibnizO R -> iPropO Σ) -> iPropO Σ)
    (A : Type)
    (e : threadpoolE A)
    : (A → itree (threadpoolE +' E) R) → iProp Σ :=
    (** Trick: To have Coq not complain about dependent types, it is important
    to introduce the dependently typed binders sufficiently late. This is why
    we put a lambda after each arm, as opposed to on the outside. *)
    match e with
    | EKillThread => λ k,
      |={∅, ⊤}=> |={⊤, ∅}=>
      ( ∀ new_current_tid new_current,
        ⌜tp !! new_current_tid = Some new_current⌝ →
        wptp new_current (delete new_current_tid tp) Φ
      )
    | EYield => λ k,
      |={∅, ⊤}=> |={⊤, ∅}=>
      ( ∀ new_current_tid new_current,
          ⌜tp !! new_current_tid = Some new_current⌝ →
          wptp new_current (cons (Tau (k tt)) (delete new_current_tid tp)) Φ
      ∨ wptp (k tt) tp Φ
      )
    | EFork => λ k,
      wptp (k CurrentThread) (cons (k NewThread) tp) Φ
    end%I.
  (** The definition of the weakest precondition, prior to taking the fixpoint. *)
  (* TODO: Uncurry this, and don't use the -n> to iProp *)
  Definition wptpF (H : iHandler Σ E)
    (wptp : leibnizO (itree (threadpoolE +' E) R) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (R -d> iPropO Σ) -> iPropO Σ) :
            leibnizO (itree (threadpoolE +' E) R) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (R -d> iPropO Σ) -> iPropO Σ :=
    λ t tp Φ,
      (|={∅}=>
        match observe t with
        | RetF r  => |={∅, ⊤}=> Φ r
        | TauF t' => wptp t' tp Φ
        | @VisF _ _ _  A (inl1 e) k => handle_threadpoolE t tp Φ wptp A e k
        | VisF (inr1 e) k => H _ e
            (λ a, wptp (k a) tp Φ)
            (λ a, |={⊤, ∅}=> wptp (k a) tp (λ _, False))
        end
      )%I.
  Definition wptpF' (H : iHandler Σ E)
    (wptp : leibnizO (itree (threadpoolE +' E) R) * leibnizO (list (itree (threadpoolE +' E) R)) * (R -d> iPropO Σ) -> iPropO Σ) :
            leibnizO (itree (threadpoolE +' E) R) * leibnizO (list (itree (threadpoolE +' E) R)) * (R -d> iPropO Σ) -> iPropO Σ :=
    λ pair, match pair with (t, tp, Φ) => wptpF H (curry3 wptp) t tp Φ end.

  Global Instance wptpF_ne n H :
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) (wptpF' H).
  Proof.
    intros wp1 wp2 Hwp [[t1 tp1] Q1] [[t2 tp2] Q2] [[Ht Htp] HQ]. simpl in Ht, Htp, HQ.
    rewrite /wptpF'/wptpF. destruct Ht, Htp. do 2 f_equiv. do 2 f_equiv.
    - rewrite /curry3. by apply Hwp.
    - destruct e as [e'|e'].
      * rewrite /handle_threadpoolE. destruct e'.
        + by apply Hwp.
        + repeat f_equiv; eauto.
        + do 3 f_equiv. intros new_current_tid. f_equiv. intros new_current. f_equiv.
          rewrite /curry3. by apply Hwp.
      * apply handler_ne.
        + intros a. by apply Hwp.
        + intros a. f_equiv. by apply Hwp.
  Qed.

  Lemma wptpF_mono H wptp1 wptp2:
    ⊢ □ (∀ t tp Φ, wptp1 t tp Φ -∗ wptp2 t tp Φ)
    → ∀ t tp Φ, wptpF H wptp1 t tp Φ -∗ wptpF H wptp2 t tp Φ.
  Proof.
    iIntros "#Hwand" (t tp Φ) "Hwp". rewrite /wptpF. destruct (observe t).
    - done.
    - by iApply "Hwand".
    - rewrite /handle_threadpoolE. destruct e as [e|e].
      * destruct e.
        + by iApply "Hwand".
        + iModIntro. iMod "Hwp". iMod "Hwp". iModIntro. iMod "Hwp". iModIntro.
          iIntros (new_current_tid new_current Hidx).
          iDestruct ("Hwp" $! new_current_tid new_current Hidx) as "[Hwp|Hwp]".
          ++ iLeft. by iApply "Hwand".
          ++ iRight. by iApply "Hwand".
        + iMod "Hwp". iModIntro. iMod "Hwp". iModIntro. iMod "Hwp". iModIntro.
          iIntros (new_current_tid new_current Hidx). iApply "Hwand". by iApply "Hwp".
      * iMod "Hwp". iModIntro. iApply ihandler_mono.
        + eauto.
        + eauto.
        + iApply ihandler_mono; last done.
          ++ iIntros (a) "Hwp". by iApply "Hwand".
          ++ iModIntro. iIntros (a) "Hwp". iMod "Hwp". iModIntro. by iApply "Hwand".
  Qed.
  Lemma wptpF_mono' H wp1 wp2:
    ⊢ □ (∀ t tp Φ, wp1 (t, tp, Φ) -∗ wp2 (t, tp, Φ))
    → ∀ t tp Φ, wptpF' H wp1 (t, tp, Φ) -∗ wptpF' H wp2 (t, tp, Φ).
  Proof.
    iApply wptpF_mono.
  Qed.

  Global Instance wp_itree_pre_monotone H :
    BiMonoPred (λ wp_itree, wptpF' H wp_itree).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([[??]?]) "Hsim" => /=. iApply wptpF_mono'; [|done].
      iModIntro. iIntros (t tp Φ) "HΠ". by iApply "Hinner".
    - intros wpi HneΦ n [t Φ] [t' Φ'] [-> HΦ]. f_equiv. simpl. by f_equiv.
  Qed.

  (* TODO: Rename [wpi] to [wpi_no_mask] or something along those lines. *)
  Definition wptp (H : iHandler Σ E) (t : itree (threadpoolE +' E) R) (tp : list (itree (threadpoolE +' E) R)) (Φ : R -> iPropO Σ) : iProp Σ :=
    bi_least_fixpoint (wptpF' H) ((t, tp), Φ).

  Lemma wptp_unfold H t tp Φ :
    wptp H t tp Φ ⊣⊢ wptpF H (wptp H) t tp Φ.
  Proof.
    apply: least_fixpoint_unfold.
  Qed.
End wptp.

Section wptp_induction.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ} {H : iHandler Σ E}.

  Lemma wptp_ind (G : leibnizO (itree (threadpoolE +' E) R) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (R -d> iPropO Σ) -> iPropO Σ):
    NonExpansive3 G →
    (□ ∀ t tp Φ, wptpF H (λ t' tp' Ψ, G t' tp' Ψ ∧ wptp H t' tp' Ψ) t tp Φ -∗ G t tp Φ) -∗
    ∀ t tp Φ, wptp H t tp Φ -∗ G t tp Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (t tp Φ) "Hwptp".
    rewrite {2}/wptp.
    unshelve iApply (least_fixpoint_ind _ (uncurry3 G) with "[] Hwptp").
    iIntros "!>" ([[??]?]) "Hwp" => /=. by iApply "HPre".
  Qed.

  Lemma wptp_iter (G : leibnizO (itree (threadpoolE +' E) R) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (R -d> iPropO Σ) -> iPropO Σ) :
    NonExpansive3 G →
    (□ ∀ t tp Φ, wptpF H G t tp Φ -∗ G t tp Φ) -∗
    ∀ t tp Φ, wptp H t tp Φ -∗ G t tp Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply wptp_ind. iIntros "!>" (t tp Φ) "Hwptp".
    iApply "HPre". iApply (wptpF_mono with "[] Hwptp").
    iIntros "!>" (???) "[? _]". by iFrame.
  Qed.

  Lemma wptp_iter' (G : leibnizO (itree (threadpoolE +' E) R) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (R -d> iPropO Σ) -> iPropO Σ):
    NonExpansive3 G →
    (□ ∀ Φ tp r, (|={∅,⊤}=> Φ r) -∗ G (Ret r) tp Φ) -∗
    (□ ∀ Φ tp t, (|={∅}=> G t tp Φ) -∗ G (Tau t) tp Φ) -∗
    (□ ∀ Φ tp k,
      (|={∅, ⊤}=> |={⊤, ∅}=> ∀ new_current_tid new_current,
        ⌜tp !! new_current_tid = Some new_current⌝ →
        G new_current (delete new_current_tid tp) Φ) -∗
      G (Vis (inl1 EKillThread) k) tp Φ
    ) -∗
    (□ ∀ Φ k tp,
      (|={∅, ⊤}=> |={⊤, ∅}=>
        (∀ new_current_tid new_current,
            ⌜tp !! new_current_tid = Some new_current⌝ →
            G new_current (cons (Tau (k tt)) (delete new_current_tid tp)) Φ
        ∨ G (k tt) tp Φ
        )) -∗
      G (Vis (inl1 EYield) k) tp Φ
    ) -∗
    (□ ∀ Φ k tp,
      (|={∅}=> G (k CurrentThread) (cons (k NewThread) tp) Φ) -∗
      G (Vis (inl1 EFork) k) tp Φ
    ) -∗
    (□ ∀ Φ A (e : E A) k tp,
      (|={∅}=> H _ e (λ a, G (k a) tp Φ) (λ a, |={⊤, ∅}=> G (k a) tp (λ _, False))) -∗
      G (Vis (inr1 e) k) tp Φ
    ) -∗
    ∀ t tp Φ, wptp H t tp Φ -∗ G t tp Φ.
  Proof.
    iIntros "%Hne #HRet #HTau #HKillThread #HYield #HFork #HVis". iApply (wptp_iter G). iModIntro.
    iIntros (t tp). destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - iIntros (Φ) "HΦ". iApply "HRet". rewrite /wptpF /=. by iMod "HΦ".
    - iIntros (Φ) "Hwp". iApply "HTau". rewrite /wptpF //.
    - iIntros (Φ) "Hwp". destruct e as [e|e]; rewrite /wptpF /=.
      * destruct e.
        + by iApply "HFork".
        + iApply "HYield". by iMod "Hwp".
        + iApply "HKillThread". iMod "Hwp". iMod "Hwp". iModIntro. iMod "Hwp". iModIntro.
          iIntros (new_current_tid new_current Hidx). by iApply "Hwp".
      * by iApply "HVis".
  Qed.

  Lemma wptp_inversion (t : itree (threadpoolE +' E) R) tp Φ G :
    wptpF H G t tp Φ -∗
    ( (∃ r, ⌜t ≅ Ret r⌝ ∧ (|={∅,⊤}=> Φ r))
    ∨ (∃ t', ⌜t ≅ Tau t'⌝ ∧ |={∅}=> G t' tp Φ)
    ∨ (∃ k, ⌜t ≅ Vis (inl1 EFork) k⌝ ∧
      |={∅}=> G (k CurrentThread) (cons (k NewThread) tp) Φ
      )
    ∨ (∃ k, ⌜t ≅ Vis (inl1 EYield) k⌝ ∧ (
      |={∅, ⊤}=> |={⊤, ∅}=>
        (∀ new_current_tid new_current,
            ⌜tp !! new_current_tid = Some new_current⌝ →
            G new_current (cons (Tau (k tt)) (delete new_current_tid tp)) Φ
        ∨ G (k tt) tp Φ
        )
      ))
    ∨ (∃ k, ⌜t ≅ Vis (inl1 EKillThread) k⌝ ∧ (
      |={∅, ⊤}=> |={⊤, ∅}=> ∀ new_current_tid new_current,
        ⌜tp !! new_current_tid = Some new_current⌝ →
        G new_current (delete new_current_tid tp) Φ
      ))
    ∨ (∃ A (e : E A) k, ⌜t ≅ Vis (inr1 e) k⌝ ∧
      |={∅}=> H _ e (λ a, G (k a) tp Φ) (λ a, |={⊤, ∅}=> G (k a) tp (λ _, False))
      )
    ).
  Proof.
    iIntros "Hwptp".
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - iLeft. iExists r. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
    - iRight. iLeft. iExists t'. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
    - destruct e as [e|e].
      * destruct e.
        + iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
        + iRight. iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=.
          by iMod "Hwptp".
        + iRight. iRight. iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=.
          iMod "Hwptp". iMod "Hwptp". iModIntro. iMod "Hwptp". iModIntro.
          iIntros (new_current_tid new_current Hidx). by iApply "Hwptp".
      * iRight. iRight. iRight. iRight. iRight. iExists _, e, k. iSplit; first done.
        rewrite /wptpF /= //.
  Qed.
End wptp_induction.

Section wptp_proper.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ} {H : iHandler Σ E}.

  (* TODO: Don't use instances for temporary class definitions. *)
  Global Instance wptp_proper_unidirectional :
    Proper (eqit (=) false false ==> Forall2 (eqit (=) false false) ==> (=) ==> (⊢)) (wptp (R:=R) H).
  Proof.
    iIntros (t1 t2 Ht tp1 tp2 Htp Φ Φ' <-).
    epose (G := λ (t1 : leibnizO (itree (threadpoolE +' E) R)) (tp1 : leibnizO (list (itree (threadpoolE +' E) R))) (Φ : leibnizO R -d> iPropO Σ),
      (∀ t2 tp2, ⌜t1 ≅ t2⌝ → ⌜Forall2 (eqit (=) false false) tp1 tp2⌝ → wptp H t2 tp2 Φ)%I).
    iAssert (∀ t tp Φ, wptp H t tp Φ -∗ G t tp Φ)%I as "Hgen"; last first.
    { iIntros "Hwptp". by iApply ("Hgen" with "Hwptp"). }
    iApply (wptp_iter G); clear.
    { intros n t1 t2 <- tp1 tp2 <- Φ1 Φ2 HΦ. rewrite /G. do 3 f_equiv.
      do 3 f_equiv. rewrite /wptp. by apply least_fixpoint_ne.
    }
    iModIntro. iIntros (t1 tp1 Φ) "Hwptp". iIntros (t2 tp2 Ht Htp). rewrite wptp_unfold /wptpF.
    punfold Ht. unfold eqit_ in Ht. remember (observe t1) as ot1. remember (observe t2) as ot2.
    destruct Ht.
    - by subst.
    - rewrite /G. iMod "Hwptp". iModIntro. iApply "Hwptp". iPureIntro. pclearbot. apply REL. done.
    - iMod "Hwptp". iModIntro. destruct e as [e|e].
      * destruct e.
        + simpl. rewrite /G. iApply "Hwptp". { iPureIntro. pclearbot. apply REL. }
          iPureIntro. constructor; eauto. pclearbot. apply REL.
        + simpl. iMod "Hwptp". iModIntro. iMod "Hwptp". iModIntro.
          iIntros (new_current_tid new_current2 Hidx2).
          apply Forall2_lookup_l with (P := eqit eq false false) (k := tp1) in Hidx2 as (new_current1&Hidx1&Hnew_current); last done.
          iDestruct ("Hwptp" $! new_current_tid new_current1 Hidx1) as "[Hwptp|Hwptp]".
          ++ iLeft. iApply "Hwptp"; first eauto. iPureIntro. constructor.
             +++ f_equiv. f_equiv. pclearbot. apply REL.
             +++ apply Forall2_delete. apply Htp.
          ++ iRight. iApply "Hwptp"; last done. iPureIntro. pclearbot. apply REL.
        + simpl. iMod "Hwptp". iModIntro. iMod "Hwptp". iModIntro.
          iIntros (new_current_tid new_current2 Hidx2).
          apply Forall2_lookup_l with (P := eqit eq false false) (k := tp1) in Hidx2 as (new_current1&Hidx1&Hnew_current); last done.
          iApply ("Hwptp" $! new_current_tid new_current1 Hidx1); first done.
          iPureIntro. apply Forall2_delete. apply Htp.
      * iApply ihandler_mono; last done.
        { iIntros (a) "Hwptp". iApply "Hwptp"; last done. pclearbot. iPureIntro. apply REL. }
        iModIntro. iIntros (a) "Hwptp". iMod "Hwptp". iModIntro. iApply "Hwptp"; last done.
        pclearbot. iPureIntro. apply REL.
    - done.
    - done.
  Qed.
  Global Instance wptp_proper :
    Proper (eqit (=) false false ==> Forall2 (eqit (=) false false) ==> (=) ==> (⊣⊢)) (wptp (R:=R) H).
  Proof.
    intros t1 t2 Ht tp1 tp2 Htp Φ1 Φ2 HΦ.
    iSplit.
    - iIntros "Hwp". rewrite Ht Htp HΦ //.
    - iIntros "Hwp". rewrite Ht Htp HΦ //.
  Qed.
End wptp_proper.

Lemma big_sepL_delete' {Σ} A (Φ : A → iProp Σ) l i x :
  l !! i = Some x →
  ([∗ list] y ∈ l, Φ y) ⊣⊢
  Φ x ∗ [∗ list] y ∈ (delete i l), Φ y.
Proof.
  intros Hidx. rewrite -(take_drop_middle l i x) // !big_sepL_app.
  rewrite assoc -!(comm _ (Φ _)) -assoc -big_sepL_app. do 2 f_equiv.
  rewrite -delete_take_drop. f_equiv. rewrite take_drop_middle //.
Qed.

Section threadpool_adequacy.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context {H : iHandler Σ E}.

  Lemma wp_wptp (t t' : itree (threadpoolE +' E) R) tp Φ :
    WPi t' @ threadpoolH ⊕ H; ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    wptp H t tp Φ -∗
    wptp H t (t' :: tp) Φ.
  Proof.
    epose (G := (λ (t : leibnizO (itree (threadpoolE +' E) R)) (tp : leibnizO (list (itree (threadpoolE +' E) R))) (Φ : leibnizO R -d> iPropO Σ),
      wptp H t tp Φ ∧ ∀ t', WPi t' @ threadpoolH ⊕ H; ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗ wptp H t (t' :: tp) Φ
      )%I).
    iAssert (∀ t tp Φ, wptp H t tp Φ -∗ G t tp Φ)%I as "Hgen"; last first.
    { iIntros "Hwp Hwptp". iApply ("Hgen" with "Hwptp"); eauto. }
    iApply (wptp_iter' (H := H) G); clear.
    - intros n t1 t2 <- tp1 tp2 <- Φ1 Φ2 HΦ. rewrite /G.
      apply bi.and_ne. { rewrite /wptp. by apply least_fixpoint_ne. } do 3 f_equiv.
      * by do 3 f_equiv.
      * apply least_fixpoint_ne; last done. reflexivity.
    - iModIntro. iIntros (Φ tp r) "HΦ". iSplit; iIntros; rewrite wptp_unfold /wptpF //.
    - iModIntro. iIntros (Φ tp t) "HG". iSplit.
      { rewrite wptp_unfold /wptpF /=. iMod "HG". by iDestruct "HG" as "[Hwptp _]". }
      iIntros (t') "Hwp". rewrite wptp_unfold /wptpF /=. iMod "HG". iDestruct "HG" as "[_ Hwptp]".
      by iApply "Hwptp".
    - iModIntro. iIntros (Φ tp k) "HG". iSplit.
      { rewrite wptp_unfold /wptpF /=. iModIntro. iMod "HG". iModIntro. iMod "HG". iModIntro.
        iIntros (new_current_tid new_current Hidx). by iDestruct ("HG" $! _ _ Hidx) as "[Hwptp _]".
      }
      iIntros (t') "Hwp". rewrite wptp_unfold /wptpF /=.
      iModIntro. iMod "HG". iModIntro. iMod "HG". iModIntro.
      iIntros (new_current_tid new_current Hidx).
      destruct new_current_tid as [|new_current_tid']; first last.
      * by iApply "HG".
      * simpl. simpl in Hidx. injection Hidx as <-. rename t' into t.
        unshelve epose (G' := (λne (t : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ), ∀ Φ,
          (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
          (∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → G new_current (delete new_current_tid tp) Φ) -∗
           wptp H t tp Φ
          )%I); try apply _; try solve_proper.
        iAssert (∀ t Φ, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ }} -∗ G' t Φ)%I as "Hgen"; last first.
        { iApply ("Hgen" with "Hwp"); eauto. }
        iApply (wpi_iter' (H := threadpoolH ⊕ H) G'); clear.
        + intros n t1 t2 Ht tp1 tp2 <-. rewrite /G'. by do 2 f_equiv.
        + iModIntro. iIntros (Φ r) "HΦ". rewrite /G' /=. iIntros (Φ') "Hfupd HG".
          rewrite wptp_unfold /wptpF /=. by iApply "Hfupd".
        + iModIntro. iIntros (Φ t) "HG'". rewrite /G' /=. iIntros (Φ') "Hfupd HG".
          rewrite wptp_unfold /wptpF /=. iMod "HG'". iModIntro. by iApply ("HG'" with "Hfupd").
        + iModIntro. iIntros (Φ A e k) "HH". rewrite /G' /=. iIntros (Φ') "Hfupd HG".
          destruct e as [e|e]; first destruct e.
          ++ rewrite wptp_unfold /wptpF /=. iMod "HH" as "[Hcurrent Hnew]". iApply "Hcurren"
    iModIntro. iIntros (t tp Φ) "Hwptp".
    iIntros (t') "Hwp".
    iDestruct (wptp_inversion with "Hwptp") as "[(%r&->&HΦ)|[?|[?|[?|[?|?]]]]]".

    unshelve epose (G' := (λne (t' : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ Φ t tp, (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗ wptpF H G t tp Φ -∗ wptp H t (t' :: tp) Φ
      )%I); try apply _; try solve_proper.
    iAssert (∀ t Φ_fupd, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ_fupd }} -∗ G' t Φ_fupd)%I as "Hgen"; last first.
    { iIntros (t') "Hwp". iApply ("Hgen" with "Hwp"); eauto. }
    iApply (wpi_iter (H := threadpoolH ⊕ H) G'); first solve_proper.
    clear. iModIntro. iIntros (t Φ) "Hwp". iIntros (Φ' t' tp) "Hwand Hwptp".
    iDestruct (wptp_inversion with "Hwptp") as "[]".

    unshelve epose (G := (λne (t' : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ Φ t tp, (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗ wptp H t tp Φ -∗ wptp H t (t' :: tp) Φ
      )%I); try apply _; try solve_proper.
    iAssert (∀ t Φ, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { iIntros "Hwp Hwptp". iApply ("Hgen" with "Hwp"); eauto. }
    clear. iApply (wpi_iter (H := threadpoolH ⊕ H) G); first solve_proper.
    iModIntro. iIntros (t' Φfupd) "Hwptp". iIntros (Φ t tp) "Hwand Hwp".
    unshelve epose (G' := (λ (t : leibnizO (itree (threadpoolE +' E) R)) (tp : leibnizO (list (itree (threadpoolE +' E) R))) (Φ : leibnizO R -d> iPropO Σ),
      ∀ t', wpiF (threadpoolH ⊕ H) (λ x : leibnizO (itree (threadpoolE +' E) R), G x) t' Φfupd -∗ wptp H t (t' :: tp) Φ
      )%I).
    iAssert (∀ t tp Φ, wptp H t tp Φ -∗ G' t tp Φ)%I as "Hgen"; last first.
    { by iApply ("Hgen" with "Hwp"). }
    iApply (wptp_iter' (H := H) G'); clear.
    - intros n t1 t2 Ht tp1 tp2 <- Φ1 Φ2 HΦ. rewrite /G'. do 3 f_equiv.
      apply least_fixpoint_ne; last done. reflexivity.
    - iModIntro. iIntros (Φ tp r) "HΦ". rewrite /G'. iIntros (t') "Hwp".
      rewrite wptp_unfold /wptpF. by iModIntro.
    - iModIntro. iIntros (Φ tp t) "HG'". rewrite /G'. iIntros (t') "Hwp".
      rewrite wptp_unfold /wptpF /=. iMod "HG'". iModIntro. by iApply "HG'".
    - iModIntro. iIntros (Φ tp k) "HG'". rewrite /G'. iIntros (t') "Hwp".
      rewrite wptp_unfold /wptpF /=. iModIntro. iIntros (new_current_tid new_current Hidx).
      iApply "HG'".
      iMod ("HG'" $! _ _ Hidx).
    
    clear. iIntros (t tp Φ) "Hwptp". iIntros (t') "Hwp".
    iIntros (Φ t tp) "Hwand Hwptp". rewrite /G /=.
      iEval (rewrite wptp_unfold /wptpF).

  Lemma wp_wptp (t : itree (threadpoolE +' E) R) Φ :
    WPi t @ (threadpoolH ⊕ H); ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    wptp H t [] Φ.
  Proof.
    unshelve epose (G := (λne (t : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ Φ, (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗ wptp H t [] Φ
      )%I); try apply _; try solve_proper.
    iAssert (∀ t Φ, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { iIntros "Hwp". iApply ("Hgen" with "Hwp"). eauto. }
    iApply (wpi_iter' (H := threadpoolH ⊕ H) G); first solve_proper.
    - clear. iModIntro. iIntros (Φfupd r) "HΦfupd". rewrite /G /=. iIntros (Φ) "Hwand".
      rewrite wptp_unfold /wptpF /=. iMod "HΦfupd". iModIntro. by iApply "Hwand".
    - clear. iModIntro. iIntros (Φfupd t) "Hwp". rewrite /G. simpl. iIntros (Φ) "Hwand".
      rewrite wptp_unfold /wptpF /=. iMod "Hwp". iModIntro. iApply "Hwp".
      iIntros (r) "HΦfupd". by iApply "Hwand".
    - clear. iModIntro. iIntros (Φfupd t e k) "HH". iEval (rewrite /G /=). iIntros (Φ) "Hfupd".
      destruct e as [e|e].
      * rewrite wptp_unfold /wptpF /= /handle_threadpoolE /=.
        destruct e.
        + 
    
  (** A technical version of adequacy, amenable to induction. See corollary below for a
  more meaningful statement. *)
  Theorem wpi_interleaving'
    (tp : list (itree (threadpoolE +' E) R))
    (current : itree (threadpoolE +' E) R)
    (interleaving : itree E R)
    (Φ : R → iProp Σ) :
    interleaves tp current interleaving →
    ([∗ list] thread ∈ tp, WPi thread @ threadpoolH ⊕ H; ⊤ {{ Φ }}) -∗
    WPi current @ threadpoolH ⊕ H; ∅ {{ r, |={∅, ⊤}=> Φ r }} -∗
    WPi interleaving @ H; ∅ {{ r, |={∅, ⊤}=> Φ r }}.
  Proof.
    iIntros "%Hinter Htp Hcurrent".
    unshelve epose (G := (λne (current : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ interleaving tp Φ,
        ⌜interleaves tp current interleaving⌝ →
        (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
        ([∗ list] thread ∈ tp, WPi thread @ threadpoolH ⊕ H; ⊤ {{ Φ }}) -∗
        WPi interleaving @ H; ∅ {{ r, |={∅, ⊤}=> Φ r }}
    )%I); try apply _; try solve_proper.
    iAssert (∀ t Φ, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hcurrent [] [] Htp"); eauto. }
    iApply (wpi_iter' (H := threadpoolH ⊕ H) G); first solve_proper.
    - clear. iModIntro. iIntros (Φ r) "HΦ". iIntros (t tp Φfupd Hinter) "HΦfupd Htp".
      punfold Hinter. inversion Hinter. subst. apply ret_observe_eqit in H3 as <-.
      rewrite -wpi_ret'. by iApply "HΦfupd".
    - clear. iModIntro. iIntros (Φ r) "HΦ". iIntros (t tp Φfupd Hinter) "HΦfupd Htp".
      punfold Hinter. inversion Hinter. subst. apply tau_observe_eqit in H2 as <-.
      rewrite -wpi_tau. iApply wpi_update. iMod "HΦ". pclearbot. by iApply ("HΦ" with "[] HΦfupd").
    - clear -Sequential0. iModIntro.
      iIntros (Φfupd A e k) "HH". iIntros (interleaving tp Φ Hinter) "HΦfupd Htp".
      punfold Hinter.
      inversion Hinter; simplify_K; simplify_eq.
      * apply vis_observe_eqit in H5 as <-. rewrite -!wpi_vis'.
        simpl. iMod "HH". iModIntro. iApply is_seq.
        iApply (ihandler_mono with "[HΦfupd Htp] [] [HH //]").
        + iIntros (a) "Hwp". iApply wpi_update_post. pclearbot. iApply ("Hwp" with "[] HΦfupd Htp").
          iPureIntro. apply H2.
        + iModIntro. by iIntros (t) "H".
      * simplify_K. apply tau_observe_eqit in H5 as <-. rewrite -wpi_tau. simpl.
        shelve.
      * simplify_K. apply tau_observe_eqit in H5 as <-. simpl. rewrite -wpi_tau.


    iLöb as "IH" forall (tp current interleaving Hinter Φ). punfold Hinter.
    - (* Return tp' r *)
      apply ret_observe_eqit in Heqcurrent as <-. apply ret_observe_eqit in Heqinterleaving as <-.
      by rewrite -!wpi_ret'.
    - (* Step current' tp' interleaving' *)
      apply tau_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      rewrite -!wpi_tau'. iMod (fupd_mask_subseteq ∅) as "Hfupd"; first done. iMod "Hcurrent".
      iModIntro. iNext. iMod "Hfupd".
      iEval (rewrite wpi_update_post). iApply ("IH" with "[] [Htp]").
      * by destruct Hinter'.
      * done.
      * rewrite !wpi_update_post //.
    - (* Emit tp' A e k k' *)
      apply vis_observe_eqit in Heqcurrent as <-. apply vis_observe_eqit in Heqinterleaving as <-.
      rewrite -!wpi_vis'. iMod (fupd_mask_subseteq ∅) as "Hfupd"; first done. iMod "Hcurrent".
      iApply is_seq. iApply (ihandler_mono with "[Hfupd Htp] [] [Hcurrent //]").
      * pclearbot. iIntros (a) "Hwp". iNext. iMod "Hfupd".
        iEval (rewrite wpi_update_post). iApply ("IH" with "[] Htp").
        + by destruct (Hinter' a).
        + rewrite wpi_update_post //.
      * iModIntro. by iIntros (t) "Hwp".
    - (* KillThread tp' k new_current_tid new_current interleaving' *)
      apply vis_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      rewrite -wpi_vis'. simpl. iApply wpi_tau. iNext.
      iDestruct (big_sepL_delete' _ _ _ new_current_tid with "Htp") as "[Hcurrent' Htp']"; first done.
      pclearbot. iApply ("IH" with "[] [Htp']").
      * done.
      * done.
      * iMod "Hcurrent". simpl. iMod "Hcurrent".
        iDestruct (wpi_clear_mask with "Hcurrent'") as "Hcurrent'". by do 2 iMod "Hcurrent'".
    - (* Yield tp' k new_current_tid new_current interleaving' *)
      apply vis_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
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
    - (* Fork tp' k interleaving' *)
      apply vis_observe_eqit in Heqcurrent as <-. apply tau_observe_eqit in Heqinterleaving as <-.
      iApply wpi_tau'. rewrite -wpi_vis'. simpl. iMod "Hcurrent" as "[Hcurrent' Hforked]".
      iModIntro. iNext. iApply wpi_update_post. iApply ("IH" with "[] [Hforked Htp]").
      * by destruct Hinter'.
      * iApply big_sepL_cons. iFrame. iApply wpi_wand; last done. by iIntros (?) "?".
      * rewrite wpi_update_post //.
  Qed.
  (** Adequacy for [threadpoolH ⊕ H]. This says that if you can prove the
  weakest precondition an [itree (threadpoolE +' E) R] then you get weakest
  preconditions for every interleaving [itree E R]. *)
  Corollary wpi_interleaving
    (concurrent : itree (threadpoolE +' E) R)
    (interleaving : itree E R)
    (Φ : R → iProp Σ) :
    interleaves [] concurrent interleaving →
    WPi concurrent @ threadpoolH ⊕ H; ⊤ {{ Φ }} -∗
    WPi interleaving @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "%Hinter Hwp". iApply wpi_clear_mask.
    iMod (fupd_mask_subseteq ∅) as "Hfupd"; first done. iModIntro.
    iApply (wpi_interleaving' []).
    - done.
    - by iApply big_sepL_nil.
    - iDestruct (wpi_clear_mask with "Hwp") as "Hwp". iApply wpi_update. by iMod "Hfupd".
  Qed.
End interleaving.
