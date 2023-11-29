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
    (tid : nat)
    (t : itree (threadpoolE +' E) R)
    (tp : list (itree (threadpoolE +' E) R))
    (Φ : leibnizO R -> iPropO Σ)
    (wptp : leibnizO (option nat) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (leibnizO R -> iPropO Σ) -> iPropO Σ)
    (A : Type)
    (e : threadpoolE A)
    : (A → itree (threadpoolE +' E) R) → iProp Σ :=
    (** Trick: To have Coq not complain about dependent types, it is important
    to introduce the dependently typed binders sufficiently late. This is why
    we put a lambda after each arm, as opposed to on the outside. *)
    match e with
    | EKillThread => λ k, |={∅, ⊤}=>
      (
      wptp None (delete tid tp) Φ
      ∧ ∀ tid' t', ⌜(delete tid tp) !! tid' = Some t'⌝ → |={⊤, ∅}=> wptp (Some tid') (delete tid tp) Φ
      )
    | EYield => λ k, |={∅, ⊤}=>
      (
      wptp None tp Φ
      ∧ ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={⊤, ∅}=> wptp (Some tid') tp Φ
      )
    | EFork => λ k,
      wptp (Some (tid + 1)) (cons (k NewThread) (<[tid:=k CurrentThread]>tp)) Φ
    end%I.
  (** The definition of the weakest precondition, prior to taking the fixpoint. *)
  (* TODO: Uncurry this, and don't use the -n> to iProp *)
  Definition wptpF (H : iHandler Σ E)
    (wptp : leibnizO (option nat) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (R -d> iPropO Σ) -> iPropO Σ) :
            leibnizO (option nat) -> leibnizO (list (itree (threadpoolE +' E) R)) -> (R -d> iPropO Σ) -> iPropO Σ :=
    λ tid tp Φ, (
      match tid with
      | None => ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={⊤, ∅}=> wptp (Some tid') tp Φ
      | Some tid => ∃ t, ⌜tp !! tid = Some t⌝ ∧ |={∅}=>
        match observe t with
        | RetF r  => |={∅, ⊤}=> Φ r
        | TauF t' => wptp (Some tid) (<[tid := t']>tp) Φ
        | @VisF _ _ _  A (inl1 e) k => handle_threadpoolE tid t tp Φ wptp A e k
        | VisF (inr1 e) k => H _ e
            (λ a, wptp (Some tid) (<[tid:=k a]>tp) Φ)
            (λ a, False)
        end
      end
    )%I.
  Definition wptpF' (H : iHandler Σ E)
    (wptp : leibnizO (option nat) * leibnizO (list (itree (threadpoolE +' E) R)) * (R -d> iPropO Σ) -> iPropO Σ) :
            leibnizO (option nat) * leibnizO (list (itree (threadpoolE +' E) R)) * (R -d> iPropO Σ) -> iPropO Σ :=
    λ pair, match pair with (t, tp, Φ) => wptpF H (curry3 wptp) t tp Φ end.

  Global Instance wptpF_ne n H :
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) (wptpF' H).
  Admitted.
  (*
  Proof.
    intros wp1 wp2 Hwp [[t1 tp1] Q1] [[t2 tp2] Q2] [[Ht Htp] HQ]. simpl in Ht, Htp, HQ.
    rewrite /wptpF'/wptpF. destruct Ht, Htp. do 2 f_equiv. do 2 f_equiv.
    - rewrite /curry3. by apply Hwp.
    - destruct e as [e'|e'].
      * rewrite /handle_threadpoolE. destruct e'.
        + by apply Hwp.
        + repeat f_equiv; eauto.
        + do 4 f_equiv. intros new_current_tid. by do 3 f_equiv.
      * apply handler_ne.
        + intros a. by apply Hwp.
        + intros a. f_equiv. by apply Hwp.
  Qed.
  *)

  Lemma wptpF_mono H wptp1 wptp2:
    ⊢ □ (∀ tid tp Φ, wptp1 tid tp Φ -∗ wptp2 tid tp Φ)
    → ∀ tid tp Φ, wptpF H wptp1 tid tp Φ -∗ wptpF H wptp2 tid tp Φ.
  Admitted.
  (*
  Proof.
    iIntros "#Hwand" (t tp Φ) "Hwp". rewrite /wptpF. destruct (observe t).
    - done.
    - by iApply "Hwand".
    - rewrite /handle_threadpoolE. destruct e as [e|e].
      * destruct e.
        + by iApply "Hwand".
        + iMod "Hwp". iModIntro. iMod "Hwp". iModIntro.
          iSplit.
          ++ iIntros (new_current_tid new_current Hidx).
             iDestruct "Hwp" as "[Hwp _]". iSpecialize ("Hwp" $! new_current_tid new_current Hidx).
             by iApply "Hwand".
          ++ iDestruct "Hwp" as "[_ Hwp]". by iApply "Hwand".
        + iMod "Hwp". iModIntro. iMod "Hwp". iModIntro.
          iIntros (new_current_tid new_current Hidx). iApply "Hwand". by iApply "Hwp".
      * iMod "Hwp". iModIntro. iApply ihandler_mono.
        + eauto.
        + eauto.
        + iApply ihandler_mono; last done.
          ++ iIntros (a) "Hwp". by iApply "Hwand".
          ++ iModIntro. iIntros (a) "Hwp". iMod "Hwp". iModIntro. by iApply "Hwand".
  Qed.
  *)
  Lemma wptpF_mono' H wp1 wp2:
    ⊢ □ (∀ tid tp Φ, wp1 (tid, tp, Φ) -∗ wp2 (tid, tp, Φ))
    → ∀ tid tp Φ, wptpF' H wp1 (tid, tp, Φ) -∗ wptpF' H wp2 (tid, tp, Φ).
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
  Definition wptp (H : iHandler Σ E) (tid : option nat) (tp : list (itree (threadpoolE +' E) R)) (Φ : R -> iPropO Σ) : iProp Σ :=
    bi_least_fixpoint (wptpF' H) ((tid, tp), Φ).

  Lemma wptp_unfold H t tp Φ :
    wptp H t tp Φ ⊣⊢ wptpF H (wptp H) t tp Φ.
  Proof.
    apply: least_fixpoint_unfold.
  Qed.
End wptp.

Section wptp_induction.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ} {H : iHandler Σ E}.

  Lemma wptp_ind (G : option nat -> list (itree (threadpoolE +' E) R) -> (R -d> iPropO Σ) -> iPropO Σ):
    (∀ t tp, NonExpansive (G t tp)) →
    (□ ∀ tid tp Φ, wptpF H (λ tid' tp' Ψ, G tid' tp' Ψ ∧ wptp H tid' tp' Ψ) tid tp Φ -∗ G tid tp Φ) -∗
    ∀ tid tp Φ, wptp H tid tp Φ -∗ G tid tp Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (tid tp Φ) "Hwptp".
    rewrite {2}/wptp.
    unshelve iApply (least_fixpoint_ind _ (λ (x : leibnizO (option nat) * leibnizO (list (itree (threadpoolE +' E) R)) * (R -d> iPropO Σ)), let (xs, Φ) := x in let (tid, tp) := xs in G tid tp Φ) with "[] Hwptp").
    { intros n [[t1 tp1] Φ1] [[t2 tp2] Φ2] [[<- <-] HΦ]. by f_equiv. }
    iIntros "!>" ([[??]?]) "Hwp" => /=. by iApply "HPre".
  Qed.

  Lemma wptp_iter (G : option nat -> list (itree (threadpoolE +' E) R) -> (R -d> iPropO Σ) -> iPropO Σ) :
    (∀ tid tp, NonExpansive (G tid tp)) →
    (□ ∀ tid tp Φ, wptpF H G tid tp Φ -∗ G tid tp Φ) -∗
    ∀ tid tp Φ, wptp H tid tp Φ -∗ G tid tp Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply wptp_ind. iIntros "!>" (t tp Φ) "Hwptp".
    iApply "HPre". iApply (wptpF_mono with "[] Hwptp").
    iIntros "!>" (???) "[? _]". by iFrame.
  Qed.

  (*
  Lemma wptp_iter' (G : itree (threadpoolE +' E) R -> list (itree (threadpoolE +' E) R) -> (R -d> iPropO Σ) -> iPropO Σ):
    (∀ t tp, NonExpansive (G t tp)) →
    (□ ∀ Φ tp r, (|={∅,⊤}=> Φ r) -∗ G (Ret r) tp Φ) -∗
    (□ ∀ Φ tp t, (|={∅}=> G t tp Φ) -∗ G (Tau t) tp Φ) -∗
    (□ ∀ Φ tp k,
      (|={∅, ⊤}=> ∀ new_current_tid new_current,
        ⌜tp !! new_current_tid = Some new_current⌝ →
        |={⊤, ∅}=> G new_current (delete new_current_tid tp) Φ) -∗
      G (Vis (inl1 EKillThread) k) tp Φ
    ) -∗
    (□ ∀ Φ k tp,
      (|={∅, ⊤}=> (
        (∀ new_current_tid new_current,
            ⌜tp !! new_current_tid = Some new_current⌝ →
            |={⊤, ∅}=> G new_current (cons (k tt) (delete new_current_tid tp)) Φ
        ) ∧ |={⊤, ∅}=> G (k tt) tp Φ
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
        + iApply "HYield". iMod "Hwp". iMod "Hwp". iModIntro. iSplit.
          ++ iIntros (???). by iApply "Hwp".
          ++ iDestruct "Hwp" as "[_ $]".
        + iApply "HKillThread". iMod "Hwp". iMod "Hwp". iModIntro. iIntros (???). by iApply "Hwp".
      * by iApply "HVis".
  Qed.
  *)

  (* TODO: Commit to the extensionality axiom in [itree.v] and remove
     unnecessary [Proper] proofs, and use equality throughout. *)
  Lemma wptp_inversion tid (tp : list (itree (threadpoolE +' E) R)) Φ G :
    wptpF H G (Some tid) tp Φ -∗
    ( (∃ r, ⌜tp !! tid = Some (Ret r)⌝ ∧ (|={∅,⊤}=> Φ r))
    ∨ (∃ t', ⌜tp !! tid = Some (Tau t')⌝ ∧ |={∅}=> G (Some tid) (<[tid:=t']>tp) Φ)
    ∨ (∃ k, ⌜tp !! tid = Some (Vis (inl1 EFork) k)⌝ ∧
      |={∅}=> G (Some (tid + 1)) (cons (k NewThread) (<[tid:=k CurrentThread]>tp)) Φ
      )
    ∨ (∃ k, ⌜tp !! tid = Some (Vis (inl1 EYield) k)⌝ ∧ |={∅, ⊤}=> (
      G None tp Φ
      ∧ ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={⊤, ∅}=> G (Some tid') tp Φ
      ))
    ∨ (∃ k, ⌜tp !! tid = Some (Vis (inl1 EKillThread) k)⌝ ∧ |={∅, ⊤}=> (
      G None (delete tid tp) Φ
      ∧ ∀ tid' t', ⌜(delete tid tp) !! tid' = Some t'⌝ → |={⊤, ∅}=> G (Some tid') (delete tid tp) Φ
      ))
    ∨ (∃ A (e : E A) k, ⌜tp !! tid = Some (Vis (inr1 e) k)⌝ ∧
      |={∅}=> H _ e (λ a, G (Some tid) (<[tid:=k a]>tp) Φ) (λ a, False)
      )
    ).
  Admitted.
  (*
  Proof.
    iIntros "Hwptp".
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - iLeft. iExists r. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
    - iRight. iLeft. iExists t'. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
    - destruct e as [e|e].
      * destruct e.
        + iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
        + iRight. iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=.
          iMod "Hwptp". iMod "Hwptp". iModIntro.
          iSplit.
          ++ iIntros (???). by iApply "Hwptp".
          ++ iDestruct "Hwptp" as "[_ $]".
        + iRight. iRight. iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=.
          iMod "Hwptp". iMod "Hwptp". iModIntro. iIntros (???). by iApply "Hwptp".
      * iRight. iRight. iRight. iRight. iRight. iExists _, e, k. iSplit; first done.
        rewrite /wptpF /= //.
  Qed.
  *)
End wptp_induction.

(*
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
    { intros t tp n Φ1 Φ2 HΦ. rewrite /G. do 3 f_equiv.
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
          iSplit.
          ++ iIntros (new_current_tid new_current2 Hidx2).
             apply Forall2_lookup_l with (P := eqit eq false false) (k := tp1) in Hidx2 as (new_current1&Hidx1&Hnew_current); last done.
             iDestruct "Hwptp" as "[Hwptp _]".
             iSpecialize ("Hwptp" $! new_current_tid new_current1 Hidx1).
             +++ iApply "Hwptp"; first eauto. iPureIntro. constructor.
                 ++++ pclearbot. apply REL.
                 ++++ apply Forall2_delete. apply Htp.
          ++ iDestruct "Hwptp" as "[_ Hwptp]". iApply "Hwptp"; last done. iPureIntro. pclearbot.
             apply REL.
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
*)

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

  Definition wptp_IH (tid : option nat) (tp : list (itree (threadpoolE +' E) R)) Φ : iProp Σ :=
    wptp H tid tp Φ ∧
    match tid with
    | Some tid => ∀ tp', wptp H None tp' Φ -∗ wptp H (Some tid) (tp ++ tp') Φ
    | None => ∀ tp' tid' tid_app, ⌜tid_app = (length tp + tid')%nat⌝ →
        wptp H (Some tid') tp' Φ -∗ wptp H (Some tid_app) (tp ++ tp') Φ
    end.
  Definition wptp_IH_right (tid' : option nat) (tp' : list (itree (threadpoolE +' E) R)) Φ : iProp Σ :=
    wptp H tid' tp' Φ ∧
    match tid' with
    | Some tid' => ∀ tp tid_app, ⌜tid_app = (length tp + tid')%nat⌝ →
      wptpF H wptp_IH None tp Φ -∗ wptp H (Some tid_app) (tp ++ tp') Φ
    | None => ∀ tid tp,
      wptpF H wptp_IH (Some tid) tp Φ -∗ wptp H (Some tid) (tp ++ tp') Φ
    end.

  Instance wpi_IH_proper n t tp :
    Proper (pointwise_relation R (dist n) ==> dist n) (wptp_IH t tp).
  Admitted.
  Instance wpi_IH_right_proper n t tp :
    Proper (pointwise_relation R (dist n) ==> dist n) (wptp_IH_right t tp).
  Admitted.

  Lemma lookup_app_r_Some A (xs ys : list A) y n :
    ys !! n = Some y →
    (xs ++ ys) !! (length xs + n) = Some y.
  Admitted.

  Lemma insert_app A (xs ys : list A) y n :
    xs ++ <[n := y]>ys = <[length xs + n := y]>(xs ++ ys).
  Admitted.

  Lemma delete_app_r A (xs ys : list A) n :
    delete (length xs + n) (xs ++ ys) = xs ++ delete n ys.
  Admitted.
  Lemma delete_app_l A (xs ys : list A) n :
    n < length xs →
    delete n (xs ++ ys) = delete n xs ++ ys.
  Admitted.

  Lemma wptp_reorder tp tp' t tid Φ :
    wptp (R:=R) H (Some (length tp + tid + 1)) (tp ++ t :: tp') Φ -∗
    wptp (R:=R) H (Some (length tp + tid + 1)) (t :: tp ++ tp') Φ.
  Admitted.

  Lemma wptp_wptpIH' `{!Sequential H} tid' tp' Φ :
    wptp H tid' tp' Φ -∗ wptp_IH_right tid' tp' Φ.
  Proof.
    generalize tid' tp' Φ.
    iApply (wptp_iter _); first solve_proper.
    iModIntro. clear tid' tp' Φ. iIntros (tid' tp' Φ) "Hwptp'".
    iSplit.
    { rewrite wptp_unfold /=. iApply wptpF_mono; last done. iModIntro. clear.
      iIntros (t tp Φ) "Hwptp". iDestruct "Hwptp" as "[$ _]".
    }
    destruct tid' as [tid'|].
    - iIntros (tp tid_app ->) "Hwptp".
      iEval (rewrite wptp_unfold /=).
      iDestruct (wptp_inversion with "Hwptp'") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|(%A&%e&%k&%Hidx&HH)]]]]]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        done.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iModIntro.
        rewrite -insert_app. by iApply "Hwptp''".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. rewrite -insert_app. iApply wptp_reorder. iMod "Hwptp''".
        iDestruct "Hwptp''" as "[_ Hwptp'']".
        iApply "Hwptp''". { iPureIntro. lia. } done.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. iModIntro. iMod "Hwptp''". iModIntro. iEval (rewrite wptp_unfold /=).
        iSplit.
        + iIntros (new_tid t' Hidx').
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iSpecialize ("Hwptp" $! _ _ Hidx'). iMod "Hwptp". iModIntro.
             iDestruct "Hwptp" as "[_ Hwptp]". iApply "Hwptp". iDestruct "Hwptp''" as "[[$ _] _]".
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''". { iPureIntro. lia. }
             clear. iIntros (new_tid t' Hidx). by iApply "Hwptp".
        + clear. iIntros (new_tid t' Hidx').
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iSpecialize ("Hwptp" $! _ _ Hidx'). iMod "Hwptp". iModIntro.
             iDestruct "Hwptp" as "[_ Hwptp]". iApply "Hwptp". iDestruct "Hwptp''" as "[[$ _] _]".
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''". { iPureIntro. lia. }
             clear. iIntros (new_tid t' Hidx). by iApply "Hwptp".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. iModIntro. iMod "Hwptp''". iModIntro. iEval (rewrite wptp_unfold /=).
        iSplit.
        + iIntros (new_tid t' Hidx').
          rewrite delete_app_r in Hidx'. rewrite delete_app_r.
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iSpecialize ("Hwptp" $! _ _ Hidx'). iMod "Hwptp". iModIntro.
             iDestruct "Hwptp" as "[_ Hwptp]". iApply "Hwptp". iDestruct "Hwptp''" as "[[$ _] _]".
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''". { iPureIntro. lia. }
             clear. iIntros (new_tid t' Hidx). by iApply "Hwptp".
        + clear. iIntros (new_tid t' Hidx').
          rewrite delete_app_r in Hidx'. rewrite delete_app_r.
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iSpecialize ("Hwptp" $! _ _ Hidx'). iMod "Hwptp". iModIntro.
             iDestruct "Hwptp" as "[_ Hwptp]". iApply "Hwptp". iDestruct "Hwptp''" as "[[$ _] _]".
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''". { iPureIntro. lia. }
             clear. iIntros (new_tid t' Hidx). by iApply "Hwptp".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. } 
        simpl. iMod "HH". iModIntro. iApply (ihandler_mono with "[Hwptp]"); last done.
        + iIntros (a) "[_ Hwptp']". rewrite -insert_app. by iApply "Hwptp'".
        + eauto.
    - iIntros (tid tp) "Hwptp".
      iEval (rewrite wptp_unfold /=).
      iDestruct (wptp_inversion with "Hwptp") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|(%A&%e&%k&%Hidx&HH)]]]]]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        done.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iModIntro.
        rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
        iApply "Hwptp''". iEval (rewrite wptp_unfold /=).
        clear. iIntros (tid' t' Hidx). iSpecialize ("Hwptp'" $! _ _ Hidx). iMod "Hwptp'". iModIntro.
        iDestruct "Hwptp'" as "[$ _]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
        iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''".
        iEval (rewrite wptp_unfold /=).
        clear. iModIntro. iIntros (tid' t' Hidx). iSpecialize ("Hwptp'" $! _ _ Hidx).
        iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. iModIntro. iMod "Hwptp''". iModIntro. iEval (rewrite wptp_unfold /=).
        iSplit.
        + iIntros (new_tid t' Hidx').
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''".
             iEval (rewrite wptp_unfold /=).
             clear. iIntros (tid' t' Hidx). iSpecialize ("Hwptp'" $! _ _ Hidx).
             iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
          ++ iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'". iModIntro.
             iDestruct "Hwptp'" as "[_ Hwptp']". iApply "Hwptp'". { iPureIntro. lia. }
             iDestruct "Hwptp''" as "[_ $]".
        + clear. iIntros (new_tid t' Hidx').
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''".
             iEval (rewrite wptp_unfold /=).
             clear. iIntros (tid' t' Hidx). iSpecialize ("Hwptp'" $! _ _ Hidx).
             iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
          ++ iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'". iModIntro.
             iDestruct "Hwptp'" as "[_ Hwptp']". iApply "Hwptp'". { iPureIntro. lia. }
             iDestruct "Hwptp''" as "[_ $]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. iModIntro. iMod "Hwptp''". iModIntro. iEval (rewrite wptp_unfold /=).
        iSplit.
        + iIntros (new_tid t' Hidx').
          rewrite delete_app_l in Hidx'; last first. { by eapply lookup_lt_Some. }
          rewrite delete_app_l; last first. { by eapply lookup_lt_Some. }
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''".
             iEval (rewrite wptp_unfold /=).
             clear. iIntros (tid' t' Hidx). iSpecialize ("Hwptp'" $! _ _ Hidx).
             iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
          ++ iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'". iModIntro.
             iDestruct "Hwptp'" as "[_ Hwptp']". iApply "Hwptp'". { iPureIntro. lia. }
             iDestruct "Hwptp''" as "[_ $]".
        + clear -Hidx. iIntros (new_tid t' Hidx').
          rewrite delete_app_l in Hidx'; last first. { by eapply lookup_lt_Some. }
          rewrite delete_app_l; last first. { by eapply lookup_lt_Some. }
          apply lookup_app_Some in Hidx' as [Hidx'|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iSpecialize ("Hwptp''" $! _ _ Hidx').
             iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''".
             iEval (rewrite wptp_unfold /=).
             clear. iIntros (tid' t' Hidx). iSpecialize ("Hwptp'" $! _ _ Hidx).
             iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
          ++ iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'". iModIntro.
             iDestruct "Hwptp'" as "[_ Hwptp']". iApply "Hwptp'". { iPureIntro. lia. }
             iDestruct "Hwptp''" as "[_ $]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. } 
        simpl. iMod "HH". iModIntro. iApply (ihandler_mono with "[Hwptp']"); last done.
        + iIntros (a) "[_ Hwptp]". rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
          iApply "Hwptp". iEval (rewrite wptp_unfold /=).
          clear. iIntros (tid' t' Hidx). iSpecialize ("Hwptp'" $! _ _ Hidx).
          iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
        + eauto.
  Qed.

  Lemma wptp_wptpIH `{!Sequential H} tid tp Φ :
    wptp H tid tp Φ -∗
    wptp_IH tid tp Φ.
  Proof.
    generalize tid tp Φ.
    iApply (wptp_iter wptp_IH); first solve_proper.
    iModIntro. clear tid tp Φ. iIntros (tid tp Φ) "Hwptp".
    iSplit.
    { rewrite wptp_unfold /=. iApply wptpF_mono; last done. iModIntro. clear.
      iIntros (t tp Φ) "Hwptp". iDestruct "Hwptp" as "[$ _]".
    }
    destruct tid as [|tid].
    - iIntros (tp') "Hwptp'".
      iDestruct (wptp_wptpIH' with "Hwptp'") as "[_ Hwptp']". by iApply "Hwptp'".
    - iIntros (tp' tid' tid_app ->) "Hwptp'".
      iDestruct (wptp_wptpIH' with "Hwptp'") as "[_ Hwptp']". by iApply "Hwptp'".
  Qed.

  Lemma wptp_wand (t : itree (threadpoolE +' E) R) tp Φ Ψ :
    □ (∀ r, Φ r -∗ Ψ r) -∗
    wptp H t tp Φ -∗
    wptp H t tp Ψ.
  Admitted.

  Lemma wptp_reorder (t t1 t2 : itree (threadpoolE +' E) R) tp Φ :
    wptp H t (t1 :: t2 :: tp) Φ -∗
    wptp H t (t2 :: t1 :: tp) Φ.
  Admitted.

  Definition wptp_IH (t : itree (threadpoolE +' E) R) (tp : list (itree (threadpoolE +' E) R)) Φ : iProp Σ :=
    wptp H t tp Φ ∧
    (∀ t', WPi t' @ threadpoolH ⊕ H; ⊤ {{ Φ }} -∗ wptp H t (t' :: tp) Φ).

  Instance wpi_IH_proper n t tp :
    Proper (pointwise_relation R (dist n) ==> dist n) (wptp_IH t tp).
  Admitted.

  Lemma wptp_suspended (t : itree (threadpoolE +' E) R) tp Φ :
    WPi t @ threadpoolH ⊕ H; ⊤ {{ Φ }} -∗
    (∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → |={⊤,∅}=> wptp_IH new_current (delete new_current_tid tp) Φ) -∗
    |={⊤, ∅}=> wptp H t tp Φ.
  Admitted.

  Lemma wp_wptp `{!Sequential H} t tp Φ :
    wptp H t tp Φ -∗
    wptp_IH t tp Φ.
  Proof.
    generalize t tp Φ.
    iApply (wptp_iter wptp_IH); first solve_proper.
    iModIntro. clear t tp Φ. iIntros (t tp Φ) "Hwptp".
    iSplit.
    - rewrite wptp_unfold /=. iApply wptpF_mono; last done. iModIntro. clear.
      iIntros (t tp Φ) "Hwptp". iDestruct "Hwptp" as "[$ _]".
    - iIntros (t') "Hwp".
      iDestruct (wptp_inversion with "Hwptp") as "[(%r&->&HΦ)|[(%tnext&->&Hwptp)|[(%k&->&Hwptp)|[(%k&->&Hwptp)|[(%k&->&Hwptp)|(%A&%e&%k&->&HH)]]]]]".
      * rewrite wptp_unfold /wptpF //.
      * iEval (rewrite wptp_unfold /wptpF /=). iMod "Hwptp". iDestruct "Hwptp" as "[_ Hwptp]".
        by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=). iMod "Hwptp". iApply wptp_reorder.
        iDestruct "Hwptp" as "[_ Hwptp]". by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=).
        iModIntro. iMod "Hwptp". iModIntro. iSplit.
        + iIntros (new_current_tid new_current Hidx).
          destruct new_current_tid as [|new_current_tid'].
          ++ simpl in Hidx. injection Hidx as <-. simpl.
             iApply (wptp_suspended with "Hwp").
             iIntros (new_current_tid new_current Hidx).
             destruct new_current_tid as [|new_current_tid'].
             +++ simpl in Hidx. injection Hidx as <-. iDestruct "Hwptp" as "[_ $]".
             +++ by iApply "Hwptp".
          ++ simpl. simpl in Hidx. iDestruct "Hwptp" as "[Hwptp _]".
             iDestruct ("Hwptp" $! _ _ Hidx) as "[_ Hwptp]". iApply wptp_reorder. by iApply "Hwptp".
        + iDestruct "Hwptp" as "[_ Hwptp]". iMod "Hwptp" as "[_ Hwptp]". by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=).
        iModIntro. iMod "Hwptp". iModIntro.
        iIntros (new_current_tid new_current Hidx).
        destruct new_current_tid as [|new_current_tid'].
        + simpl in Hidx. injection Hidx as <-. simpl.
          iApply (wptp_suspended with "Hwp").
          iIntros (new_current_tid new_current Hidx).
          by iApply "Hwptp".
        + simpl. simpl in Hidx. iDestruct ("Hwptp" $! _ _ Hidx) as "[_ Hwptp]".
          by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=).
        iApply (is_seq _ _ _ (const True%I)).
        iApply (ihandler_mono with "[Hwp]"); last done.
        + iIntros (a) "[_ Hwptp]". by iApply "Hwptp".
        + iModIntro. by iIntros (a) "?".
  Qed.

  (* TODO: Extract the G into its own definition (wpi_IH). If necessary, prove
     monotonicity and reuse that. *)
  Definition wpi_IH (t : itree (threadpoolE +' E) R) Φ_fupd : iProp Σ :=
    WPi t @ threadpoolH ⊕ H; ∅ {{ Φ_fupd }} ∧
    ∀ tp Φ, (□ ∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
    (* (1) Passing control back to threadpool. *)
    ((∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → |={⊤,∅}=> wptp H new_current (delete new_current_tid tp) Φ) -∗
      wptp H t tp Φ
    ) ∧
    (* (2) Forking new threads. *)
    (∀ t' tp, wptp H t' tp Φ -∗ wptp H t' (t :: tp) Φ).

  Instance wpi_IH_proper n t :
    Proper (pointwise_relation R (dist n) ==> dist n) (wpi_IH t).
  Admitted.

  Lemma wpi_IH_wand (t : itree (threadpoolE +' E) R) Φ Ψ:
    (∀ r, Φ r -∗ Ψ r) -∗
    wpi_IH t Φ -∗
    wpi_IH t Ψ.
  Admitted.

  Lemma wptp_suspended (t : itree (threadpoolE +' E) R) tp Φ :
    wpiF (threadpoolH ⊕ H) wpi_IH t (λ r, |={∅, ⊤}=> Φ r) -∗
    (∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → |={⊤,∅}=> wptp H new_current (delete new_current_tid tp) Φ) -∗
    wptp H t tp Φ.
  Proof.
    iIntros "Hwp Hsuspend".
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]]; rewrite wptp_unfold /wptpF /wpiF /=.
    - done.
    - iMod "Hwp" as "[_ Hwp]". iDestruct ("Hwp" $! tp Φ with "[]") as "[Hwp _]"; first eauto.
      by iApply "Hwp".
    - destruct e as [e|e]; first destruct e.
      * iMod "Hwp" as "[Hcur Hnew]". iModIntro. rewrite /handle_threadpoolE.
        iDestruct "Hcur" as "[_ Hcur]". iDestruct ("Hcur" with "[]") as "[_ Hcur]"; first eauto.
  Admitted.

  Lemma wp_wptp `{!Sequential H} (t : itree (threadpoolE +' E) R) Φ_fupd :
    WPi t @ threadpoolH ⊕ H; ∅ {{ Φ_fupd }} -∗
    wpi_IH t Φ_fupd.
  Proof.
    generalize t Φ_fupd.
    iApply (wpi_iter (H := threadpoolH ⊕ H) wpi_IH); first solve_proper.
    iModIntro. clear t Φ_fupd. iIntros (t Φ_fupd) "Hwp".
    iSplit; last iIntros (tp Φ) "#Hwand"; last iSplit.
    - iApply wpi_wand; last first.
      * rewrite wpi_unfold. iApply wpiF_mono; last done. iModIntro. clear.
        iIntros (t Φ_fupd) "Hwp". iDestruct "Hwp" as "[$ _]".
      * eauto.
    - iIntros "Hwptp". iApply (wptp_suspended with "[Hwp Hwand] Hwptp").
      iApply (wpiF_wand with "Hwand").
      { clear t. iIntros (t) "Hwp". by iApply wpi_IH_wand. }
      iApply wpiF_mono; last done.
      clear t. iModIntro. by iIntros (t Φ') "Hwp".
    - clear tp. iIntros (t' tp) "Hwptp".
      epose (G := (λ (t : leibnizO (itree (threadpoolE +' E) R)) (tp : leibnizO (list (itree (threadpoolE +' E) R))) (Φ : leibnizO R -d> iPropO Σ), ∀ t',
        (|={⊤, ∅}=> wpiF (threadpoolH ⊕ H) wpi_IH t' (λ r, |={∅, ⊤}=> Φ r)) -∗ wptp H t (t' :: tp) Φ
        )%I).
      iAssert (∀ t tp Φ, wptp H t tp Φ -∗ G t tp Φ)%I as "Hgen"; last first.
      { iApply ("Hgen" with "Hwptp"); eauto. iApply (wpiF_wand with "Hwand"); last done.
        iIntros (?) "Hwp". by iApply wpi_IH_wand. }
      iApply (wptp_ind (H := H) G).
      { clear. intros ??????. rewrite /G. do 3 f_equiv.
        - apply wpiF_ne.
          * intros t1 t2 <- Φ1 Φ2 HΦ. by apply wpi_IH_proper.
          * done.
          * intros ?. by f_equiv.
        - rewrite /wptp. apply least_fixpoint_ne; first done. by split.
      }
      iModIntro. iClear "Hwand". clear t t' tp Φ Φ_fupd.
      iIntros (t tp Φ_fupd) "Hwptp". iIntros (t') "Hwp".
      iDestruct (wptp_inversion with "Hwptp") as "[(%r&->&HΦ)|[(%tnext&->&Hwptp)|[(%k&->&Hwptp)|[(%k&->&Hwptp)|[(%k&->&Hwptp)|(%A&%e&%k&->&HH)]]]]]".
      * rewrite wptp_unfold /wptpF //.
      * iEval (rewrite wptp_unfold /wptpF /=). iMod "Hwptp". iDestruct "Hwptp" as "[Hwptp _]".
        by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=). iMod "Hwptp". iApply wptp_reorder.
        iDestruct "Hwptp" as "[Hwptp _]". by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=).
        iModIntro. iMod "Hwptp". iModIntro. iMod "Hwptp". iModIntro.
        iSplit.
        + iIntros (new_current_tid new_current Hidx).
          destruct new_current_tid as [|new_current_tid'].
          ++ simpl in Hidx. injection Hidx as <-. simpl.
             iApply (wptp_suspended with "[Hwp]").
             { iApply wpiF_wand; eauto. }
             iIntros (new_current_tid new_current Hidx).
             destruct new_current_tid.
             +++ simpl in Hidx. injection Hidx as <-. simpl.
                 by iDestruct "Hwptp" as "[_ [_ Hwptp]]".
             +++ simpl. simpl in Hidx. iDestruct "Hwptp" as "[Hwptp _]".
                 by iDestruct ("Hwptp" $! _ _ Hidx) as "[_ Hwptp]".
          ++ simpl. simpl in Hidx. iDestruct "Hwptp" as "[Hwptp _]".
             iDestruct ("Hwptp" $! _ _ Hidx) as "[Hwptp _]". iApply wptp_reorder. by iApply "Hwptp".
        + iDestruct "Hwptp" as "[_ [Hwptp _]]". by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=).
        iModIntro. iMod "Hwptp". iModIntro. iMod "Hwptp". iModIntro.
        iIntros (new_current_tid new_current Hidx).
        destruct new_current_tid as [|new_current_tid'].
        + simpl in Hidx. injection Hidx as <-. simpl.
          iApply (wptp_suspended with "Hwp").
          iIntros (new_current_tid new_current Hidx).
          by unshelve iDestruct ("Hwptp" $! _ _ _) as "[_ Hwptp]".
        + simpl. simpl in Hidx. iDestruct ("Hwptp" $! _ _ Hidx) as "[Hwptp _]".
          by iApply "Hwptp".
      * iEval (rewrite wptp_unfold /wptpF /=).
        iApply (is_seq _ _ _ (const True%I)).
        iApply (ihandler_mono with "[Hwp]"); last done.
        + iIntros (a) "[Hwptp _]". by iApply "Hwptp".
        + iModIntro. by iIntros (a) "?".
  Qed.

  Lemma wp_wptp (t : itree (threadpoolE +' E) R) Φ :
    WPi t @ threadpoolH ⊕ H; ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    ∀ tp,
    (
      (* (1) Passing control back to threadpool. Depends on (1) and (2). *)
      ((∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → wptp H new_current (delete new_current_tid tp) Φ) -∗
        wptp H t tp Φ
      ) ∧
      (* (2) Forking new threads. Depends on (1). *)
      (∀ t' tp, wptp H t' tp Φ -∗ wptp H t' (t :: tp) Φ)
    ).
  Proof.
    epose (G := (λ (t : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ), ∀ tp Φ,
      □ (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
      (* (1) Passing control back to threadpool. Depends on (1) and (2). *)
      ((∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → wptp H new_current (delete new_current_tid tp) Φ) -∗
        wptp H t tp Φ
      ) ∧
      (* (2) Forking new threads. Depends on (1). *)
      (∀ t' tp, wptp H t' tp Φ -∗ wptp H t' (t :: tp) Φ)
      )%I).
    { intros n Φ1 Φ2 HΦ. repeat f_equiv. }
    iAssert (□ ∀ t Φ Ψ, □ (∀ r, Φ r -∗ Ψ r) -∗ G t Φ -∗ G t Ψ)%I as "#HGmono".
    { admit.
    }
    iAssert (∀ t Φ_fupd, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ_fupd }} -∗ G t Φ_fupd)%I as "Hgen"; last first.
    { iIntros "Hwp" (tp). iSplit.
      - iIntros "Hwptp". iApply ("Hgen" with "Hwp"). { iModIntro. by iIntros (r) "HΦ". }
        iIntros (new_current_tid new_current Hidx). by iApply "Hwptp".
      - iIntros (t' tp') "Hwptp". iApply ("Hgen" with "Hwp"); last done.
        iModIntro. by iIntros (r) "HΦ".
    }
    iApply (wpi_ind (H := threadpoolH ⊕ H) G); first solve_proper.
    clear t Φ. iModIntro. iIntros (t Φ_fupd) "Hwp". iIntros (tp Φ) "#Hwand". iSplit.
    - iIntros "Hwptp". iApply (wptp_suspended with "[Hwp Hwand] Hwptp").
      iApply (wpiF_wand with "Hwand").
      { clear t. iIntros (t) "Hwp". iIntros (Φ') "Hwand'".
        iAssert (∀ r : leibnizO R, Φ_fupd r ={∅,⊤}=∗ Φ' r)%I with "[Hwand Hwand']" as "Hwand''".
        { iIntros (r) "HΦ_fupd". iApply "Hwand'". by iApply "Hwand". }
        iSplit; last iSplit.
      - iIntros "Hyield".
        iDestruct ("Hwp" with "Hwand''") as "[Hwp _]". iApply "Hwp".
        iIntros (???). by iApply "Hyield".
      - iIntros (t' tp') "Hwptp". 
        iDestruct ("Hwp" with "Hwand''") as "[_ [Hwp _]]". by iApply "Hwp".
      - iDestruct ("Hwp" with "Hwand''") as "[_ [_ Hwp]]". by iApply "Hwp".
      }
      iApply wpiF_mono; last done.
      clear t. iModIntro. iIntros (t Φ') "Hwp". iIntros (Φ'') "Hwand'".
      iAssert (∀ r : leibnizO R, Φ_fupd r ={∅,⊤}=∗ Φ' r)%I with "[Hwand Hwand']" as "Hwand''".
      { iIntros (r) "HΦ_fupd". iApply "Hwand'". by iApply "Hwand". }
      iSplit; last iSplit.
      * iIntros "Hyield".
        iDestruct ("Hwp" with "Hwand''") as "[Hwp _]". iApply "Hwp".
        iIntros (???). by iApply "Hyield".
      - iIntros (t' tp') "Hwptp". 
        iDestruct ("Hwp" with "Hwand''") as "[_ [Hwp _]]". by iApply "Hwp".
      - iDestruct ("Hwp" with "Hwand''") as "[_ [_ Hwp]]". by iApply "Hwp".

  Lemma wptp_suspended (t : itree (threadpoolE +' E) R) tp Φ :
    WPi t @ threadpoolH ⊕ H; ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    (∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → wptp H new_current (delete new_current_tid tp) Φ) -∗
    wptp H t tp Φ.
  Proof.
    epose (G := (λne (t : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ), ∀ tp Φ,
      (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
      (∀ new_current_tid new_current, ⌜tp !! new_current_tid = Some new_current⌝ → wptp H new_current (delete new_current_tid tp) Φ) -∗
      wptp H t tp Φ
      )%I).
    { intros n Φ1 Φ2 HΦ. repeat f_equiv. }
    iAssert (∀ t Φ_fupd, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ_fupd }} -∗ G t Φ_fupd)%I as "Hgen"; last first.
    { iIntros "Hwp Hwptp". iApply ("Hgen" with "Hwp").
      - by iIntros (r) "HΦ".
      - iIntros (new_current_tid new_current Hidx). by iApply "Hwptp".
    }
    clear. iApply (wpi_iter' (H := threadpoolH ⊕ H) G); first solve_proper.
    - iModIntro. iIntros (Φ r) "HΦ". iIntros (tp Φ') "Hwand Hwptp". rewrite wptp_unfold /wptpF /=.
      by iApply "Hwand".
    - iModIntro. iIntros (Φ t) "HG". iIntros (tp Φ') "Hwand Hwptp". rewrite wptp_unfold /wptpF /=.
      iApply ("HG" with "Hwand"). iIntros (new_current_tid new_current Hidx). by iApply "Hwptp".
    - iModIntro. iIntros (Φ A e k) "HH". iIntros (tp Φ') "Hwand Hwptp".
      destruct e as [e|e]; rewrite wptp_unfold /wptpF /=.
      * rewrite /handle_threadpoolE /=. destruct e.
        + iMod "HH" as "[Hcurrent Hnew]". iApply ("Hcurrent" with "Hwand"). iModIntro.
          iIntros (new_current_tid new_current Hidx). Admitted.

  Lemma wp_wptp (t t' : itree (threadpoolE +' E) R) tp Φ :
    WPi t' @ threadpoolH ⊕ H; ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    wptp H t tp Φ -∗
    wptp H t (t' :: tp) Φ.
  Proof.
    epose (G := (λ (t : leibnizO (itree (threadpoolE +' E) R)) (tp : leibnizO (list (itree (threadpoolE +' E) R))) (Φ : leibnizO R -d> iPropO Σ),
      ∀ t', WPi t' @ threadpoolH ⊕ H; ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗ wptp H t (t' :: tp) Φ
      )%I).
    iAssert (∀ t tp Φ, wptp H t tp Φ -∗ G t tp Φ)%I as "Hgen"; last first.
    { iIntros "Hwp Hwptp". iApply ("Hgen" with "Hwptp"); eauto. }
    iApply (wptp_ind (H := H) G).
    { intros n t1 t2 <- tp1 tp2 <- Φ1 Φ2 HΦ. rewrite /G. f_equiv.
      f_equiv. f_equiv.
      - do 3 f_equiv. apply HΦ.
      - rewrite /wptp. by apply least_fixpoint_ne.
    }
    iModIntro. clear t t' tp Φ. iIntros (t tp Φ) "Hwptp". iIntros (t') "Hwp".
    iDestruct (wptp_inversion with "Hwptp") as "[(%r&->&HΦ)|[(%tnext&->&Hwptp)|[(%k&->&Hwptp)|[(%k&->&Hwptp)|[(%k&->&Hwptp)|(%A&%e&%k&->&HH)]]]]]".
    - rewrite wptp_unfold /wptpF //.
    - iEval (rewrite wptp_unfold /wptpF /=). iMod "Hwptp". iDestruct "Hwptp" as "[Hwptp _]".
      by iApply "Hwptp".
    - iEval (rewrite wptp_unfold /wptpF /=). iMod "Hwptp". iApply wptp_reorder.
      iDestruct "Hwptp" as "[Hwptp _]". by iApply "Hwptp".
    - iEval (rewrite wptp_unfold /wptpF /=).
      iModIntro. iMod "Hwptp". iModIntro. iMod "Hwptp". iModIntro.
      iSplit.
      * iIntros (new_current_tid new_current Hidx).
        destruct new_current_tid as [|new_current_tid'].
        + simpl in Hidx. injection Hidx as <-. simpl.
          iApply (wptp_suspended with "Hwp").
          iIntros (new_current_tid new_current Hidx).
          destruct new_current_tid.
          ++ simpl in Hidx. injection Hidx as <-. simpl.
             by iDestruct "Hwptp" as "[_ [_ Hwptp]]".
          ++ simpl. simpl in Hidx. iDestruct "Hwptp" as "[Hwptp _]".
             by iDestruct ("Hwptp" $! _ _ Hidx) as "[_ Hwptp]".
        + simpl. simpl in Hidx. iDestruct "Hwptp" as "[Hwptp _]".
          iDestruct ("Hwptp" $! _ _ Hidx) as "[Hwptp _]". iApply wptp_reorder. by iApply "Hwptp".
      * iDestruct "Hwptp" as "[_ [Hwptp _]]". by iApply "Hwptp".
    - iEval (rewrite wptp_unfold /wptpF /=).
      iModIntro. iMod "Hwptp". iModIntro. iMod "Hwptp". iModIntro.
      iIntros (new_current_tid new_current Hidx).
      destruct new_current_tid as [|new_current_tid'].
      * simpl in Hidx. injection Hidx as <-. simpl.
        iApply (wptp_suspended with "Hwp").
        iIntros (new_current_tid new_current Hidx).
        by iDestruct ("Hwptp" $! _ _ _) as "[_ Hwptp]".
      * simpl. simpl in Hidx. iDestruct ("Hwptp" $! _ _ Hidx) as "[Hwptp _]".
        by iApply "Hwptp".
    - iEval (rewrite wptp_unfold /wptpF /=).
      iApply (is_seq _ _ _ (const True%I)).
      iApply (ihandler_mono with "[Hwp]"); last done.
      * iIntros (a) "[Hwptp _]". by iApply "Hwptp".
      * iModIntro. by iIntros (a) "?".
  Qed.

  Lemma wp_wptp (t : itree (threadpoolE +' E) R) Φ :
    WPi t @ (threadpoolH ⊕ H); ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    wptp H t [] Φ.
  Proof.
    epose (G := (λ (t : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ Φ, (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗ wptp H t [] Φ
      )%I).
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
    epose (G := (λ (current : leibnizO (itree (threadpoolE +' E) R)) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ interleaving tp Φ,
        ⌜interleaves tp current interleaving⌝ →
        (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
        ([∗ list] thread ∈ tp, WPi thread @ threadpoolH ⊕ H; ⊤ {{ Φ }}) -∗
        WPi interleaving @ H; ∅ {{ r, |={∅, ⊤}=> Φ r }}
    )%I).
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
