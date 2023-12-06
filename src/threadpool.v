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

  (* TODO: Update comments here in view of changes to the way that the focused
  thread is encoded etc. *)

  (** The interleaving relation, prior to taking the fixpoint. This relation
  encodes what it means for an [itree E R] to refine an itree
  [itree (threadpoolE +' E) R] that can emit events [threadpoolE] regarding
  concurrency. *)
  Variant interleavesF
    (interleaves : nat → list (itree (threadpoolE +' E) R) → itree E R → Prop)
    : nat
    → itree' (threadpoolE +' E) R
    → list (itree (threadpoolE +' E) R)
    → itree' E R
    → Prop :=
  (** If a thread returns, the interleaved [itree] ends. *)
  | Return current_tid tp r :
    interleavesF interleaves current_tid (RetF r) tp (RetF r)
  (** If the current thread steps, so does the interleaved [itree]. *)
  | Step current_tid current' tp interleaving' :
    interleaves current_tid (<[current_tid:=current']>tp) interleaving' →
    interleavesF interleaves current_tid (TauF current') tp (TauF interleaving')
  (** If an event of type [E] is emitted, the interleaved [itree] also
  emits this event. *)
  | Emit current_tid tp A (e : E A) k k' :
    (∀ a, interleaves current_tid (<[current_tid:=k a]>tp) (k' a)) →
    interleavesF interleaves current_tid (VisF (inr1 e) k) tp (VisF e k')
  (** If a thread emits the [EKillThread] event, the thread ends and control is
  yielded to some other thread in the threadpool. The interleaved [itree] takes
  a silent step in place of the [EKillThread]. *)
  | KillThread current_tid tp k new_current_tid new_current interleaving' :
    delete current_tid tp !! new_current_tid = Some new_current →
    interleaves new_current_tid (delete current_tid tp) interleaving' →
    interleavesF interleaves current_tid (VisF (inl1 EKillThread) k) tp (TauF interleaving')
  (** The [EYield] event yields control to another thread placing the current
  thread in the threadpool to be resumed. Resumption costs a step. The
  interleaved [itree] takes a silent step in place of the [EYield]. *)
  | Yield current_tid tp k new_current_tid new_current interleaving' :
    tp !! new_current_tid = Some new_current →
    interleaves new_current_tid (<[current_tid := k ()]>tp) interleaving' →
    interleavesF interleaves current_tid (VisF (inl1 EYield) k) tp (TauF interleaving')
  (** The [EFork] event adds a new thread to the threadpool and continues
  executing the current thread. The interleaved [itree] takes a silent step in
  place of the [EFork]. *)
  | Fork current_tid tp k interleaving' :
    interleaves (S current_tid) (k NewThread :: <[current_tid := k CurrentThread]>tp) interleaving' →
    interleavesF interleaves current_tid (VisF (inl1 EFork) k) tp (TauF interleaving').
  Hint Constructors interleavesF : iris_itree.
  Definition interleaves_
    (interleaves : nat → list (itree (threadpoolE +' E) R) → itree E R → Prop)
    : nat
    → list (itree (threadpoolE +' E) R)
    → itree E R
    → Prop :=
    λ tid tp interleaving, ∃ t, tp !! tid = Some t ∧ interleavesF interleaves tid (observe t) tp (observe interleaving).

  Lemma interleavesF_mono interleaves interleaves' tid t tp interleaving :
    interleaves <3= interleaves' →
    interleavesF interleaves tid t tp interleaving →
    interleavesF interleaves' tid t tp interleaving.
  Proof.
    intros Hleq HinterleavesF. destruct HinterleavesF; eauto with iris_itree.
  Qed.
  Lemma interleaves__mono :
    monotone3 interleaves_.
  Proof.
    rewrite /monotone3 /interleaves_. intros tid tp t r r' [t' [Hidx Hinter]] Hrel.
    eexists. split; first done. by eapply interleavesF_mono; last done.
  Qed.
  Hint Resolve interleaves__mono : paco.

  (** The interleaving relation. (See comments above.) *)
  Definition interleaves : nat → list (itree (threadpoolE +' E) R) → itree E R → Prop :=
    paco3 interleaves_ bot3.

  Lemma interleaves_inversion_Ret tid tp r interleaving :
    tp !! tid = Some (Ret r) →
    interleaves tid tp interleaving →
    interleaving ≅ Ret r.
  Proof.
    intros Hidx Hinter. punfold Hinter. destruct Hinter as [t [Hidx' Hinter]].
    rewrite Hidx' in Hidx. injection Hidx as Hidx. rewrite Hidx in Hinter.
    inversion Hinter. subst. by simplify_obs.
  Qed.
  Lemma interleaves_inversion_Tau tid tp t interleaving :
    tp !! tid = Some (Tau t) →
    interleaves tid tp interleaving →
    ∃ interleaving', interleaves tid (<[tid := t]>tp) interleaving' ∧ interleaving ≅ Tau interleaving'.
  Proof.
    intros Hidx Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]].
    rewrite Hidx' in Hidx. injection Hidx as Hidx. rewrite Hidx in Hinter.
    inversion Hinter. subst. exists interleaving'. pclearbot. by simplify_obs.
  Qed.
  Lemma interleaves_inversion_Vis_EKillThread tid tp k interleaving :
    tp !! tid = Some (Vis (inl1 EKillThread) k) →
    interleaves tid tp interleaving →
    ∃ interleaving' tid', interleaves tid' (delete tid tp) interleaving' ∧ interleaving ≅ Tau interleaving'.
  Proof.
    intros Hidx Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]].
    rewrite Hidx' in Hidx. injection Hidx as Hidx. rewrite Hidx in Hinter.
    inversion Hinter. subst. pclearbot. simplify_K. exists interleaving', new_current_tid.
    split; first done. by simplify_obs.
  Qed.
  Lemma interleaves_inversion_Vis_EYield tid tp k interleaving :
    tp !! tid = Some (Vis (inl1 EYield) k) →
    interleaves tid tp interleaving →
    ∃ interleaving' tid', interleaves tid' (<[tid:=k ()]>tp) interleaving' ∧ interleaving ≅ Tau interleaving'.
  Proof.
    intros Hidx Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]].
    rewrite Hidx' in Hidx. injection Hidx as Hidx. rewrite Hidx in Hinter.
    inversion Hinter. subst. pclearbot. simplify_K. exists interleaving', new_current_tid.
    split; first done. by simplify_obs.
  Qed.
  Lemma interleaves_inversion_Vis_EFork tid tp k interleaving :
    tp !! tid = Some (Vis (inl1 EFork) k) →
    interleaves tid tp interleaving →
    ∃ interleaving', interleaves (S tid) (k NewThread :: <[tid:=k CurrentThread]>tp) interleaving' ∧ interleaving ≅ Tau interleaving'.
  Proof.
    intros Hidx Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]].
    rewrite Hidx' in Hidx. injection Hidx as Hidx. rewrite Hidx in Hinter.
    inversion Hinter. subst. pclearbot. simplify_K. exists interleaving'. by simplify_obs.
  Qed.
  Lemma interleaves_inversion_Vis tid tp A (e : E A) k interleaving :
    tp !! tid = Some (Vis (inr1 e) k) →
    interleaves tid tp interleaving →
    ∃ k', (∀ a, interleaves tid (<[tid:=k a]>tp) (k' a)) ∧ interleaving ≅ Vis e k'.
  Proof.
    intros Hidx Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]].
    rewrite Hidx' in Hidx. injection Hidx as Hidx. rewrite Hidx in Hinter.
    inversion Hinter. subst. pclearbot. simplify_K. exists k'. by simplify_obs.
  Qed.

  Lemma interleaves_lookup tid tp interleaving :
    interleaves tid tp interleaving →
    ∃ t, tp !! tid = Some t.
  Proof.
    intros Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]]. eauto.
  Qed.
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
    (* TODO: Unify [EKillThread] and [EYield] by having a unified insert/delete
    accepting an [option nat]. *)
    | EKillThread => λ k,
      (
      (|={∅, ⊤}=> wptp None (delete tid tp) Φ)
      ∧ ∀ tid' t', ⌜(delete tid tp) !! tid' = Some t'⌝ → |={∅}=> wptp (Some tid') (delete tid tp) Φ
      )
    | EYield => λ k,
      (
      (|={∅, ⊤}=> wptp None (<[tid:=k ()]>tp) Φ)
      ∧ ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={∅}=> wptp (Some tid') (<[tid:=k ()]>tp) Φ
      )
    | EFork => λ k,
      wptp (Some (S tid)) (cons (k NewThread) (<[tid:=k CurrentThread]>tp)) Φ
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
    Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) (wptpF H).
  Proof.
    intros wp1 wp2 Hwptp tid1 tid2 <- tp1 tp2 <- Φ1 Φ2 HΦ.
    rewrite /wptpF'/wptpF. do 2 f_equiv.
    - rewrite /curry3. do 4 f_equiv.
      * by f_equiv.
      * by apply Hwptp.
      * rewrite /handle_threadpoolE.
        destruct e as [e'|e'].
        + rewrite /handle_threadpoolE. destruct e'.
          ++ by apply Hwptp.
          ++ repeat f_equiv; by apply Hwptp.
          ++ repeat f_equiv; first by apply Hwptp. repeat f_equiv. by apply Hwptp.
        + apply handler_ne.
          ++ intros ?. by apply Hwptp.
          ++ by intros.
    - repeat f_equiv. by apply Hwptp.
  Qed.
  Global Instance wptpF'_ne n H :
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) (wptpF' H).
  Proof.
    intros wp1 wp2 Hwp [[tid1 tp1] Q1] [[tid2 tp2] Q2] [[Htid Htp] HQ]. simpl in Htid, Htp, HQ.
    rewrite /wptpF'. by repeat f_equiv.
  Qed.

  Lemma wptpF_mono H wptp1 wptp2:
    ⊢ □ (∀ tid tp Φ, wptp1 tid tp Φ -∗ wptp2 tid tp Φ)
    → ∀ tid tp Φ, wptpF H wptp1 tid tp Φ -∗ wptpF H wptp2 tid tp Φ.
  Proof.
    iIntros "#Hwand" (tid tp Φ) "Hwptp". rewrite /wptpF. destruct tid as [tid|].
    - iDestruct "Hwptp" as "[%t [%Hidx Hwptp]]". iExists _. iSplit. { iPureIntro. exact Hidx. }
      iMod "Hwptp". iModIntro. destruct (observe t).
      * done.
      * by iApply "Hwand".
      * rewrite /handle_threadpoolE. destruct e as [e|e].
        + destruct e.
          ++ by iApply "Hwand".
          ++ iSplit.
             +++ iDestruct "Hwptp" as "[Hwptp _]". by iApply "Hwand".
             +++ iDestruct "Hwptp" as "[_ Hwptp]". iIntros (tid' t' Hidx').
                 iSpecialize ("Hwptp" $! _ _ Hidx'). by iApply "Hwand".
          ++ iSplit.
             +++ iDestruct "Hwptp" as "[Hwptp _]". by iApply "Hwand".
             +++ iDestruct "Hwptp" as "[_ Hwptp]". iIntros (tid' t' Hidx').
                 iSpecialize ("Hwptp" $! _ _ Hidx'). by iApply "Hwand".
        + iApply ihandler_mono.
          ++ eauto.
          ++ eauto.
          ++ iApply ihandler_mono; last done.
             +++ iIntros (a) "Hwptp". by iApply "Hwand".
             +++ eauto.
    - iIntros (tid' t' Hidx). iSpecialize ("Hwptp" $! _ _ Hidx). by iApply "Hwand".
  Qed.
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

  Lemma wptp_unfold H tid tp Φ :
    wptp H tid tp Φ ⊣⊢ wptpF H (wptp H) tid tp Φ.
  Proof.
    apply: least_fixpoint_unfold.
  Qed.

  Global Instance wpi_proper_dist H n tid tp :
    Proper ((pointwise_relation R (dist n)) ==> (dist n)) (wptp H tid tp).
  Proof.
    intros Φ1 Φ2 HΦ. by apply least_fixpoint_ne.
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
      |={∅}=> G (Some (S tid)) (cons (k NewThread) (<[tid:=k CurrentThread]>tp)) Φ
      )
    ∨ (∃ k, ⌜tp !! tid = Some (Vis (inl1 EYield) k)⌝ ∧ (
      (|={∅, ⊤}=> G None (<[tid:=k ()]>tp) Φ)
      ∧ ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={∅}=> G (Some tid') (<[tid:=k ()]>tp) Φ
      ))
    ∨ (∃ k, ⌜tp !! tid = Some (Vis (inl1 EKillThread) k)⌝ ∧ (
      (|={∅, ⊤}=> G None (delete tid tp) Φ)
      ∧ ∀ tid' t', ⌜(delete tid tp) !! tid' = Some t'⌝ → |={∅}=> G (Some tid') (delete tid tp) Φ
      ))
    ∨ (∃ A (e : E A) k, ⌜tp !! tid = Some (Vis (inr1 e) k)⌝ ∧
      |={∅}=> H _ e (λ a, G (Some tid) (<[tid:=k a]>tp) Φ) (λ a, False)
      )
    ).
  Proof.
    iIntros "Hwptp". iDestruct "Hwptp" as "[%t [%Hidx Hwptp]]".
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - iLeft. iExists r. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
    - iRight. iLeft. iExists t'. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
    - destruct e as [e|e].
      * destruct e.
        + iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=. by iMod "Hwptp".
        + iRight. iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=.
          iSplit.
          ++ iMod "Hwptp". iDestruct "Hwptp" as "[$ _]".
          ++ iIntros (tid' t' Hidx'). iMod "Hwptp". iDestruct "Hwptp" as "[_ Hwptp]".
             by iApply "Hwptp".
        + iRight. iRight. iRight. iRight. iLeft. iExists k. iSplit; first done. rewrite /wptpF /=.
          iSplit.
          ++ iMod "Hwptp". iDestruct "Hwptp" as "[$ _]".
          ++ iIntros (tid' t' Hidx'). iMod "Hwptp". iDestruct "Hwptp" as "[_ Hwptp]".
             by iApply "Hwptp".
      * iRight. iRight. iRight. iRight. iRight. iExists _, e, k. iSplit; first done.
        rewrite /wptpF /= //.
  Qed.
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

Section wpi_ind.
  Context {Σ : gFunctors} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context {H : iHandler Σ E}.

  Lemma wpi_ind_masked {R} (G : bool -> itree E R -> (R -d> iPropO Σ) -> iPropO Σ):
    (∀ b t, NonExpansive (G b t)) →
    (□ ∀ t Φ, wpiF H (λ t' Ψ, G false t' Ψ ∧ WPi t' @ H; ∅ {{ Ψ }}) t Φ -∗ G false t Φ) -∗
    (□ ∀ t Φ, (|={⊤, ∅}=> (G false t Φ ∧ WPi t @ H; ∅ {{ Φ }})) -∗ G true t Φ) -∗
    ∀ t Φ, WPi t @ H; ∅ {{ Φ }} -∗ G false t Φ.
  Admitted.

  Lemma wpi_iter_masked {R} (G : bool -> itree E R -> (R -d> iPropO Σ) -> iPropO Σ):
    (∀ b t, NonExpansive (G b t)) →
    (□ ∀ t Φ, wpiF H (G false) t Φ -∗ G false t Φ) -∗
    (□ ∀ t Φ, (|={⊤, ∅}=> G false t Φ) -∗ G true t Φ) -∗
    ∀ t Φ, WPi t @ H; ∅ {{ Φ }} -∗ G false t Φ.
  Admitted.
End wpi_ind.

Section threadpool_adequacy.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context {H : iHandler Σ E}.

  Definition wptp_IH (tid : option nat) (tp : list (itree (threadpoolE +' E) R)) Φ : iProp Σ :=
    wptp H tid tp Φ ∧
    match tid with
    | Some tid => ∀ tp', wptp H None tp' Φ -∗ wptp H (Some tid) (tp ++ tp') Φ
    | None =>
        (∀ tp', wptp H None tp' Φ -∗ wptp H None (tp ++ tp') Φ) ∧
        (∀ tp' tid' tid_app, ⌜tid_app = (length tp + tid')%nat⌝ →
          wptp H (Some tid') tp' Φ -∗ wptp H (Some tid_app) (tp ++ tp') Φ)
    end.
  Definition wptp_IH_right (tid' : option nat) (tp' : list (itree (threadpoolE +' E) R)) Φ : iProp Σ :=
    wptp H tid' tp' Φ ∧
    match tid' with
    | Some tid' => ∀ tp tid_app, ⌜tid_app = (length tp + tid')%nat⌝ →
      wptpF H wptp_IH None tp Φ -∗ wptp H (Some tid_app) (tp ++ tp') Φ
    | None =>
      (∀ tp, wptpF H wptp_IH None tp Φ -∗ wptp H None (tp ++ tp') Φ) ∧
      (∀ tid tp, wptpF H wptp_IH (Some tid) tp Φ -∗ wptp H (Some tid) (tp ++ tp') Φ)
    end.

  Instance wpi_IH_proper n t tp :
    Proper (pointwise_relation R (dist n) ==> dist n) (wptp_IH t tp).
  Proof.
    intros Φ1 Φ2 HΦ. rewrite /wptp_IH. repeat f_equiv.
  Qed.
  Instance wpi_IH_right_proper n t tp :
    Proper (pointwise_relation R (dist n) ==> dist n) (wptp_IH_right t tp).
  Proof.
    intros Φ1 Φ2 HΦ. rewrite /wptp_IH_right. repeat ( done || apply wptpF_ne || f_equiv );
    clear; intros tid1 tid2 <- tp1 tp2 <- Φ1 Φ2 HΦ; repeat f_equiv.
  Qed.

  Lemma lookup_app_r_Some A (xs ys : list A) y n :
    ys !! n = Some y →
    (xs ++ ys) !! (length xs + n) = Some y.
  Proof.
    intros Hidx. rewrite lookup_app_r; last lia.
    by replace (length xs + n - length xs) with n by lia.
  Qed.

  Lemma delete_app_r A (xs ys : list A) n :
    delete (length xs + n) (xs ++ ys) = xs ++ delete n ys.
  Proof.
    rewrite !delete_take_drop.
    replace (S (length xs + n)) with (length xs + (1 + n)) by lia.
    rewrite take_add_app // drop_add_app // -app_assoc //.
  Qed.

  Lemma delete_app_l A (xs ys : list A) n :
    n < length xs →
    delete n (xs ++ ys) = delete n xs ++ ys.
  Admitted.

  Definition enumerate {A} (xs : list A) : list (nat * A) :=
    zip (seq 0 (length xs)) xs.
  Definition permutes {A} (idx : option nat) (xs : list A) (idx' : option nat) (xs' : list A) : Prop :=
    ∃ enumerated_xs',
    enumerate xs ≡ₚ enumerated_xs' ∧
    match idx with
    | Some idx =>
        match idx' with
        | Some idx' => snd <$> enumerated_xs' = xs' ∧ fst <$> (enumerated_xs' !! idx') = Some idx
        | None => False
        end
    | None => idx' = None
    end.
  Lemma permutes_Some {A} (idx : nat) (xs : list A) (idx' : option nat) (xs' : list A) :
    permutes (Some idx) xs idx' xs' →
    idx < length xs ∧
    ∃ idx'unwrap, idx' = Some idx'unwrap ∧ xs' !! idx'unwrap = xs !! idx.
  Admitted.
  Lemma permutes_Some_Some {A} (idx : nat) (xs : list A) (idx' : nat) (xs' : list A) :
    permutes (Some idx) xs (Some idx') xs' →
    idx < length xs ∧ xs' !! idx' = xs !! idx.
  Admitted.
  Lemma permutes_None {A} (xs : list A) (idx' : option nat) (xs' : list A) :
    permutes None xs idx' xs' →
    idx' = None ∧ permutes None xs None xs'.
  Admitted.
  Lemma permutes_insert {A} (idx : nat) (xs : list A) (idx' : nat) (xs' : list A) (x : A) :
    permutes (Some idx) xs (Some idx') xs' →
    permutes (Some idx) (<[idx:=x]>xs) (Some idx') (<[idx':=x]>xs').
  Admitted.
  Lemma permutes_cons {A} (idx sidx : nat) (xs : list A) (idx' sidx' : nat) (xs' : list A) (x : A) :
    sidx = S idx →
    sidx' = S idx' →
    permutes (Some idx) xs (Some idx') xs' →
    permutes (Some sidx) (x::xs) (Some sidx') (x::xs').
  Admitted.
  Lemma permutes_Some_None {A} (idx : nat) (xs : list A) (idx': nat) (xs' : list A) :
    permutes (Some idx) xs (Some idx') xs' →
    permutes None xs None xs'.
  Admitted.
  Lemma permutes_delete {A} (idx : nat) (xs : list A) (idx': nat) (xs' : list A) :
    permutes (Some idx) xs (Some idx') xs' →
    permutes None (delete idx xs) None (delete idx' xs').
  Admitted.
  Lemma permutes_mapping {A} (xs : list A) (idx': nat) (xs' : list A) :
    permutes None xs None xs' →
    idx' < length xs' →
    ∃ idx, permutes (Some idx) xs (Some idx') xs'.
  Admitted.

  (* TODO: lookup_lt_is_Some already exists *)
  Lemma lookup_lt_Some' {A} (i : nat) (xs : list A) :
    i < length xs → ∃ x, xs !! i = Some x.
  Admitted.

  Lemma delete_insert {A} (i : nat) (x : A) (xs : list A) :
    delete i (<[i:=x]> xs) = delete i xs.
  Admitted.

  Lemma wptp_reorder tp tid tp' tid' Φ :
    permutes tid tp tid' tp' →
    wptp (R:=R) H tid  tp  Φ -∗
    wptp (R:=R) H tid' tp' Φ.
  Proof.
    iIntros (Hperm) "Hwptp". iRevert (tid' tp' Hperm). iRevert (tid tp Φ) "Hwptp".
    iApply (wptp_iter _); first solve_proper.
    iModIntro. iIntros (tid tp Φ) "Hwptp". iIntros (tid' tp' Hperm).
    iEval (rewrite wptp_unfold /=).
    destruct tid as [tid|].
    - destruct (permutes_Some _ _ _ _ Hperm) as [Hidxbound [tid'' [-> Hcoincide]]].
      iDestruct (wptp_inversion with "Hwptp") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp')|[(%k&%Hidx&Hwptp')|[(%k&%Hidx&Hwptp')|[(%k&%Hidx&Hwptp')|(%A&%e&%k&%Hidx&HH)]]]]]".
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        done.
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        iMod "Hwptp'". iModIntro. iApply "Hwptp'". iPureIntro.
        by apply permutes_insert.
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        iMod "Hwptp'". iModIntro. iApply "Hwptp'". iPureIntro.
        eapply permutes_cons; eauto. by apply permutes_insert.
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        iModIntro. iSplit.
        + iDestruct "Hwptp'" as "[>Hwptp' _]". iApply "Hwptp'".
          iModIntro. iPureIntro.
          apply permutes_insert with (x := k ()) in Hperm.
          by eapply permutes_Some_None.
        + apply permutes_insert with (x := k()) in Hperm.
          apply permutes_Some_None in Hperm.
          clear -Hperm.
          iIntros (tid_' t Hidx_').
          apply permutes_mapping with (idx' := tid_') in Hperm; first last.
          { rewrite insert_length. by eapply lookup_lt_Some. }
          destruct Hperm as [tid_ Hperm].
          destruct (permutes_Some_Some _ _ _ _ Hperm) as [Hidxbound Hcoincide].
          iDestruct "Hwptp'" as "[_ Hwptp']".
          rewrite insert_length in Hidxbound. apply lookup_lt_Some' in Hidxbound as [t' Hidx_].
          by iApply "Hwptp'".
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        iModIntro. iSplit.
        + iDestruct "Hwptp'" as "[>Hwptp' _]". iApply "Hwptp'".
          iModIntro. iPureIntro. by eapply permutes_delete.
        + apply permutes_delete in Hperm. clear -Hperm. iIntros (tid' t' Hidx').
          apply permutes_mapping with (idx' := tid') in Hperm; first last.
          { by eapply lookup_lt_Some. } destruct Hperm as [tid_ Hperm'].
          destruct (permutes_Some_Some _ _ _ _ Hperm') as [Hidxbound Hcoincide].
          iDestruct "Hwptp'" as "[_ Hwptp']".
          rewrite Hcoincide in Hidx'. by iApply "Hwptp'".
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        iApply ihandler_mono; last done; last eauto.
        iIntros (a) "Hwptp". iApply "Hwptp". iPureIntro. by apply permutes_insert.
    - apply permutes_None in Hperm as [-> Hperm]. iIntros (tid' t' Hidx').
      apply permutes_mapping with (idx' := tid') in Hperm; first last. { by eapply lookup_lt_Some. }
      destruct Hperm as [tid Hperm].
      destruct (permutes_Some_Some _ _ _ _ Hperm) as [Hidxbound Hcoincide].
      rewrite Hcoincide in Hidx'.
      by iApply "Hwptp".
  Qed.

  Lemma wptp_reorder' tp tp' t tid Φ :
    wptp (R:=R) H (Some (S (length tp + tid))) (tp ++ t :: tp') Φ -∗
    wptp (R:=R) H (Some (S (length tp + tid))) (t :: tp ++ tp') Φ.
  Admitted.

  Lemma wptp_update tid tp Φ :
    (|={∅}=> wptp (R:=R) H tid tp Φ) -∗
    wptp (R:=R) H tid tp Φ.
  Admitted.

  Lemma wptp_IH_right_wptp tid tp Φ :
    wptpF H wptp_IH_right tid tp Φ -∗ wptp (R:=R) H tid tp Φ.
  Proof.
    iIntros "Hwptp". rewrite wptp_unfold /=. iApply wptpF_mono; last done. iModIntro. clear.
    iIntros (t tp Φ) "Hwptp". iDestruct "Hwptp" as "[$ _]".
  Qed.

  Lemma wptp_None tp Φ :
    (∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={⊤, ∅}=> wptp H (Some tid') tp Φ) -∗
    wptp (R:=R) H None tp Φ.
  (* TODO: Prove this. Maybe there is a simpler proof, but I was thinking of
  taking the existing induction template and tweaking it. Maybe the tweaked
  induction template can even use the existing one aside from the None case. *)
  Admitted.

  Lemma wptp_wptpIH' tid' tp' Φ :
    wptp H tid' tp' Φ -∗ wptp_IH_right tid' tp' Φ.
  Proof.
    generalize tid' tp' Φ.
    iApply (wptp_iter _); first solve_proper.
    iModIntro. clear tid' tp' Φ. iIntros (tid' tp' Φ) "Hwptp'".
    iSplit; first by iApply wptp_IH_right_wptp.
    destruct tid' as [tid'|].
    - iIntros (tp tid_app ->) "Hwptp".
      iEval (rewrite wptp_unfold /=).
      iDestruct (wptp_inversion with "Hwptp'") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|(%A&%e&%k&%Hidx&HH)]]]]]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        done.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iModIntro.
        rewrite insert_app_r. by iApply "Hwptp''".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. rewrite insert_app_r. iApply wptp_reorder'. iMod "Hwptp''".
        iDestruct "Hwptp''" as "[_ Hwptp'']".
        iApply "Hwptp''". { iPureIntro. lia. } done.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        iModIntro. iSplit.
        + iDestruct "Hwptp''" as "[>[_ [Hwptp'' _]] _]". rewrite insert_app_r.
          by iApply "Hwptp''".
        + clear. iIntros (new_tid t Hidx).
          apply lookup_app_Some in Hidx as [Hidx|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[>[Hwptp'' _] _]".
             rewrite insert_app_r. by iApply "Hwptp".
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". rewrite insert_app_r.
             iApply "Hwptp''"; eauto. iPureIntro. lia.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        iModIntro. iSplit.
        + iDestruct "Hwptp''" as "[>[_ [Hwptp'' _]] _]". rewrite delete_app_r.
          by iApply "Hwptp''".
        + clear. iIntros (new_tid t Hidx).
          rewrite delete_app_r in Hidx. rewrite delete_app_r.
          apply lookup_app_Some in Hidx as [Hidx|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[>[Hwptp'' _] _]". by iApply "Hwptp".
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''"; eauto. iPureIntro. lia.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. iMod "HH". iModIntro. iApply (ihandler_mono with "[Hwptp]"); last done.
        + iIntros (a) "[_ Hwptp']". rewrite insert_app_r. by iApply "Hwptp'".
        + eauto.
    - iSplit.
      { iIntros (tp) "Hwptp". iApply wptp_None. iIntros (tid' t' Hidx). rewrite /wptpF.
        apply lookup_app_Some in Hidx as [Hidx|[Hidx'bound Hidx']].
        - iMod ("Hwptp" $! _ _ Hidx) as "Hwptp". iApply "Hwptp". iApply wptp_None.
          iModIntro. clear. iIntros (tid t Hidx). by iMod ("Hwptp'" $! _ _ Hidx) as "[$ _]".
        - iMod ("Hwptp'" $! _ _ Hidx') as "Hwptp'". iApply "Hwptp'". { iPureIntro. lia. }
          iModIntro. clear. iIntros (tid t Hidx). by iSpecialize ("Hwptp" $! _ _ Hidx).
      }
      iIntros (tid tp) "Hwptp".
      iEval (rewrite wptp_unfold /=).
      iDestruct (wptp_inversion with "Hwptp") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|(%A&%e&%k&%Hidx&HH)]]]]]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        done.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iModIntro.
        rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
        iApply "Hwptp''". iEval (rewrite wptp_unfold /=).
        clear. iIntros (tid' t' Hidx'). iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'". iModIntro.
        iDestruct "Hwptp'" as "[$ _]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
        iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''".
        iEval (rewrite wptp_unfold /=).
        clear. iModIntro. iIntros (tid' t' Hidx'). iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'".
        iModIntro. iDestruct "Hwptp'" as "[$ _]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. iModIntro. iSplit.
        + iDestruct "Hwptp''" as "[>[_ [Hwptp'' _]] _]".
          rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
          iApply "Hwptp''". iModIntro. iApply wptp_None. clear. iIntros (tid' t' Hidx').
          iSpecialize ("Hwptp'" $! _ _ Hidx').
          iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
        + rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
          clear. iIntros (new_tid t Hidx).
          apply lookup_app_Some in Hidx as [Hidx|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']".
             iApply "Hwptp''"; first done.
             iEval (rewrite wptp_unfold /=). clear. iIntros (tid' t' Hidx').
             iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'". iModIntro.
             iDestruct "Hwptp'" as "[$ _]".
          ++ iDestruct "Hwptp''" as "[>[_ [_ Hwptp'']] _]". iApply "Hwptp''".
             { iPureIntro. rewrite insert_length.
               apply (Nat.le_add_sub (length tp) new_tid Hidx'bound). }
             iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'".
             iModIntro. by iDestruct "Hwptp'" as "[Hwptp' _]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. iModIntro. rewrite delete_app_l; last first. { by eapply lookup_lt_Some. }
        iSplit.
        + iDestruct "Hwptp''" as "[>[_ [Hwptp'' _]] _]".
          iApply "Hwptp''". iModIntro. iApply wptp_None. clear. iIntros (tid' t' Hidx').
          iSpecialize ("Hwptp'" $! _ _ Hidx').
          iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
        + clear. iIntros (new_tid t Hidx).
          apply lookup_app_Some in Hidx as [Hidx|[Hidx'bound Hidx']].
          ++ iDestruct "Hwptp''" as "[_ Hwptp'']". iApply "Hwptp''"; first done.
             iEval (rewrite wptp_unfold /=). clear. iIntros (tid' t' Hidx).
             iSpecialize ("Hwptp'" $! _ _ Hidx). iMod "Hwptp'". iModIntro.
             iDestruct "Hwptp'" as "[$ _]".
          ++ iDestruct "Hwptp''" as "[>[_ [_ Hwptp'']] _]". iApply "Hwptp''".
             { iPureIntro. apply (Nat.le_add_sub _ new_tid Hidx'bound). }
             iSpecialize ("Hwptp'" $! _ _ Hidx'). iMod "Hwptp'".
             iModIntro. by iDestruct "Hwptp'" as "[Hwptp' _]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_l_Some. }
        simpl. iMod "HH". iModIntro. iApply (ihandler_mono with "[Hwptp']"); last done.
        + iIntros (a) "[_ Hwptp]". rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
          iApply "Hwptp". iEval (rewrite wptp_unfold /=). clear.
          iIntros (tid' t' Hidx'). iSpecialize ("Hwptp'" $! _ _ Hidx').
          iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
        + eauto.
  Qed.

  Lemma wptp_wptpIH tid tp Φ :
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
    - iSplit.
      * iIntros (tp') "Hwptp'".
        iDestruct (wptp_wptpIH' with "Hwptp'") as "[_ Hwptp']". by iApply "Hwptp'".
      * iIntros (tp' tid' tid_app ->) "Hwptp'".
        iDestruct (wptp_wptpIH' with "Hwptp'") as "[_ Hwptp']". by iApply "Hwptp'".
  Qed.

  Lemma wptp_2_threads t t' Φ :
    wptp H None [t] Φ -∗
    wptp H (Some 0) [t'] Φ -∗
    wptp (R:=R) H (Some 1) [t; t'] Φ.
  Admitted.

  Lemma wp_wptp {Hseq : Sequential H} (t : itree (threadpoolE +' E) R) Φ :
    WPi t @ (threadpoolH ⊕ H); ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    wptp H (Some 0) [t] Φ.
  (* TODO: Prove this by giving a version of WPi that incorporates the full
  mask into the induction. Basically, whether the mask is full should be a part
  of the induction. Or maybe even generic over any mask. *)
  Proof.
    epose (G := (λ (masked : bool) (t : itree (threadpoolE +' E) R) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ Φ, (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
        if masked then
          wptp H None [t] Φ
        else
          wptp H (Some 0) [t] Φ
      )%I).
    iAssert (∀ t Φ, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ }} -∗ G false t Φ)%I as "Hgen"; last first.
    { iIntros "Hwp". iApply ("Hgen" with "Hwp"). eauto. }
    iApply (wpi_iter_masked (H := threadpoolH ⊕ H) G); first solve_proper.
    - iModIntro. clear -Hseq. iIntros (t Φ_fupd) "Hwp". iIntros (Φ) "Hwand".
      destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
      * rewrite wptp_unfold /wpiF /=.
        iExists _. iSplit. { iPureIntro. reflexivity. }
        by iApply "Hwand".
      * rewrite wptp_unfold /wptpF /wpiF /=.
        iExists _. iSplit. { iPureIntro. reflexivity. }
        simpl. by iApply "Hwp".
      * rewrite wptp_unfold /wptpF /wpiF /=.
        destruct e as [e|e].
        + iExists _. iSplit. { iPureIntro. reflexivity. }
          destruct e.
          ++ iMod "Hwp" as "[Hcurrent Hnew]". iApply (wptp_2_threads with "[Hnew]").
             +++ iApply wptp_None. iIntros (tid' t' Hidx). iMod "Hnew".
                 apply list_lookup_singleton_Some in Hidx as [-> _].
                 iApply "Hnew". iModIntro. by iIntros (r) "?".
             +++ by iApply "Hcurrent".
          ++ iModIntro. iSplit.
             +++ do 2 iMod "Hwp". iModIntro. iApply wptp_None. iIntros (tid' t' Hidx).
                 apply list_lookup_singleton_Some in Hidx as [-> _].
                 by iApply "Hwp".
             +++ iIntros (tid t Hidx).
                 apply list_lookup_singleton_Some in Hidx as [-> _].
                 do 3 iMod "Hwp". by iApply "Hwp".
          ++ iModIntro. iSplit.
             +++ do 2 iMod "Hwp". iModIntro. iApply wptp_None. by iIntros (tid' t' Hidx).
             +++ by iIntros (tid t Hidx).
        + iExists _. iSplit. { iPureIntro. reflexivity. }
          unshelve iDestruct (is_seq with "Hwp") as "Hwp".
          iApply (ihandler_mono with "[Hwand]"); last done; eauto.
          iIntros (a) "HG". by iApply "HG".
    - clear. iIntros "!>" (t Φ) "HG". iIntros (Φ') "Hwand". iApply wptp_None.
      iIntros (tid' t' Hidx'). apply list_lookup_singleton_Some in Hidx' as [-> _].
      iMod "HG". iModIntro. by iApply "HG".
  Qed.

  (* TODO: Why do I need to register this hint again here when I already did it
  in another section? *)
  Hint Resolve interleaves__mono : paco.

  Theorem wpi_interleaving' :
    ∀ tid' tp Φ,
    wptp (R:=R) H tid' tp Φ -∗
    ∀ tid interleaving,
      ⌜tid' = Some tid⌝ →
      ⌜interleaves tid tp interleaving⌝ →
      WPi interleaving @ H; ∅ {{ r, |={∅, ⊤}=> Φ r }}.
  Proof.
    iApply (wptp_iter _); first solve_proper.
    iIntros "!>" (tid' tp Φ) "Hwptp". iIntros (tid interleaving -> Hinter).
    iDestruct (wptp_inversion with "Hwptp") as "[(%r&%Hidx'&HΦ)|[(%tnext&%Hidx'&Hwptp')|[(%k&%Hidx'&Hwptp')|[(%k&%Hidx'&Hwptp')|[(%k&%Hidx'&Hwptp')|(%A&%e&%k&%Hidx'&HH)]]]]]".
    - apply interleaves_inversion_Ret with (r := r) in Hinter; last done.
      rewrite Hinter -wpi_ret' //.
    - iApply wpi_update. iMod "Hwptp'". iModIntro.
      apply interleaves_inversion_Tau with (t := tnext) in Hinter; last done.
      destruct Hinter as [interleaving' [Hinter ->]]. rewrite -wpi_tau. by iApply "Hwptp'".
    - iApply wpi_update. iMod "Hwptp'". iModIntro.
      apply interleaves_inversion_Vis_EFork with (k := k) in Hinter; last done.
      destruct Hinter as [interleaving' [Hinter ->]]. rewrite -wpi_tau. by iApply "Hwptp'".
    - iApply wpi_update. iDestruct "Hwptp'" as "[_ Hwptp']".
      apply interleaves_inversion_Vis_EYield with (k := k) in Hinter; last done.
      destruct Hinter as [interleaving' [tid' [Hinter ->]]]. rewrite -wpi_tau.
      assert (Hidx'' := interleaves_lookup _ _ _ Hinter).
      destruct Hidx'' as [t Hidx''].
      apply lookup_lt_Some in Hidx''. rewrite insert_length in Hidx''.
      apply lookup_lt_Some' in Hidx'' as [t' Hidx''].
      by iApply ("Hwptp'" $! tid').
    - iApply wpi_update. iDestruct "Hwptp'" as "[_ Hwptp']".
      apply interleaves_inversion_Vis_EKillThread with (k := k) in Hinter; last done.
      destruct Hinter as [interleaving' [tid' [Hinter ->]]]. rewrite -wpi_tau.
      assert (Hidx'' := interleaves_lookup _ _ _ Hinter).
      destruct Hidx'' as [t Hidx''].
      by iApply ("Hwptp'" $! tid').
    - iApply wpi_update. iMod "HH". iModIntro.
      apply interleaves_inversion_Vis with (k := k) (e := e) in Hinter; last done.
      destruct Hinter as [interleaving' [Hinter' ->]]. iApply wpi_vis.
      iModIntro. iApply ihandler_mono; last done.
      * iIntros (a) "Hwp". iApply wpi_update_post. by iApply "Hwp".
      * iIntros "!>" (t). by iIntros "?".
  Qed.

  (** Adequacy for [threadpoolH ⊕ H]. This says that if you can prove the
  weakest precondition an [itree (threadpoolE +' E) R] then you get weakest
  preconditions for every interleaving [itree E R]. *)
  Corollary wpi_interleaving `{!Sequential H}
    (concurrent : itree (threadpoolE +' E) R)
    (interleaving : itree E R)
    (Φ : R → iProp Σ) :
    interleaves 0 [concurrent] interleaving →
    WPi concurrent @ threadpoolH ⊕ H; ⊤ {{ Φ }} -∗
    WPi interleaving @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "%Hinter Hwp". iApply wpi_clear_mask.
    iEval (rewrite -wpi_clear_mask) in "Hwp". iMod "Hwp".
    iDestruct (wp_wptp with "Hwp") as "Hwptp".
    iDestruct (wpi_interleaving' with "Hwptp") as "Hwp".
    by iApply "Hwp".
  Qed.
End threadpool_adequacy.
