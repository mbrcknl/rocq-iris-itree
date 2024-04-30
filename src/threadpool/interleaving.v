From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Import fixpoint.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree.threadpool Require Import handler.
From ITree Require Import ITree.
From ITree Require Import Eq.
From stdpp Require Import list.
From Paco Require Import paco.
From Paco Require Import paco3.

(** The interleaving relation. *)
Section interleaving.
  Context {E : Type → Type} {R : Type}.

  (** The interleaving relation. This relation encodes what it means for an
  [itree E R] to refine an itree [itree (threadpoolE +' E) R] that can emit
  events [threadpoolE] regarding concurrency. *)

  (** The recuirsion template for the interleaving relation, without enforcing
  [tp !! tid = Some t]. *)
  Variant interleavesF
    (** The recursive instance of the interleaving relation (doing bound
    checks). *)
    (interleaves : nat → list (itree (threadpoolE +' E) R) → itree E R → Prop)
    (** The thread ID [tid] of the currently executing thread. *)
    : nat
    (** The thread [t] that is currently being executed. *)
    → itree' (threadpoolE +' E) R
    (** The threadpool [tp] (supposed to satisfy [tp !! tid = Some t]) *)
    → list (itree (threadpoolE +' E) R)
    (** The interleaved [itree]. *)
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
  (** The [EYield] event yields control to another thread. The
  interleaved [itree] takes a silent step in place of the [EYield]. *)
  | Yield current_tid tp k new_current_tid interleaving' :
    interleaves new_current_tid (<[current_tid := k ()]>tp) interleaving' →
    interleavesF interleaves current_tid (VisF (inl1 EYield) k) tp (TauF interleaving')
  (** The [EFork] event adds a new thread to the threadpool and continues
  executing the current thread. The interleaved [itree] takes a silent step in
  place of the [EFork]. *)
  | Fork current_tid tp k interleaving' :
    interleaves current_tid (<[current_tid := k CurrentThread]>tp ++ [k NewThread]) interleaving' →
    interleavesF interleaves current_tid (VisF (inl1 EFork) k) tp (TauF interleaving').
  Hint Constructors interleavesF : iris_itree.
  (** The recuirsion template for the interleaving relation. *)
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

  Lemma interleaves_lookup tid tp interleaving :
    interleaves tid tp interleaving →
    ∃ t, tp !! tid = Some t.
  Proof.
    intros Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]]. eauto.
  Qed.

  (** Inversion lemmata. *)

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
    ∃ interleaving', interleaves tid (<[tid:=k CurrentThread]>tp ++ [k NewThread ]) interleaving' ∧ interleaving ≅ Tau interleaving'.
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
End interleaving.

(* Our objective is to prove the threadpool adequacy theorem [threadpool_adequacy].
For this, we need an induction principle for an entire threadpool as opposed to
for a weakest precondition of a single thread (since this thread could spawn
new threads). Therefore, it is necessary to define a weakest precondition for
threadpools. However, this is only a necessity for the proof. It does not
affect the statement of adequacy.

The weakest precondition for a threadpool [wptp] takes a threadpool and a
currently executing thread. A key technical idea in proving the threadpool
adequacy theorem is to also have the option of control being at the "outside
world", that is, that the threadpool is currently suspended and waiting to
be resumed. (This is necessary to state e.g. [wptp_merge_r], which is a lemma
necessary to prove the threadpool adequacy theorem.) This is represented by
having [wptp] take an [option nat] which is either [Some tid] for
representing that the thread with thread ID [tid] is currently executing or
[None] representing that the threadpool is suspended.

With (a carefully chosen) definition of [wptp], the proof of
[threadpool_adequacy] breaks into two implications:

(1) [wp_wptp] which relates [WPi] with the threadpool handler to [wptp], and
(2) [wptp_wp], which is a version of [threadpool_adequacy] where the hypothesis
    is a [wptp] instead of a [WPi].
*)
Section wptp.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.

  (** The definition of the weakest precondition, prior to taking the least
  fixpoint. *)
  Definition wptpF (H : iHandler Σ E)
    (wptp : leibnizO (option nat) → leibnizO (list (itree (threadpoolE +' E) R)) → (R -d> iPropO Σ) → iPropO Σ) :
            leibnizO (option nat) → leibnizO (list (itree (threadpoolE +' E) R)) → (R -d> iPropO Σ) → iPropO Σ :=
    λ tid tp Φ, (
      match tid with
      (** The threadpool is suspended but can be resumed at any thread in it
      after opening up invariants. *)
      | None => ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={⊤, ∅}=> wptp (Some tid') tp Φ
      (** [tid] is the thread ID for the currently executing thread. *)
      | Some tid => ∃ t, ⌜tp !! tid = Some t⌝ ∧ |={∅}=>
        match observe t with
        (** Upon return, we close down all invariants and verify the
        postcondition. *)
        | RetF r  => |={∅, ⊤}=> Φ r
        (** We simply skip over silent steps. *)
        | TauF t' => wptp (Some tid) (<[tid := t']>tp) Φ
        | @VisF _ _ _  A (inl1 e) k =>
          (** Trick: To have Coq not complain about dependent types, it is important
          to introduce the dependently typed binders sufficiently late. This is why
          we put a lambda after each arm, as opposed to on the outside. *)
          (match (e : threadpoolE A) with
          | EYield => λ k,
            (
            (** [EYield] can yield control to the outside world (in which case all
            invariants must be closed so that they can be accessed when resuming
            another suspended threadpool) or ... *)
            (|={∅, ⊤}=> wptp None (<[tid:=k ()]>tp) Φ)
            (** ... to another thread in the threadpool. *)
            ∧ ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={∅}=> wptp (Some tid') (<[tid:=k ()]>tp) Φ
            )
          | EFork => λ (k : thread → _),
            (** Newly forked threads are just prepended to the threadpool. *)
            wptp (Some tid) (<[tid:=k CurrentThread]>tp ++ [k NewThread]) Φ
          end : (A → _) → _) k
        (** Non-threadpool events are handled using the handler [H]. *)
        | VisF (inr1 e) k => H _ e
            (λ a, wptp (Some tid) (<[tid:=k a]>tp) Φ)
            (λ a, False)
        end
      end
    )%I.
  Definition wptpF' (H : iHandler Σ E)
    (wptp : leibnizO (option nat) * leibnizO (list (itree (threadpoolE +' E) R)) * (R -d> iPropO Σ) → iPropO Σ) :
            leibnizO (option nat) * leibnizO (list (itree (threadpoolE +' E) R)) * (R -d> iPropO Σ) → iPropO Σ :=
    λ pair, match pair with (t, tp, Φ) => wptpF H (curry3 wptp) t tp Φ end.

  Global Instance wptpF_ne n H :
    Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) (wptpF H).
  Proof.
    intros wp1 wp2 Hwptp tid1 tid2 <- tp1 tp2 <- Φ1 Φ2 HΦ.
    rewrite /wptpF'/wptpF. do 2 f_equiv.
    - rewrite /curry3. do 4 f_equiv.
      * by f_equiv.
      * by apply Hwptp.
      * destruct e as [e'|e'].
        + destruct e'.
          ++ by apply Hwptp.
          ++ repeat f_equiv; by apply Hwptp.
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
      * destruct e as [e|e].
        + destruct e.
          ++ by iApply "Hwand".
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

  Definition wptp (H : iHandler Σ E) (tid : option nat) (tp : list (itree (threadpoolE +' E) R)) (Φ : R → iPropO Σ) : iProp Σ :=
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

  Lemma wptp_bound H tid tp Φ :
    wptp H (Some tid) tp Φ -∗
    ⌜tid < length tp⌝.
  Proof.
    iIntros "Hwptp". rewrite wptp_unfold. iDestruct "Hwptp" as "[%t [%Hidx _]]".
    by apply lookup_lt_Some in Hidx.
  Qed.
End wptp.

(** Induction and inversion principles for [wptp]. *)
Section wptp_induction.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ} {H : iHandler Σ E}.

  Lemma wptp_ind (G : option nat → list (itree (threadpoolE +' E) R) → (R -d> iPropO Σ) → iPropO Σ):
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

  Lemma wptp_iter (G : option nat → list (itree (threadpoolE +' E) R) → (R -d> iPropO Σ) → iPropO Σ) :
    (∀ tid tp, NonExpansive (G tid tp)) →
    (□ ∀ tid tp Φ, wptpF H G tid tp Φ -∗ G tid tp Φ) -∗
    ∀ tid tp Φ, wptp H tid tp Φ -∗ G tid tp Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply wptp_ind. iIntros "!>" (t tp Φ) "Hwptp".
    iApply "HPre". iApply (wptpF_mono with "[] Hwptp").
    iIntros "!>" (???) "[? _]". by iFrame.
  Qed.

  (* TODO: Commit to the extensionality axiom in [itree.v] and remove
     unnecessary [Proper] proofs, and use equality throughout. *)
  Lemma wptp_inversion tid (tp : list (itree (threadpoolE +' E) R)) Φ G :
    wptpF H G (Some tid) tp Φ -∗
    ( (∃ r, ⌜tp !! tid = Some (Ret r)⌝ ∧ (|={∅,⊤}=> Φ r))
    ∨ (∃ t', ⌜tp !! tid = Some (Tau t')⌝ ∧ |={∅}=> G (Some tid) (<[tid:=t']>tp) Φ)
    ∨ (∃ k, ⌜tp !! tid = Some (Vis (inl1 EFork) k)⌝ ∧
      |={∅}=> G (Some tid) (<[tid:=k CurrentThread]>tp ++ [k NewThread]) Φ
      )
    ∨ (∃ k, ⌜tp !! tid = Some (Vis (inl1 EYield) k)⌝ ∧ (
      (|={∅, ⊤}=> G None (<[tid:=k ()]>tp) Φ)
      ∧ ∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={∅}=> G (Some tid') (<[tid:=k ()]>tp) Φ
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
      * iRight. iRight. iRight. iRight. iExists _, e, k. iSplit; first done.
        rewrite /wptpF /= //.
  Qed.
End wptp_induction.

(** In order to prove [wp_wptp], it is necessary to have an tailored induction
principle [wpi_iter_masked] for [WPi] allowing not just [∅] but also [⊤] mask.
Technically speaking, this is because depending on whether we are in the case
of [tid] being [None] (outside world has control) or [Some tid'] (thread [tid']
has control), the mask in the hypothesis has to be [⊤] or [∅] respectively. *)
Section wpi_masked_ind.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.

  (** Recursive template whose fixpoint is [|={⊤, ∅}=> WPi t @ H; ∅ {{ Φ }}] when
  [masked = true] and [WPi t @ H; ∅ {{ Φ }}] when [masked = false]. *)
  Definition wpiF_masked (H : iHandler Σ E)
    (wpi : leibnizO bool → leibnizO (itree E R) → (R -d> iPropO Σ) → iPropO Σ) :
           leibnizO bool → leibnizO (itree E R) → (R -d> iPropO Σ) → iPropO Σ :=
    (λ masked t Φ, if masked then
        (* The case where [masked = true], we just do a mask changing update
        and call the unmasked case recursively. *)
        |={⊤, ∅}=> wpi false t Φ
      else
        (* The unmasked case just makes use of the recursion template used to
        define [WPi]. *)
        wpiF H (wpi false) t Φ
    )%I.
  Definition wpiF_masked' (H : iHandler Σ E)
    (wpi : leibnizO bool * leibnizO (itree E R) * (R -d> iPropO Σ) → iPropO Σ) :
           leibnizO bool * leibnizO (itree E R) * (R -d> iPropO Σ) → iPropO Σ :=
    λ pair, let (rest, Φ) := pair in let (masked, t) := rest in wpiF_masked H (curry3 wpi) masked t Φ.

  Global Instance wpiF_masked_ne n H :
    Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) (wpiF_masked H).
  Proof.
    intros wp1 wp2 Hwp m1 m2 <- t1 t2 <- Φ1 Φ2 HΦ. rewrite /wpiF_masked.
    do 2 f_equiv; eauto. by apply Hwp.
  Qed.
  Global Instance wpiF_masked_ne' n H :
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) (wpiF_masked' H).
  Proof.
    intros wp1 wp2 Hwp [[m1 t1] Φ1] [[m2 t2] Φ2] [[Hm Ht] HΦ]. rewrite /wpiF'.
    apply wpiF_masked_ne; eauto. intros. by f_equiv.
  Qed.

  Lemma wpiF_masked_mono H wp1 wp2:
    ⊢ □ (∀ masked t Φ, wp1 masked t Φ -∗ wp2 masked t Φ)
    → ∀ masked t Φ, wpiF_masked H wp1 masked t Φ -∗ wpiF_masked H wp2 masked t Φ.
  Proof.
    iIntros "#Hwand" (masked t Φ) "Hwp". rewrite /wpiF_masked. destruct masked.
    - by iApply "Hwand".
    - iApply wpiF_mono; eauto.
  Qed.
  Lemma wpiF_masked_mono' H wp1 wp2:
    ⊢ □ (∀ masked t Φ, wp1 (masked, t, Φ) -∗ wp2 (masked, t, Φ))
    → ∀ masked t Φ, wpiF_masked' H wp1 (masked, t, Φ) -∗ wpiF_masked' H wp2 (masked, t, Φ).
  Proof.
    rewrite /wpiF_masked'. iApply wpiF_masked_mono.
  Qed.

  Global Instance wpi_masked_pre_monotone H :
    BiMonoPred (λ wp_itree, wpiF_masked' H wp_itree).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([[??]?]) "Hsim" => /=. iApply wpiF_masked_mono'; [|done].
      iIntros "!>" (???) "HΠ". by iApply ("Hinner" $! (_, _)).
    - intros wpi HneΦ n [t Φ] [t' Φ'] [-> HΦ]. f_equiv. simpl. by f_equiv.
  Qed.

  Definition wpi_masked (H : iHandler Σ E) (masked : bool) (t : itree E R) (Φ : R → iProp Σ) : iProp Σ :=
    bi_least_fixpoint (wpiF_masked' H) (masked, t, Φ).

  Lemma wpi_without_mask H (t : itree E R) Φ :
    WPi t @ H; ∅ {{ Φ }} -∗ wpi_masked H false t Φ.
  Proof.
    iRevert (t Φ). iApply wpi_iter. { intros t n Φ1 Φ2 HΦ. by apply least_fixpoint_ne. }
    iIntros "!>" (t Φ) "Hwp". iEval (rewrite /wpi_masked least_fixpoint_unfold).
    iApply wpiF_mono; last done. clear. by iIntros "!>" (t Φ) "Hwp".
  Qed.

  Lemma wpi_iter_masked' (H : iHandler Σ E) (G : bool → itree E R → (R -d> iPropO Σ) → iPropO Σ):
    (∀ b t, NonExpansive (G b t)) →
    (□ ∀ t Φ, wpiF H (G false) t Φ -∗ G false t Φ) -∗
    (□ ∀ t Φ, (|={⊤, ∅}=> G false t Φ) -∗ G true t Φ) -∗
    ∀ masked t Φ, wpi_masked H masked t Φ -∗ G masked t Φ.
  Proof.
    iIntros (Hne) "#Hnomask #Hmask". rewrite /wpi_masked.
    iAssert (∀ (x : leibnizO bool * leibnizO (itree E R) * (R -d> iPropO Σ)), bi_least_fixpoint (wpiF_masked' H) x -∗ G (fst (fst x)) (snd (fst x)) (snd x))%I as "Hgen"; last first.
    { iIntros (masked t Φ) "Hwp". by iApply ("Hgen" $! (masked, t, Φ)). }
    unshelve iApply (least_fixpoint_iter (wpiF_masked' H) (λ x, G (fst (fst x)) (snd (fst x)) (snd x))).
    { iIntros (n [[masked1 t1] Φ1] [[masked2 t2] Φ2] [[<- <-] HΦ]). by f_equiv. }
    iModIntro. iIntros ([[[|] t] Φ]) "Hwp"; simpl.
    - by iApply "Hmask".
    - by iApply "Hnomask".
  Qed.

  Lemma wpi_iter_masked (H : iHandler Σ E) (G : bool → itree E R → (R -d> iPropO Σ) → iPropO Σ):
    (∀ b t, NonExpansive (G b t)) →
    (□ ∀ t Φ, wpiF H (G false) t Φ -∗ G false t Φ) -∗
    (□ ∀ t Φ, (|={⊤, ∅}=> G false t Φ) -∗ G true t Φ) -∗
    ∀ t Φ, WPi t @ H; ∅ {{ Φ }} -∗ G false t Φ.
  Proof.
    iIntros (Hne) "#Hnomask #Hmask". iIntros (t Φ) "Hwp".
    iApply (wpi_iter_masked' H G with "Hnomask Hmask").
    by iApply wpi_without_mask.
  Qed.
End wpi_masked_ind.

(** List lemmata. *)
Section list.
  Lemma singleton_or_more {A} (xs : list A) idx i :
    xs !! idx = Some i →
    ((idx = 0 ∧ xs = [i]) ∨ (length xs > 1 ∧ xs !! idx = Some i)).
  Proof.
    intros Hidx.
      destruct (decide (length xs = 1)) as [Hlen|Hlen].
      - left. destruct xs as [|t ts]; first discriminate.
        simpl in Hlen. injection Hlen as Hlen. apply nil_length_inv in Hlen as ->.
        destruct idx; last discriminate. simpl in Hidx. injection Hidx as ->.
        done.
      - right.
        destruct xs; first discriminate.
        destruct xs. { simpl in Hlen. contradiction. }
        simpl. split.
        * lia.
        * done.
  Qed.

  Lemma lookup_app_r_Some {A} (xs ys : list A) y n :
    ys !! n = Some y →
    (xs ++ ys) !! (length xs + n) = Some y.
  Proof.
    intros Hidx. rewrite lookup_app_r; last lia.
    by replace (length xs + n - length xs) with n by lia.
  Qed.

  Lemma delete_app_r {A} (xs ys : list A) n :
    delete (length xs + n) (xs ++ ys) = xs ++ delete n ys.
  Proof.
    rewrite !delete_take_drop.
    replace (S (length xs + n)) with (length xs + (1 + n)) by lia.
    rewrite take_app_add' // drop_app_add' // -app_assoc //.
  Qed.
  Lemma delete_app_l {A} (xs ys : list A) n :
    n < length xs →
    delete n (xs ++ ys) = delete n xs ++ ys.
  Proof.
    intros Hlt.
    rewrite !delete_take_drop take_app_le; last by lia.
    rewrite drop_app_le; last by lia.
    rewrite app_assoc //.
  Qed.

  Lemma app_lookup {A} (idx : nat) (xs ys : list A) :
    ((xs ++ ys) !! idx = None) ∨
    (∃ x, (xs ++ ys) !! idx = xs !! idx ∧ xs !! idx = Some x) ∨
    (∃ y, (xs ++ ys) !! idx = ys !! (idx - length xs) ∧ ys !! (idx - length xs) = Some y).
  Proof.
    destruct (idx <? length xs) eqn:Heq.
    - apply Nat.ltb_lt in Heq as Hbound. right. left.
      assert (Hbound' := Hbound).
      apply lookup_lt_is_Some_2 in Hbound as [x Hidx].
      eexists. by split; first by apply lookup_app_l.
    - apply Nat.ltb_nlt in Heq as Hbound.
      destruct (idx <? length xs + length ys) eqn:Heq'.
      * apply Nat.ltb_lt in Heq' as Hbound'. right. right.
        rewrite -app_length in Hbound'.
        apply lookup_lt_is_Some_2 in Hbound' as [x Hidx].
        eexists. split.
        + apply lookup_app_r. lia.
        + rewrite -lookup_app_r; first done. lia.
      * apply Nat.ltb_nlt in Heq' as Hbound'. left. apply lookup_ge_None_2. rewrite app_length. lia.
  Qed.

  Lemma zip_length {A B} (xs : list A) (ys : list B) :
    length (zip xs ys) = min (length xs) (length ys).
  Proof. apply zip_with_length. Qed.

  Lemma zip_lookup {A B} (xs : list A) (a : A) (ys : list B) (b : B) (idx : nat) :
    (zip xs ys) !! idx = Some (a, b) →
    xs !! idx = Some a ∧ ys !! idx = Some b.
  Proof.
    rewrite lookup_zip_with. intros Hidx.
    destruct (xs !! idx) as [x|]; last done.
    destruct (ys !! idx) as [y|]; last done.
    by injection Hidx as -> ->.
  Qed.

  Lemma zip_insert {A B} (xs : list A) (a : A) (ys : list B) (b : B) (idx : nat) :
    <[idx:=(a, b)]>(zip xs ys) = zip (<[idx:=a]>xs) (<[idx:=b]>ys).
  Proof. apply insert_zip_with. Qed.

  Lemma seq_0_insert (idx len : nat) :
    <[idx := idx]>(seq 0 len) = seq 0 len.
  Proof.
    apply list_eq. intros i.
    destruct (i <? len) eqn:Hineq.
    - apply Nat.ltb_lt in Hineq.
      destruct (i =? idx) eqn:Heq.
      * apply Nat.eqb_eq in Heq as ->.
        rewrite list_lookup_insert; last rewrite seq_length //. rewrite lookup_seq_lt //.
      * apply Nat.eqb_neq in Heq. rewrite list_lookup_insert_ne //.
    - apply Nat.ltb_ge in Hineq.
      rewrite !lookup_ge_None_2 //. { rewrite seq_length //. }
      rewrite insert_length seq_length //.
  Qed.

  Lemma nin_cons {A} (xs : list A) (x x' : A) :
    x' ∉ x :: xs → x' ∉ xs.
  Proof.
    intros Hnin. intros Hin. unshelve eassert (Hnin := Hnin _). { by constructor. } done.
  Qed.

  Definition enumerate_from {A} (n : nat) (xs : list A) : list (nat * A) :=
    zip (seq n (length xs)) xs.
  Definition enumerate {A} (xs : list A) : list (nat * A) :=
    enumerate_from 0 xs.

  Lemma enumerate_lookup {A} (xs : list A) (idx idx' : nat) (x : A) :
    enumerate xs !! idx = Some (idx', x) → idx = idx' ∧ xs !! idx = Some x.
  Proof.
    intros Hidx. rewrite /enumerate/enumerate_from in Hidx. apply zip_lookup in Hidx as [Hseq Hidx].
    by apply lookup_seq in Hseq as [Heq Hbound].
  Qed.

  Lemma enumerate_from_cons {A} (n : nat) (x : A) (xs : list A) :
    enumerate_from n (x :: xs) = (n, x) :: enumerate_from (S n) xs.
  Proof. done. Qed.

  Lemma enumerate_from_fst {A} (n : nat) (xs : list A) :
    fst <$> enumerate_from n xs = seq n (length xs).
  Proof.
    rewrite /enumerate_from fst_zip // seq_length //.
  Qed.

  Lemma enumerate_from_snd {A} (n : nat) (xs : list A) :
    snd <$> enumerate_from n xs = xs.
  Proof.
    rewrite /enumerate_from snd_zip // seq_length //.
  Qed.

  Lemma enumerate_lookup_fst {A} (xs : list A) (idx: nat) :
    idx < length xs →
    fst <$> enumerate xs !! idx = Some idx.
  Proof.
    intros Hbound. rewrite -list_lookup_fmap /enumerate enumerate_from_fst lookup_seq //.
  Qed.

  Lemma enumerate_length {A} (xs : list A) :
    length (enumerate xs) = length xs.
  Proof.
    rewrite /enumerate zip_length seq_length. apply Nat.min_id.
  Qed.

  Lemma enumerate_insert {A} (xs : list A) (i : nat) (x : A) :
    enumerate (<[i:=x]>xs) = <[i:=(i, x)]>(enumerate xs).
  Proof.
    rewrite zip_insert seq_0_insert /enumerate/enumerate_from insert_length //.
  Qed.

  Lemma enumerate_bound {A} (xs : list A) (i : nat) (x : A) :
    (i, x) ∈ enumerate xs → i < length xs.
  Proof.
    by intros [idx [<- Hbound%lookup_lt_Some]%enumerate_lookup]%elem_of_list_lookup_1.
  Qed.

  Lemma enumerate_from_NoDup {A} (n : nat) (xs : list A) :
    NoDup (fst <$> enumerate_from n xs).
  Proof.
    induction xs.
    - constructor.
    - rewrite enumerate_from_fst. apply NoDup_seq.
  Qed.
  Lemma enumerate_NoDup {A} (xs : list A) :
    NoDup (fst <$> enumerate xs).
  Proof.
    rewrite enumerate_from_fst. apply NoDup_seq.
  Qed.

  Lemma enumerate_app {A} (xs xs' : list A) :
    enumerate (xs ++ xs') = enumerate xs ++ zip (seq (length xs) (length xs')) xs'.
  Proof.
    rewrite /enumerate/enumerate_from -zip_with_app.
    - f_equiv. rewrite app_length. apply seq_app.
    - rewrite seq_length //.
  Qed.

  Lemma enumerate_from_fmap_offset A (xs : list A) n m :
    (λ i : nat * A, let (n, x) := i in (m + n, x)) <$> enumerate_from n xs
    =
    enumerate_from (m + n) xs.
  Proof.
    revert n.
    induction xs as [|x xs' IH]; first done.
    intros n.
    rewrite !enumerate_from_cons fmap_cons. f_equiv.
    replace (S (m + n)) with (m + S n) by lia.
    by rewrite IH.
  Qed.
End list.

(** In order to state the reordering principle [wptp_reorder], it is necessary
to have a theory of "pointed" permutations, that is, we want to know not just
that some list is a permutation of another list but also track that a specified
item of the former list corresponds to a specified item of the latter. *)
Section pointed_permutations.
  (** Inserting into "uniquely labeled" (meaning that [NoDup (fst <$> xs)])
  lists. *)

  Lemma NoDup_insert_fmap {A} (xs : list (nat * A)) (idx idx' : nat) (x' : A) :
    NoDup (fst <$> xs) →
    fst <$> xs !! idx' = Some idx →
    <[idx':=(idx, x')]>xs = (λ i, if fst i =? idx then (idx, x') else i) <$> xs.
  Proof.
    intros Hdup. remember (fst <$> xs) as xs1. revert xs Heqxs1 idx idx'. induction Hdup as [|n ns Hin Hdup IH].
    - intros xs Heq idx idx' Hidx. rewrite -list_lookup_fmap -Heq in Hidx. discriminate.
    - intros xs Heq idx idx' Hidx. destruct xs as [|x xs]; first discriminate.
      rewrite fmap_cons in Heq. rewrite fmap_cons.
      destruct idx' as [|idx'].
      * etransitivity. { by simpl. }
        injection Hidx as <-. rewrite Nat.eqb_refl. f_equiv.
        injection Heq as <- ->. clear -Hin. induction xs as [|x xs IH].
        + done.
        + rewrite fmap_cons. rewrite fmap_cons in Hin. destruct (x.1 =? n) as [|] eqn:Heq.
          ++ apply Nat.eqb_eq in Heq as <-.
             by unshelve eassert (Hin := Hin _); first constructor.
          ++ f_equiv. apply IH. intros Hin'.
             by unshelve eassert (Hin := Hin _); first by constructor.
      * etransitivity. { by simpl. }
        injection Heq as <- ->. simpl in Hidx.
        destruct (n =? idx) as [|] eqn:Heq.
        + apply Nat.eqb_eq in Heq as <-.
          rewrite -list_lookup_fmap in Hidx.
          apply elem_of_list_lookup_2 in Hidx. contradiction.
        + f_equiv. by apply IH.
  Qed.
  Lemma enumerate_insert_fmap {A} (xs : list A) (enumerated_xs' : list (nat * A)) (idx idx' : nat) (x' : A) :
    enumerate xs ≡ₚ enumerated_xs' →
    fst <$> enumerated_xs' !! idx' = Some idx →
    <[idx':=(idx, x')]>enumerated_xs' = (λ i, if fst i =? idx then (idx, x') else i) <$> enumerated_xs'.
  Proof.
    intros Hperm Hidx. apply NoDup_insert_fmap; last done. rewrite -Hperm. apply enumerate_NoDup.
  Qed.

  (** Deleting from uniquely labeled lists. *)

  Definition remove {A} (idx : nat) (xs : list (nat * A)) : list (nat * A) :=
    mbind (λ i, if fst i =? idx then [] else if fst i <? idx then [(fst i, snd i)] else [(fst i - 1, snd i)]) xs.
  Global Instance remove_proper {A} idx :
    Proper ((≡ₚ) ==> (≡ₚ)) (remove (A:=A) idx).
  Proof.
    intros xs xs' Hperm. rewrite /remove Hperm //.
  Qed.
  Lemma NoDup_remove_id {A} (xs : list (nat * A)) (idx : nat) :
    NoDup (fst <$> xs) →
    idx ∉ fst <$> xs →
    snd <$> remove idx xs = snd <$> xs.
  Proof.
    intros Hdup Hnin. induction xs as [|x xs IH]; first done.
    rewrite fmap_cons /=. destruct (x.1 =? idx) eqn:Heq.
    - apply Nat.eqb_eq in Heq as <-. rewrite fmap_cons in Hnin.
      unshelve eassert (Hnin := Hnin _). { constructor. } done.
    - apply Nat.eqb_neq in Heq. rewrite fmap_app. apply nin_cons in Hnin.
      inversion Hdup. destruct (x.1 <? idx); simpl; f_equiv; by apply IH.
  Qed.
  Lemma NoDup_delete_remove {A} (xs : list (nat * A)) (idx idx' : nat) :
    NoDup (fst <$> xs) →
    fst <$> xs !! idx' = Some idx →
    snd <$> remove idx xs = delete idx' (snd <$> xs).
  Proof.
    intros Hdup Hidx. revert idx idx' Hidx. induction xs as [|x xs IH]; first done.
    intros idx idx' Hidx. destruct idx' as [|idx'].
    - rewrite -list_lookup_fmap in Hidx. injection Hidx as <-. simpl.
      rewrite Nat.eqb_refl app_nil_l. inversion Hdup. by apply NoDup_remove_id.
    - rewrite fmap_cons. etransitivity; last simpl; first done.
      simpl. destruct (x.1 =? idx) eqn:Heq.
      * apply Nat.eqb_eq in Heq as <-.
        rewrite -list_lookup_fmap fmap_cons lookup_cons in Hidx.
        apply elem_of_list_lookup_2 in Hidx. inversion Hdup. contradiction.
      * apply Nat.eqb_neq in Heq. rewrite fmap_app.
        inversion Hdup. destruct (x.1 <? idx); simpl; f_equiv; by apply IH.
  Qed.
  Lemma NoDup_remove_length {A} (xs : list (nat * A)) (idx idx' : nat) :
    NoDup (fst <$> xs) →
    fst <$> xs !! idx' = Some idx →
    length (remove idx xs) = length xs - 1.
  Proof.
    intros Hdup Hidx. rewrite -(fmap_length snd) (NoDup_delete_remove _ _ idx') // length_delete.
    - rewrite fmap_length //.
    - rewrite list_lookup_fmap. by destruct (xs !! idx').
  Qed.

  (** Deleting from [enumerate_from] and [enumerate]. *)

  Lemma enumerate_from_delete_outside_range {A} (xs : list A) (idx idx' : nat) :
    idx' < S idx →
    enumerate_from idx xs = remove idx' (zip (seq (S idx) (length xs)) xs).
  Proof.
    revert idx. induction xs as [|x xs IH]; first done. intros idx Hineq.
    rewrite enumerate_from_cons. destruct idx.
    - apply Nat.lt_1_r in Hineq as ->. simpl. f_equiv. rewrite IH //. lia.
    - simpl. destruct idx' as [|[|idx']].
      * replace (S (S idx) <? 0) with false; first last.
        { symmetry. apply Nat.ltb_nlt. lia. }
        simpl. f_equiv. apply IH. lia.
      * replace (S (S idx) <? 0) with false; first last.
        { symmetry. apply Nat.ltb_nlt. lia. }
        simpl. f_equiv. apply IH. lia.
      * replace (idx =? idx') with false; first last.
        { symmetry. apply Nat.eqb_neq. lia. }
        replace (S (S idx) <? S (S idx')) with false; first last.
        { symmetry. apply Nat.ltb_nlt. lia. }
        simpl. f_equiv. apply IH. lia.
  Qed.
  Lemma enumerate_from_delete {A} (xs : list A) (idx idx' : nat) (n : nat) :
    idx' = idx + n →
    enumerate_from n (delete idx xs) = remove idx' (enumerate_from n xs).
  Proof.
    intros ->. revert n idx. induction xs as [|x xs IH]; first done.
    destruct idx as [|idx].
    - simpl. rewrite Nat.eqb_refl app_nil_l. apply enumerate_from_delete_outside_range. lia.
    - simpl. destruct (n =? S (idx + n)) eqn:Heq.
      * apply Nat.eqb_eq in Heq. lia.
      * apply Nat.eqb_neq in Heq. destruct (n <? S (idx + n)) eqn:Hineq.
        + apply Nat.ltb_lt in Hineq.
          rewrite enumerate_from_cons. simpl. f_equiv. rewrite IH.
          by replace (idx + S n) with (S (idx + n)) by lia.
        + apply Nat.ltb_nlt in Hineq. lia.
  Qed.
  Lemma enumerate_delete {A} (xs : list A) (enumerated_xs' : list (nat * A)) (idx idx' : nat) :
    fst <$> enumerated_xs' !! idx' = Some idx →
    enumerate xs ≡ₚ enumerated_xs' →
    enumerate (delete idx xs) ≡ₚ remove idx enumerated_xs' ∧ snd <$> remove idx enumerated_xs' = delete idx' (snd <$> enumerated_xs').
  Proof.
    intros Hidx Hperm. split.
    - rewrite -Hperm. rewrite /enumerate. by apply reflexive_eq, enumerate_from_delete.
    - apply NoDup_delete_remove; last done. rewrite -Hperm. apply enumerate_NoDup.
  Qed.

  (** States that [xs] is a permutation of [xs'] so that [idx] (unless [None])
  in [xs] maps to [idx'] in [xs']. *)
  Definition permutes {A} (idx : option nat) (xs : list A) (idx' : option nat) (xs' : list A) : Prop :=
    (** [enumerated_xs'] is [xs'] but where each item has an attached label
    tracking what index it corresponded to in [xs]. *)
    ∃ enumerated_xs',
    enumerate xs ≡ₚ enumerated_xs' ∧
    snd <$> enumerated_xs' = xs' ∧
    match idx with
    | Some idx =>
        match idx' with
        | Some idx' => fst <$> (enumerated_xs' !! idx') = Some idx
        | None => False
        end
    | None => idx' = None
    end.

  Lemma permutes_mapping {A} (xs : list A) (idx': nat) (xs' : list A) :
    permutes None xs None xs' →
    idx' < length xs' →
    ∃ idx, permutes (Some idx) xs (Some idx') xs'.
  Proof.
    intros [enumerated_xs' [Hperm [Hsnd _]]] Hbound.
    rewrite -Hsnd fmap_length in Hbound. apply lookup_lt_is_Some_2 in Hbound as [[idx x] Hidx'].
    exists idx. exists enumerated_xs'. split; first done. split.
    - done.
    - rewrite Hidx' //.
  Qed.
  Lemma permutes_Some {A} (idx : nat) (xs : list A) (idx' : option nat) (xs' : list A) :
    permutes (Some idx) xs idx' xs' →
    idx < length xs ∧
    ∃ idx'unwrap, idx' = Some idx'unwrap ∧ xs' !! idx'unwrap = xs !! idx.
  Proof.
    intros [enumerated_xs' [Hperm [Hsnd Hfst]]]. destruct idx' as [idx'|]; last done.
    destruct (enumerated_xs' !! idx') as [[idx'' x]|] eqn:Heidx; last discriminate.
    simpl in Hfst. injection Hfst as Hfst. destruct Hfst.
    apply elem_of_list_lookup_2 in Heidx as Hin.
    rewrite -Hperm in Hin. apply elem_of_list_lookup in Hin as [idx Heidx'].
    assert (Heidx'' := Heidx'). apply enumerate_lookup in Heidx' as [<- Hidx].
    split.
    - rewrite -enumerate_length. by eapply lookup_lt_Some.
    - eexists. split; first done. rewrite Hidx -Hsnd list_lookup_fmap Heidx //.
  Qed.
  Lemma permutes_Some_Some {A} (idx : nat) (xs : list A) (idx' : nat) (xs' : list A) :
    permutes (Some idx) xs (Some idx') xs' →
    idx < length xs ∧ xs' !! idx' = xs !! idx.
  Proof.
    intros Hperm. by apply permutes_Some in Hperm as [Hbound [idx'unwrap [[=<-] Heq]]].
  Qed.
  Lemma permutes_None {A} (xs : list A) (idx' : option nat) (xs' : list A) :
    permutes None xs idx' xs' →
    idx' = None ∧ permutes None xs None xs'.
  Proof.
    intros Hperm. assert (Hperm' := Hperm). by destruct Hperm as [enumerated_xs' [Hperm [Hsnd ->]]].
  Qed.
  Lemma permutes_Some_None {A} (idx : nat) (xs : list A) (idx': nat) (xs' : list A) :
    permutes (Some idx) xs (Some idx') xs' →
    permutes None xs None xs'.
  Proof.
    intros [enumerated_xs' [Hperm [Hfst Hsnd]]]. by exists enumerated_xs'.
  Qed.

  Lemma permutes_insert {A} (idx : nat) (xs : list A) (idx' : nat) (xs' : list A) (x : A) :
    permutes (Some idx) xs (Some idx') xs' →
    permutes (Some idx) (<[idx:=x]>xs) (Some idx') (<[idx':=x]>xs').
  Proof.
    intros [enumerated_xs' [Hperm [Hsnd Hfst]]]. exists (<[idx':=(idx, x)]>enumerated_xs').
    split; last split.
    - rewrite enumerate_insert.
      rewrite (enumerate_insert_fmap xs (enumerate xs) idx idx x).
      2:done.
      2:{ rewrite enumerate_lookup_fst; first done.
          destruct (enumerated_xs' !! idx') as [[idx'' x']|] eqn:Heq; last done.
          simpl in Hsnd. injection Hfst as ->.
          apply elem_of_list_lookup_2 in Heq. rewrite -Hperm in Heq.
          by apply enumerate_bound in Heq.
      }
      rewrite (enumerate_insert_fmap xs enumerated_xs' idx idx' x) //.
      by f_equiv.
    - rewrite list_fmap_insert Hsnd //.
    - rewrite list_lookup_insert; first done. destruct (enumerated_xs' !! idx') eqn:Heq; last done.
      by apply lookup_lt_Some in Heq.
  Qed.

  Lemma permutes_delete {A} (idx : nat) (xs : list A) (idx': nat) (xs' : list A) :
    permutes (Some idx) xs (Some idx') xs' →
    permutes None (delete idx xs) None (delete idx' xs').
  Proof.
    intros [enumerated_xs' [Hperm [Hsnd Hfst]]]. eexists (remove idx enumerated_xs').
    assert (Hperm' := Hperm).
    apply enumerate_delete with (idx := idx) (idx' := idx') in Hperm' as [-> Hsnd']; last done.
    split; last split.
    - destruct (enumerated_xs' !! idx') as [[idx'' x']|] eqn:Heq; last done.
      simpl in Hsnd. injection Hfst as ->.
      apply elem_of_list_lookup_2 in Heq. rewrite -Hperm in Heq.
      by apply enumerate_bound in Heq.
    - rewrite Hsnd' Hsnd //.
    - done.
  Qed.

  Lemma permutes_app_r {A} idx (xs ys : list A) idx' (xs' : list A) :
    permutes idx xs idx' xs' →
    permutes idx (xs ++ ys) idx' (xs' ++ ys).
  Proof.
    intros [enumerated_xs' [Hperm [Hsnd Hfst]]].
    exists (enumerated_xs' ++ enumerate_from (length xs) ys).
    split; last split.
    - rewrite enumerate_app. rewrite /enumerate_from. by f_equiv.
    - rewrite -Hsnd fmap_app snd_zip // seq_length //.
    - destruct idx, idx'; eauto.
      rewrite -list_lookup_fmap fmap_app. rewrite -list_lookup_fmap in Hfst.
      by apply lookup_app_l_Some.
  Qed.

  Lemma permutes_app_l {A} idx sidx (xs ys : list A) idx' sidx' (xs' : list A) :
    sidx = length ys + idx →
    sidx' = length ys + idx' →
    permutes (Some idx) xs (Some idx') xs' →
    permutes (Some sidx) (ys ++ xs) (Some sidx') (ys ++ xs').
  Proof.
    intros -> -> [enumerated_xs' [Hperm [Hsnd Hfst]]].
    exists (enumerate ys ++ ((λ (i : nat * A), let (n, x) := i in (length ys + n, x)) <$> enumerated_xs')).
    split; last split.
    - rewrite enumerate_app. f_equiv. rewrite -Hperm. rewrite /enumerate.
      rewrite enumerate_from_fmap_offset. by replace (length ys + 0) with (length ys) by lia.
    - rewrite fmap_app -list_fmap_compose /= -Hsnd /enumerate enumerate_from_snd. f_equiv. apply Forall_fmap_ext_1.
      apply List.Forall_forall. by intros [a b] ?.
    - rewrite lookup_app_r; last first. { rewrite enumerate_length. lia. }
      rewrite list_lookup_fmap.
      replace (length ys + idx' - length (enumerate ys)) with idx'; last first.
      { rewrite enumerate_length. lia. }
      destruct (enumerated_xs' !! idx') as [[a b]|]; last done. simpl. by injection Hfst as ->.
  Qed.

  Lemma permutes_cons {A} (idx sidx : nat) (xs : list A) (idx' sidx' : nat) (xs' : list A) (x : A) :
    sidx = S idx →
    sidx' = S idx' →
    permutes (Some idx) xs (Some idx') xs' →
    permutes (Some sidx) (x::xs) (Some sidx') (x::xs').
  Proof.
    intros -> -> [enumerated_xs' [Hperm [Hsnd Hfst]]].
    exists ((0, x) :: ((λ (i : nat * A), let (n, x) := i in (S n, x)) <$> enumerated_xs')).
    split; last split.
    - rewrite /enumerate enumerate_from_cons. simpl. f_equiv. rewrite -Hperm. rewrite /enumerate.
      remember 0 as n. generalize n. clear. induction xs as [|x xs' IH].
      * done.
      * intros n'. rewrite enumerate_from_cons. simpl. f_equiv. apply IH.
    - rewrite fmap_cons -list_fmap_compose /= -Hsnd. f_equiv. apply Forall_fmap_ext_1.
      apply List.Forall_forall. by intros [a b] ?.
    - simpl. rewrite list_lookup_fmap -option_fmap_compose.
      destruct (enumerated_xs' !! idx') as [[a b]|]; last done. simpl. by injection Hfst as ->.
  Qed.

  Lemma permutes_to_front {A} (xs : list A) (idx: nat) (xs' : list A) (x : A) :
    idx > length xs →
    idx < length xs + length xs' + 1 →
    permutes (Some idx) (xs ++ x :: xs') (Some idx) (x :: xs ++ xs').
  Proof.
    intros Hgt Hlt.
    exists (((length xs, x) :: enumerate xs) ++ zip (seq (S (length xs)) (length xs')) xs').
    split; last split.
    - etransitivity; last rewrite Permutation_cons_append -app_assoc //.
      rewrite enumerate_app //.
    - rewrite fmap_app /enumerate fmap_cons !snd_zip.
      * done.
      * by rewrite seq_length.
      * by rewrite seq_length.
    - destruct idx as [|idx].
      * lia.
      * simpl. destruct (app_lookup idx (enumerate xs) (zip (seq (S (length xs)) (length xs')) xs')) as [Hidx|[[[idx' x'] [-> Hidx]]|[[idx' x'] [-> Hidx]]]].
        + rewrite Hidx.
          assert (Hlen : length (enumerate xs ++ zip (seq (S (length xs)) (length xs')) xs') = length xs + length xs').
          { rewrite app_length enumerate_length. f_equiv. rewrite zip_length.
            apply Nat.min_r. rewrite seq_length //.
          }
          apply lookup_ge_None_1 in Hidx. lia.
        + apply lookup_lt_Some in Hidx. rewrite enumerate_length in Hidx. lia.
        + rewrite -list_lookup_fmap fst_zip.
          ++ rewrite enumerate_length. replace (S idx) with ((S (length xs)) + (idx - length xs)) by lia.
             apply lookup_seq_lt. lia.
          ++ rewrite seq_length //.
  Qed.

  Lemma permutes_to_middle {A} (xs : list A) (idx: nat) (xs' : list A) (x : A) :
    idx < length xs →
    permutes (Some idx) (xs ++ [x] ++ xs') (Some idx) (xs ++ xs' ++ [x]).
  Proof.
    intros Hlt.
    exists (enumerate xs ++ enumerate_from (length xs + 1) xs' ++ [(length xs, x)]).
    split; last split.
    - rewrite app_assoc !enumerate_app -app_assoc. f_equiv. simpl.
      rewrite /enumerate_from Permutation_cons_append app_length //.
    - rewrite !fmap_app /enumerate !enumerate_from_snd //.
    - rewrite -list_lookup_fmap fmap_app lookup_app_l.
      * rewrite /enumerate !enumerate_from_fst lookup_seq_lt //.
      * rewrite fmap_length enumerate_length //.
  Qed.
End pointed_permutations.

Section threadpool_adequacy.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context {H : iHandler Σ E}.

  (** We are now at a point where we have defined the ingredients that are
  necessary to prove the threadpool adequacy theorem, the critical piece being
  the weakest precondition for threadpools [wptp]. The proof structure may be
  outlined as follows:

                                    ----- Reordering lemmata --------

           |     [wptp_wptpIH']  <- [wptp_reorder'] <- [wptp_reorder]
           |           |
           |           v
           |     [wptp_wptpIH]
           |           |
  Merge lemmata        v                                                    |
           |     [wptp_merge_r]       [wpi_iter_masked]        [wptp_wp]   [wptp] to [WPi]
           |           |                     |                     |        |
           |           v                     v                     v
           |     [wptp_2_threads] -----> [wp_wptp] -----> [threadpool_adequacy]

                                  --- [WPi] to [wptp] ---

  Let us explain the high-level structure of the proof working backwards from
  [threadpool_adequacy]. As explained earlier, the idea is to factor the proof
  into two implications. First, we pass from [WPi t @ threadpoolH ⊕ H; ∅ {{ Φ }}]
  to [wptp H (Some 0) [t] Φ]. This is the role of [wp_wptp]. Then, we pass from
  [wptp H tid tp Φ] (thus in particular [wptp H (Some 0) [t] Φ]) to [WPi] of
  any interleaving of the threadpool [tp] (currently executing [tid]). This is
  [wptp_wp].

  [wp_wptp] is the more intricate step out of the two. It is proven by
  induction over [WPi], but because of technicalities with masks, one must
  use an induction principle [wpi_iter_masked] tailored for [WPi] with masks
  [∅] and [⊤]. A difficulty is encountered in the case of the [EFork] event. In
  particular, it is necessary to prove a lemma of the form [wptp_2_threads].
  This is generalized to [wptp_merge_r], whose proof in essence comes down to
  nested induction. The reader is encouraged to first study the proof of
  [twptp_app] in [iris/program_logic/total_adequacy.v]. This is a proof that
  follows the same structure of nested induction but is much simpler, a
  simplicity afforded from "all threads being equal", meaning that their
  [twptp] has no notion of currently focused thread. (Note that to even state
  this lemma in our setting, we needed the technical idea of allowing the
  threadpool to be suspended, that is, [tid = None]).

  Let us elaborate further on the proof of [wptp_merge_r]. [wptp_merge_r] is
  generalized to [wptp_wptpIH_left]: it is very important that the induction
  hypothesis takes the right form (weakening it a bit will give you issue
  when you step the [wptp] in the goal and it yields to the outside world; a
  point we shall return to later). To prove [wptp_wptpIH_left], we first do
  induction on the [wptp] for the left threadpool (we get to assume
  [wptpIH_left] "one step later"), and then inside that induction proof, we
  do induction on the right threadpool (we get to further assume [wptpIH_right]
  "one step later"). The latter induction argument is found in the proof of
  [wptp_wptpIH_right]. The reason that [wptpIH_right] refers to
  [wptp_wptpIH_left] in its definition is exactly because the latter induction
  happens nested within the former.

  One technicality arises in the induction argument in [wptp_wptpIH_left] when
  the threadpool to the right spawns a new thread, and it ends up in the middle
  of the concatenated threadpool as opposed to in the beginning. In order to
  match up the order of the threads in the [wptp] in the assumption and the
  [wptp] in the conclusion, it is necessary to prove the reordering principle
  [wptp_reorder']. This is proven by generalizing it to [wptp_reorder], which
  is amenable to induction. To state this generalization, it is necessary to
  define a notion of "pointed permutations", as is covered in the section
  [pointed_permutations]. *)

  (** Reordering lemmata. *)

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
      iDestruct (wptp_inversion with "Hwptp") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp')|[(%k&%Hidx&Hwptp')|[(%k&%Hidx&Hwptp')|(%A&%e&%k&%Hidx&HH)]]]]".
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        done.
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        iMod "Hwptp'". iModIntro. iApply "Hwptp'". iPureIntro.
        by apply permutes_insert.
      * iExists _. iSplit. { iPureIntro. by etransitivity. }
        iMod "Hwptp'". iModIntro. iApply "Hwptp'". iPureIntro.
        eapply permutes_app_r; eauto. by apply permutes_insert.
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
          rewrite insert_length in Hidxbound. apply lookup_lt_is_Some_2 in Hidxbound as [t' Hidx_].
          by iApply "Hwptp'".
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
    tid < length tp →
    wptp (R:=R) H (Some tid) ((tp ++ [t]) ++ tp') Φ -∗
    wptp (R:=R) H (Some tid) ((tp ++ tp') ++ [t]) Φ.
  Proof.
    iIntros (Hlt) "Hwptp". iDestruct (wptp_bound with "Hwptp") as "%Hbound".
    iApply wptp_reorder; last done. rewrite -!app_assoc. by apply permutes_to_middle.
  Qed.

  (** Merge lemmata. *)

  (** The induction hypothesis for the left threadpool. *)
  Definition wptp_IH_left (tid : option nat) (tp : list (itree (threadpoolE +' E) R)) Φ : iProp Σ :=
    wptp H tid tp Φ ∧
    match tid with
    (** When the threadpool is currently executing, we can extended it on the
    right by a suspended threadpool. *)
    | Some tid => ∀ tp', wptp H None tp' Φ -∗ wptp H (Some tid) (tp ++ tp') Φ
    (** When the threadpool is suspended, ... *)
    | None =>
        (** we can extend the threadpool from the right by another suspended
        threadpool. This matters for the cases in [wptp_wptpIH_right] where the
        goal steps and passes control to the "outside world". And, ... *)
        (∀ tp', wptp H None tp' Φ -∗ wptp H None (tp ++ tp') Φ) ∧
        (** we can extend the threadpool from the right by a currently
        executing threadpool. *)
        (∀ tp' tid' tid_app, ⌜tid_app = (length tp + tid')%nat⌝ →
          wptp H (Some tid') tp' Φ -∗ wptp H (Some tid_app) (tp ++ tp') Φ)
    end.
  (** The induction hypothesis for the right threadpool. This takes effectively
  the same shape as [wptp_IH_left], aside from two differences. First, we are
  extending on the right instead of the left. Second, the hypotheses in the
  magic wands are [wptpF H wptp_IH_left] as opposed to [wptp H]. This reflects
  how this induction hypothesis is used for an induction nested inside of the
  induction on the [wptp] for the left threadpool. *)
  Definition wptp_IH_right (tid' : option nat) (tp' : list (itree (threadpoolE +' E) R)) Φ : iProp Σ :=
    wptp H tid' tp' Φ ∧
    match tid' with
    | Some tid' => ∀ tp tid_app, ⌜tid_app = (length tp + tid')%nat⌝ →
      wptpF H wptp_IH_left None tp Φ -∗ wptp H (Some tid_app) (tp ++ tp') Φ
    | None =>
      (∀ tp, wptpF H wptp_IH_left None tp Φ -∗ wptp H None (tp ++ tp') Φ) ∧
      (∀ tid tp, wptpF H wptp_IH_left (Some tid) tp Φ -∗ wptp H (Some tid) (tp ++ tp') Φ)
    end.

  Local Instance wptp_IH_left_proper n t tp :
    Proper (pointwise_relation R (dist n) ==> dist n) (wptp_IH_left t tp).
  Proof.
    intros Φ1 Φ2 HΦ. rewrite /wptp_IH_left. repeat f_equiv.
  Qed.
  Local Instance wpi_IH_right_proper n t tp :
    Proper (pointwise_relation R (dist n) ==> dist n) (wptp_IH_right t tp).
  Proof.
    intros Φ1 Φ2 HΦ. rewrite /wptp_IH_right. repeat ( done || apply wptpF_ne || f_equiv );
    clear; intros tid1 tid2 <- tp1 tp2 <- Φ1 Φ2 HΦ; repeat f_equiv.
  Qed.

  Lemma wptp_None tp Φ :
    (∀ tid' t', ⌜tp !! tid' = Some t'⌝ → |={⊤, ∅}=> wptp H (Some tid') tp Φ) -∗
    wptp (R:=R) H None tp Φ.
  Proof.
    iIntros "Hwptp". by iEval (rewrite wptp_unfold).
  Qed.

  (** A lemma used for proving [wptp_wptpIH_left]. This contains the inner
  nested induction. *)
  Lemma wptp_wptpIH_right tid' tp' Φ :
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
      iDestruct (wptp_inversion with "Hwptp'") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|(%A&%e&%k&%Hidx&HH)]]]]".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        done.
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iModIntro.
        rewrite insert_app_r. by iApply "Hwptp''".
      * iExists _. iSplit. { iPureIntro. by apply lookup_app_r_Some. }
        simpl. rewrite insert_app_r.
        rewrite -app_assoc.
        iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']".
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
      iDestruct (wptp_inversion with "Hwptp") as "[(%r&%Hidx&HΦ)|[(%tnext&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|[(%k&%Hidx&Hwptp'')|(%A&%e&%k&%Hidx&HH)]]]]".
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
        iMod "Hwptp''". iDestruct "Hwptp''" as "[_ Hwptp'']". iApply wptp_reorder'.
        { rewrite insert_length. by apply lookup_lt_is_Some_1. }
        iApply "Hwptp''".
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
        simpl. iMod "HH". iModIntro. iApply (ihandler_mono with "[Hwptp']"); last done.
        + iIntros (a) "[_ Hwptp]". rewrite insert_app_l; last first. { by eapply lookup_lt_Some. }
          iApply "Hwptp". iEval (rewrite wptp_unfold /=). clear.
          iIntros (tid' t' Hidx'). iSpecialize ("Hwptp'" $! _ _ Hidx').
          iMod "Hwptp'". iModIntro. iDestruct "Hwptp'" as "[$ _]".
        + eauto.
  Qed.

  Lemma wptp_wptpIH_left tid tp Φ :
    wptp H tid tp Φ -∗
    wptp_IH_left tid tp Φ.
  Proof.
    generalize tid tp Φ.
    iApply (wptp_iter wptp_IH_left); first solve_proper.
    iModIntro. clear tid tp Φ. iIntros (tid tp Φ) "Hwptp".
    iSplit.
    { rewrite wptp_unfold /=. iApply wptpF_mono; last done. iModIntro. clear.
      iIntros (t tp Φ) "Hwptp". iDestruct "Hwptp" as "[$ _]".
    }
    destruct tid as [|].
    - iIntros (tp') "Hwptp'".
      iDestruct (wptp_wptpIH_right with "Hwptp'") as "[_ Hwptp']". by iApply "Hwptp'".
    - iSplit.
      * iIntros (tp') "Hwptp'".
        iDestruct (wptp_wptpIH_right with "Hwptp'") as "[_ Hwptp']". by iApply "Hwptp'".
      * iIntros (tp' tid' tid_app ->) "Hwptp'".
        iDestruct (wptp_wptpIH_right with "Hwptp'") as "[_ Hwptp']". by iApply "Hwptp'".
  Qed.

  Lemma wptp_merge_l tp tp' i Φ :
    wptp H (Some i) tp Φ -∗
    wptp H None tp' Φ -∗
    wptp (R:=R) H (Some i) (tp ++ tp') Φ.
  Proof.
    iIntros "Hwptp Hwptp'". iDestruct (wptp_wptpIH_left with "Hwptp") as "[_ Hwptp]".
    by iApply "Hwptp".
  Qed.
  Lemma wptp_merge_r tp tp' i Φ :
    wptp H None tp Φ -∗
    wptp H (Some i) tp' Φ -∗
    wptp (R:=R) H (Some (length tp + i)) (tp ++ tp') Φ.
  Proof.
    iIntros "Hwptp Hwptp'". iDestruct (wptp_wptpIH_left with "Hwptp") as "[_ [_ Hwptp]]".
    by iApply "Hwptp".
  Qed.

  Lemma wptp_2_threads t t' Φ :
    wptp H (Some 0) [t] Φ -∗
    wptp H None [t'] Φ -∗
    wptp (R:=R) H (Some 0) [t; t'] Φ.
  Proof.
    iIntros "Hwptp Hwptp'". iDestruct (wptp_merge_l with "Hwptp Hwptp'") as "$".
  Qed.

  (** Passage from [WPi] to [wptp]. *)

  Lemma wp_wptp {Hseq : Sequential H} (t : itree (threadpoolE +' E) R) Φ :
    WPi t @ (threadpoolH ⊕ H); ∅ {{ v, |={∅, ⊤}=> Φ v }} -∗
    wptp H (Some 0) [t] Φ.
  Proof.
    pose (G := (λ (masked : bool) (t : itree (threadpoolE +' E) R) (Φ_fupd : leibnizO R -d> iPropO Σ),
      ∀ Φ, (∀ r, Φ_fupd r -∗ (|={∅, ⊤}=> Φ r)) -∗
        if masked then
          wptp H None [t] Φ
        else
          wptp H (Some 0) [t] Φ
      )%I).
    iAssert (∀ t Φ, WPi t @ threadpoolH ⊕ H; ∅ {{ Φ }} -∗ G false t Φ)%I as "Hgen"; last first.
    { iIntros "Hwp". iApply ("Hgen" with "Hwp"). eauto. }
    iApply (wpi_iter_masked (threadpoolH ⊕ H) G); first solve_proper.
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
          ++ iMod "Hwp" as "[Hcurrent Hnew]". simpl.
             (** The induction hypotheses [Hcurrent] and [Hnew] can only be
             used to prove [wptp]s for singleton threadpools, and yet the goal
             is a [wptp] for two threads (the current one and the newly forked
             one). We use a "merge lemma" to split this goal into two pieces, a
             [wptp] for each of the two threads: *)
             iApply (wptp_2_threads with "[Hcurrent Hwand]").
             +++ by iApply "Hcurrent".
             +++ iApply wptp_None. iIntros "!>" (tid' t' Hidx). iMod "Hnew".
                 apply list_lookup_singleton_Some in Hidx as [-> _].
                 iApply "Hnew". iModIntro. by iIntros (r) "?".
          ++ iModIntro. iSplit.
             +++ do 2 iMod "Hwp". iModIntro. iApply wptp_None. iIntros (tid' t' Hidx).
                 apply list_lookup_singleton_Some in Hidx as [-> _].
                 by iApply "Hwp".
             +++ iIntros (tid t Hidx).
                 apply list_lookup_singleton_Some in Hidx as [-> _].
                 do 3 iMod "Hwp". by iApply "Hwp".
        + iExists _. iSplit. { iPureIntro. reflexivity. }
          unshelve iDestruct (is_seq with "Hwp") as "Hwp".
          iApply (ihandler_mono with "[Hwand]"); last done; eauto.
          iIntros (a) "HG". by iApply "HG".
    - clear. iIntros "!>" (t Φ) "HG". iIntros (Φ') "Hwand". iApply wptp_None.
      iIntros (tid' t' Hidx'). apply list_lookup_singleton_Some in Hidx' as [-> _].
      iMod "HG". iModIntro. by iApply "HG".
  Qed.

  (** Passage from [wptp] to [WPi] of interleaving. *)

  (* TODO: Why do I need to register this hint again here when I already did it
  in another section? *)
  Hint Resolve interleaves__mono : paco.

  Theorem wptp_wp :
    ∀ tid' tp Φ,
    wptp (R:=R) H tid' tp Φ -∗
    ∀ tid interleaving,
      ⌜tid' = Some tid⌝ →
      ⌜interleaves tid tp interleaving⌝ →
      WPi interleaving @ H; ∅ {{ r, |={∅, ⊤}=> Φ r }}.
  Proof.
    iApply (wptp_iter _); first solve_proper.
    iIntros "!>" (tid' tp Φ) "Hwptp". iIntros (tid interleaving -> Hinter).
    iDestruct (wptp_inversion with "Hwptp") as "[(%r&%Hidx'&HΦ)|[(%tnext&%Hidx'&Hwptp')|[(%k&%Hidx'&Hwptp')|[(%k&%Hidx'&Hwptp')|(%A&%e&%k&%Hidx'&HH)]]]]".
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
      apply lookup_lt_is_Some_2 in Hidx'' as [t' Hidx''].
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
  Corollary threadpool_adequacy `{!Sequential H}
    (concurrent : itree (threadpoolE +' E) R)
    (interleaving : itree E R)
    (Φ : R → iProp Σ) :
    interleaves 0 [concurrent] interleaving →
    WPi concurrent @ threadpoolH ⊕ H; ⊤ {{ Φ }} -∗
    WPi interleaving @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "%Hinter Hwp". iApply wpi_clear_mask.
    iEval (rewrite -wpi_clear_mask) in "Hwp". iMod "Hwp".
    (** Pass to [wptp]: *)
    iDestruct (wp_wptp with "Hwp") as "Hwptp".
    (** Pass to [WPi] of interleaving: *)
    iDestruct (wptp_wp with "Hwptp") as "Hwp".
    by iApply "Hwp".
  Qed.
End threadpool_adequacy.
