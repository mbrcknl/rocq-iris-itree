From iris.itree Require Import handler wpi itree.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Export fancy_updates.
From ITree Require Import ITree Eqit Recursion RecursionFacts TranslateFacts.

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
  (** Yield control to another (demonically chosen) thread in the thread-pool
  or the current thread. *)
  | EYield : threadpoolE unit
  (** (Safely) kill the current thread and yield. *)
  | EKillThread : threadpoolE Empty_set.

(** End the thread safely. *)
Definition kill_thread {R : Type} `{threadpoolE -< E} : itree E R :=
  vis EKillThread (λ (a : Empty_set), match a with end).

Lemma kill_thread_bind {A B : Type} `{threadpoolE -< E} (k : A → itree E B) :
  ITree.bind kill_thread k ≈ kill_thread.
Proof.
  rewrite /kill_thread. rewrite bind_vis. do 2 f_equiv. intros [].
Qed.

Lemma kill_thread_to_translate {E1 E2 R} (HE1 : threadpoolE -< E1) (HE2 : threadpoolE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (kill_thread (R := R)) Hin (kill_thread (R := R)).
Proof.
  (* FIXME: This proof is poor style. *)
  intros Hresum. rewrite /kill_thread. inversion Hresum.
  constructor. rewrite translate_vis. setoid_rewrite translate_resum.
  f_equiv. f_equiv. intros [].
Qed.
Global Hint Resolve kill_thread_to_translate : itree_auto.

(** Yield control to another (demonically chosen) thread in the thread-pool
or the current thread. *)
Definition yield `{threadpoolE -< E} : itree E () :=
  trigger EYield.

Lemma yield_to_translate {E1 E2} (HE1 : threadpoolE -< E1) (HE2 : threadpoolE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate yield Hin yield.
Proof. move => ?. rewrite /yield. by apply trigger_to_translate. Qed.
Global Hint Resolve yield_to_translate : itree_auto.

(** [iHandler] for [threadpoolE]. *)
Program Definition threadpoolH {Σ} `{!invGS_gen hlc Σ} : iHandler Σ threadpoolE :=
  IHandler (λ A e,
    match e with
    (** We define the iHandler in a way that imposes a semantic restriction on
    [EFork] disallowing returning in the [NewThread] continuation, even
    though it is possible to define [itree]s that do so. From the point of view
    of [WPi], we are thus declaring such returns as unsafe. This
    overapproximation is justified from our applications: typically, only the
    return value of the main thread concerns us. *)
    | EFork      => λ Φ s, Φ CurrentThread ∗ s NewThread
    (** To prove that one can [EYield], one must restablish all the invariants. *)
    | EYield     => λ Φ _, |={∅, ⊤}=> |={⊤, ∅}=> Φ ()
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

Section spawn.
  (** Spawn a new thread executing [t]. *)
  Definition spawn `{threadpoolE -< E} (t : itree E ()) : itree E () :=
      thread ← trigger EFork;
      match thread with
      | CurrentThread => Ret ()
      | NewThread =>
          t ;;
          kill_thread
      end.

  Global Instance spawn_proper `{threadpoolE -< E} b1 b2 :
    Proper ((eqit (=) b1 b2) ==> (eqit (=) b1 b2)) (spawn (E := E)).
  Proof.
    intros Heqit t1 t2.
    rewrite /spawn. f_equiv. intros [|]; first done.
    by f_equiv.
  Qed.

  Lemma spawn_interp_recursive `{threadpoolE -< E} {A B} (t : itree (callE A B +' E) ()) f :
    interp (recursive f) (spawn t) ≈ spawn (interp (recursive f) t).
  Proof.
    rewrite /spawn. eutt_norm/=. f_equiv. intros thread. case_match; by eutt_norm.
  Qed.
End spawn.

Lemma normalize_itree_spawn_interp_recursive `{threadpoolE -< E} {A B} (t : itree (callE A B +' E) ()) f t' p :
  NormalizeITree p (interp (recursive f) t) t' →
  NormalizeITree true (interp (recursive f) (spawn t)) (spawn t').
Proof. move => [Heq]. constructor. by rewrite -Heq spawn_interp_recursive. Qed.
Global Hint Resolve normalize_itree_spawn_interp_recursive : itree_auto.

(** Stepping lemmata for the threadpool [WPi]. *)
Section wp_threadpool.
  Context `{!invGS_gen hlc Σ} {E : Type → Type} {H : iHandler Σ E}.
  Context `{threadpoolE -< E} `{inH Σ threadpoolE E threadpoolH H}.

  (** Note here crucially that the mask has to be full for the rule to apply.
  This means that you cannot step over an [EYield] if there are open
  invariants. It amounts to the typical requirement of atomicity in the
  invariant opening rule known from "normal Iris". *)
  Lemma wpi_yield (Φ : () → iProp Σ) :
    Φ () -∗
    WPi (trigger EYield) @ H; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_vis. iApply is_inH. simpl.
    iApply fupd_mask_intro_subseteq; first done.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply wpi_ret. by iMod "Hfupd".
  Qed.

  Lemma wpi_kill {R} (k : Empty_set → itree E R) (Φ : R → iProp Σ) :
    ⊢ WPi (vis EKillThread k) @ H; ⊤ {{ Φ }}.
  Proof.
    iApply wpi_vis. iApply is_inH. simpl.
    by iApply fupd_mask_intro_subseteq; first done.
  Qed.

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

  Lemma wpi_spawn t (M : coPset) (Φ : () → iProp Σ) :
    Φ () -∗
    WPi t @ H; ⊤ {{ _, True }} -∗
    WPi (spawn t) @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ Hwp".
    rewrite /spawn.
    rewrite bind_trigger. iApply @wpi_fork. iSplitL "HΦ".
    - by iApply wpi_ret.
    - iApply wpi_bind. iApply wpi_wand; last done. iIntros (r _).
      by iApply @wpi_kill.
  Qed.
End wp_threadpool.
