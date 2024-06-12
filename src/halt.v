From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree Require Import trace.
From iris.bi Require Import fixpoint.
From iris.bi Require Import derived_laws.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import ITree.
From ITree Require Import Eqit.

(** An event type for halting the machine safely. *)
Variant haltE : Type → Type :=
  (** Event for safely halting the execution. *)
  | EHalt : haltE void.

Global Instance AnswerEqDecision_haltE :
  AnswerEqDecision haltE.
Proof. intros A [] []. Qed.

(** Halt the machine (crash safely). *)
Definition halt {R : Type} `{!haltE -< E} : itree E R :=
  vis EHalt (λ (a : Empty_set), match a with end).

Lemma halt_to_translate {E1 E2 R} (HE1 : haltE -< E1) (HE2 : haltE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (halt (R:=R)) Hin halt.
Proof. move => ?. rewrite /halt. by apply vis_to_translate. Qed.
Global Hint Resolve halt_to_translate : itree_auto.

Definition some_or_halt {E R} `{!haltE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => halt end)%itree.
Notation "x !" := (some_or_halt x) (at level 10, format "x !") : itree_scope.

Lemma some_or_halt_to_translate {E1 E2 R} (o : option R) (HE1 : haltE -< E1) (HE2 : haltE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (o!) Hin (o!).
Proof. move => ?. by destruct o => /=; [apply Ret_to_translate|apply halt_to_translate]. Qed.
Global Hint Resolve some_or_halt_to_translate : itree_auto.

Definition assume {E} `{haltE -< E} (P : Prop) `{!Decision P} : itree E P :=
  if decide P is left HP then Ret HP
  else halt.

Lemma assume_to_translate {E1 E2} (HE1: haltE -< E1) (HE2: haltE -< E2) P `{!Decision P} (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (assume P) Hin (assume P).
Proof. move => ?. rewrite /assume. by case_decide; [apply Ret_to_translate|apply halt_to_translate]. Qed.
Global Hint Resolve assume_to_translate : itree_auto.

Section handler.
  Context {Σ : gFunctors} `{!invGS_gen hlc Σ}.

  Program Definition haltH : iHandler Σ haltE :=
    IHandler (λ _ _ _ _, (|={∅, ⊤}=> True)%I) _.
  Next Obligation.
    eauto.
  Qed.
  Global Instance haltH_Sequential :
    Sequential haltH.
  Proof.
    by iIntros (A e Φ s) "HH".
  Qed.
End handler.

Section wp_halt.
  Context {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context {H : iHandler Σ E} `{!haltE -< E} `{!inH haltH H}.

  Lemma wpi_halt {R} (Φ : R → iProp Σ) :
    ⊢ WPi halt @ H; ⊤ {{ Φ }}.
  Proof using Type*.
    iApply wpi_vis => /=. rewrite -is_inH /=.
    iApply fupd_mask_intro; first set_solver. iIntros "Hfupd".
    by iMod "Hfupd".
  Qed.

  Lemma wpi_assume P `{!Decision P} (Φ : P → iProp Σ) :
    (∀ HP:P, Φ HP) -∗
    WPi assume P @ H; ⊤ {{ Φ }}.
  Proof using Type*.
    iIntros "HΦ". rewrite /assume. case_decide.
    - iApply wpi_ret. iApply "HΦ".
    - iApply wpi_halt.
  Qed.
End wp_halt.

(** "Sandbox" an [itree] with halt events by replacing halt with returning [None]. *)
Definition sandbox_halt {R E} (t : itree (haltE +' E) R) : itree E (option R) :=
  ITree.iter (λ (t : itree (haltE +' E) (option R)),
    match observe t with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | VisF (inl1 EHalt) k => Ret (inr None)
    | VisF (inr1 e) k => ITree.map (λ x, inl (k x)) (trigger e)
    end) (ITree.map Some t).

Lemma sandbox_halt_ret {E R} (r : R) :
  sandbox_halt (Ret r) ≅ (Ret (Some r) : itree E (option R)).
Proof.
  rewrite /sandbox_halt.
  pose (Heq := map_ret (E:=haltE +' E) Some r).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_halt_tau {E R} (t : itree (haltE +' E) R) :
  sandbox_halt (Tau t) ≅ Tau (sandbox_halt t).
Proof.
  rewrite /sandbox_halt.
  pose (Heq := map_tau (E:=haltE +' E) (Some : R -> option R) t).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_halt_halt {E R} (k : ∅ → itree (haltE +' E) R) :
  sandbox_halt (Vis (inl1 EHalt) k) ≅ Ret None.
Proof.
  rewrite /sandbox_halt.
  pose (Heq := map_vis (E:=haltE +' E) (Some : R -> option R) (inl1 EHalt) k).
  apply bisimulation_is_eq in Heq.
  rewrite Heq unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_halt_vis {E R A} (e : E A) (k : A → itree (haltE +' E) R) :
  sandbox_halt (Vis (inr1 e) k) ≅ Vis e (λ a, Tau (sandbox_halt (k a))).
Proof.
  rewrite /sandbox_halt.
  pose (Heq := map_vis (E:=haltE +' E) (Some : R -> option R) (inr1 e) k).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter /= bind_bind bind_vis. f_equiv. f_equiv. intros a.
  rewrite !bind_ret_l //.
Qed.

Section halt_adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS_gen hlc Σ} {H : iHandler Σ E}.
  (** This sequentiality assumption is necessary because [sandbox_halt]
  introduces [Ret] (with non [False] post-conditions) even in branches not
  corresponding to the main thread. *)
  Context `{!Sequential H}.

  Theorem halt_adequacy' (t : itree (haltE +' E) R) Φ :
    WPi t @ haltH ⊕ H; ∅ {{ Φ }} -∗
    WPi sandbox_halt t @ H; ∅ {{ r,
      match r with
      | Some r => Φ r
      | None => |={∅, ⊤}=> True
      end
    }}.
  Proof.
    iRevert (t Φ). iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". by iEval (rewrite sandbox_halt_ret -wpi_ret').
    - iIntros "!>" (Φ t) "Hwp". rewrite sandbox_halt_tau -wpi_tau. by iApply wpi_update.
    - iIntros "!>" (Φ A [[]|e] k) "HH".
      * simpl. rewrite sandbox_halt_halt. by iApply wpi_ret'.
      * simpl. rewrite sandbox_halt_vis. iApply wpi_vis.
        iDestruct (is_seq with "HH") as "HH".
        iApply ihandler_mono; last done.
        + iIntros (a) "Hwp". rewrite wpi_tau. by iApply wpi_update_post.
        + by iIntros "!>" (a) "Hwp".
  Qed.

  Corollary halt_adequacy (t : itree (haltE +' E) R) Φ :
    WPi t @ haltH ⊕ H; ⊤ {{ Φ }} -∗
    WPi sandbox_halt t @ H; ⊤ {{ r,
      match r with
      | Some r => Φ r
      | None => True
      end
    }}.
  Proof.
    iIntros "Hwp". rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iApply (wpi_wand with "[] [Hwp]"). 2: by iApply halt_adequacy'.
    iIntros (?) "Hp". by case_match.
  Qed.

End halt_adequacy.
