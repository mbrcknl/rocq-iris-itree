From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree Require Import trace.
From iris.itree Require Import exec.
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
    (** Halting reestablishes the invariants, making it qualitatively different
    from some other kinds of NB. *)
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

Section wp.
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
End wp.

Section ifn.
  (** Return type for executions that halted. *)
  Variant halted := Halted.

  (** Interpretation function for [haltE]. It effectively replaces [EHalt] events
  with [Ret (inr Halted)]. *)
  Definition halt_ifn {R E} (t : itree (haltE +' E) R) : itree E (R + halted) :=
    ITree.iter (λ (t : itree (haltE +' E) R),
      match observe t with
      | RetF r => Ret (inr (inl r))
      | TauF t => Ret (inl t)
      | VisF (inl1 EHalt) k => Ret (inr (inr Halted))
      | VisF (inr1 e) k => ITree.map (λ x, inl (k x)) (trigger e)
      end) t.

  Lemma halt_ifn_ret {E R} (r : R) :
    halt_ifn (Ret r) ≅ (Ret (inl r) : itree E (R + halted)).
  Proof.
    rewrite /halt_ifn.
    rewrite unfold_iter bind_ret_l //.
  Qed.

  Lemma halt_ifn_tau {E R} (t : itree (haltE +' E) R) :
    halt_ifn (Tau t) ≅ Tau (halt_ifn t).
  Proof.
    rewrite /halt_ifn.
    rewrite unfold_iter bind_ret_l //.
  Qed.

  Lemma halt_ifn_halt {E R} (k : ∅ → itree (haltE +' E) R) :
    halt_ifn (Vis (inl1 EHalt) k) ≅ Ret (inr Halted).
  Proof.
    rewrite /halt_ifn.
    rewrite unfold_iter bind_ret_l //.
  Qed.

  Lemma halt_ifn_vis {E R A} (e : E A) (k : A → itree (haltE +' E) R) :
    halt_ifn (Vis (inr1 e) k) ≅ Vis e (λ a, Tau (halt_ifn (k a))).
  Proof.
    rewrite /halt_ifn.
    pose (Heq := map_vis (E:=haltE +' E) (Some : R -> option R) (inr1 e) k).
    rewrite unfold_iter /= bind_bind bind_vis. f_equiv. f_equiv. intros a.
    rewrite !bind_ret_l //.
  Qed.
End ifn.

Section adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS_gen hlc Σ} {H : iHandler Σ E}.
  (** This sequentiality assumption is necessary because [halt_ifn]
  introduces [Ret] (with non [False] post-conditions) even in branches not
  corresponding to the main thread. *)
  Context `{!Sequential H}.

  Theorem halt_adequacy_empty (t : itree (haltE +' E) R) Φ :
    WPi t @ haltH ⊕ H; ∅ {{ Φ }} -∗
    WPi halt_ifn t @ H; ∅ {{ r,
      match r with
      | inl r => Φ r
      | inr Halted => |={∅, ⊤}=> True
      end
    }}.
  Proof.
    iRevert (t Φ). iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". by iEval (rewrite halt_ifn_ret -wpi_ret').
    - iIntros "!>" (Φ t) "Hwp". rewrite halt_ifn_tau -wpi_tau. by iApply wpi_update.
    - iIntros "!>" (Φ A [[]|e] k) "HH".
      * simpl. rewrite halt_ifn_halt. by iApply wpi_ret'.
      * simpl. rewrite halt_ifn_vis. iApply wpi_vis.
        iDestruct (is_seq with "HH") as "HH".
        iApply ihandler_mono; last done.
        + iIntros (a) "Hwp". rewrite wpi_tau. by iApply wpi_update_post.
        + by iIntros "!>" (a) "Hwp".
  Qed.

  (** Adequacy theorem for [haltH]. *)
  Corollary halt_adequacy (t : itree (haltE +' E) R) Φ :
    WPi t @ haltH ⊕ H; ⊤ {{ Φ }} -∗
    WPi halt_ifn t @ H; ⊤ {{ r,
      match r with
      | inl r => Φ r
      | inr Halted => True
      end
    }}.
  Proof.
    iIntros "Hwp". rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iApply (wpi_wand with "[] [Hwp]"). 2: by iApply halt_adequacy_empty.
    iIntros (?) "Hp". case_match; first done. by case_match.
  Qed.
End adequacy.

(** Definitions for exec *)
Program Definition haltEH : seHandler haltE :=
  SEHandler unit (λ A e s C, False) _.
Next Obligation. done. Qed.

Global Program Instance haltEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    seHandlerAdequate haltH haltEH := {| sehandler_inv s := True%I |}.
Next Obligation. move => ????????? HP. done. Qed.

Lemma exec_assume (P : Prop) E (EH : eHandler E E P) `{!haltE -< E} f1 f2 `{!inEH haltEH EH f1 f2} `{!Decision P} s C:
  P →
  (∀ HP, C (Ret HP) s) →
  exec EH (assume P) s C.
Proof. move => ??. rewrite /assume. case_decide; [apply exec_stop; naive_solver|done]. Qed.
