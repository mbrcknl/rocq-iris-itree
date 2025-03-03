From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree Require Import exec.
From iris.bi Require Import fixpoint_mono.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import ITree.
From ITree Require Import Basics.Monad.
From ITree Require Import Eqit.

(** Event type for angelic non-determinism. *)
Variant angelicE : Type → Type :=
  | EAngelic (A : Type) : angelicE A.

Definition angelic_choice `{angelicE -< E} (A : Type) `{EqDecision A} `{Inhabited A} : itree E A :=
  trigger (EAngelic A).
Lemma angelic_choice_to_translate {E1 E2} (A : Type) `{EqDecision A} `{Inhabited A} (HE1 : angelicE -< E1) (HE2 : angelicE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (angelic_choice A) Hin (angelic_choice A).
Proof.
  move => ?. by apply trigger_to_translate.
Qed.
Global Hint Resolve angelic_choice_to_translate : itree_auto.

Section handler.
  Context {Σ : gFunctors}.

  Program Definition angelicH : iHandler Σ angelicE :=
    IHandler (λ A e,
      match e with
      | EAngelic A => λ Φ _, (∃ s, Φ s)
      end
    )%I _.
  Next Obligation.
    iIntros (? e ????) "HΦwand Hswand". destruct e. iIntros "[% HΦ]". iExists _. by iApply "HΦwand".
  Qed.
  Global Instance angelicH_Sequential :
    Sequential angelicH.
  Proof.
    iIntros (A e Φ s) "HH". by destruct e.
  Qed.
End handler.

Section wp.
  Context {E : Type → Type} `{H : iHandler Σ E} `{!angelicE -< E} `{!inH angelicH H}.
  Context `{!invGS_gen hlc Σ}.

  Lemma wpi_angelic_vis {R A} k a M (Φ : R → iProp Σ) :
    WPi k a @ H; M {{ Φ }} -∗
    WPi (vis (EAngelic A) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /angelicH/=. iExists _.
    iEval (rewrite -wpi_update). iMod "Hfupd". rewrite wpi_clear_mask //.
  Qed.

  Lemma wpi_angelic {A} `{EqDecision A} `{Inhabited A} M a (Φ : A → iProp Σ) :
    Φ a -∗
    WPi angelic_choice A @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_angelic_vis. iApply wpi_ret. iApply "Hwp".
  Qed.
End wp.

Program Definition angelicEH : seHandler angelicE :=
  SEHandler unit (λ A e s, match e with | EAngelic A => λ C, ∀ x, C x tt end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance angelicEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    seHandlerAdequate angelicH angelicEH := {| sehandler_inv s := True%I |}.
Next Obligation.
  move => ????????? HP. iIntros "Hwp _".
  rewrite /angelicH/=. case_match => /=. simplify_eq/=. iDestruct "Hwp" as (?) "Hwp".
  iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|]. iApply "Hwp".
Qed.
