From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi trace handler.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree.

Variant laterE : Type → Type :=
  | ELater : laterE ().

Global Instance AnswerEqDecision_laterE :
  AnswerEqDecision laterE.
Proof. intros A [] [] []. by left. Qed.

Section handler.
  Context {Σ : gFunctors}.

  Program Definition laterH : iHandler Σ laterE :=
    IHandler (λ A e,
      match e with
      | ELater => λ Φ _, ▷ Φ ()
      end
    )%I _.
  Next Obligation.
    iIntros (??????) "HΦwand _". destruct e.
    iIntros "HΦ". iNext. by iApply "HΦwand".
  Qed.
  Global Instance laterH_Sequential :
    Sequential laterH.
  Proof.
    by iIntros (A [] Φ s) "HH".
  Qed.
End handler.

Section wpi_later.
  Context `{!invGS_gen hlc Σ} {E : Type → Type} {H : iHandler Σ E}.
  Context `{laterE -< E} `{inH Σ laterE E laterH H}.

  Lemma wpi_later M (Φ : () → iProp Σ) :
    (▷ |={M}=> Φ ()) -∗
    WPi (trigger ELater) @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply is_inH. simpl. iNext. iApply wpi_ret. by iMod "Hfupd".
  Qed.
End wpi_later.
