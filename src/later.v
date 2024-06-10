From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi trace handler.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree.

Variant laterE : Type → Type :=
  | ELater : laterE ().

Definition step `{laterE -< E} : itree E () :=
  trigger ELater.

Global Instance AnswerEqDecision_laterE :
  AnswerEqDecision laterE.
Proof. intros A [] [] []. by left. Qed.

Variant later_modality : Set :=
  | Identity
  | Later.

Definition lat {Σ} (m : later_modality) (P : iProp Σ) : iProp Σ :=
  match m with
  | Identity => P
  | Later => ▷ P
  end.

Section lat.
  Lemma lat_mono {Σ} m (Φ Ψ : iProp Σ) :
    (Φ -∗ Ψ) -∗
    lat m Φ -∗ lat m Ψ.
  Proof.
    iIntros "Hwand HΦ". destruct m; by iApply "Hwand".
  Qed.

  Lemma lat_intro {Σ} m (Φ : iProp Σ) :
    Φ -∗
    lat m Φ.
  Proof.
    iIntros "HΦ". by destruct m.
  Qed.

  Lemma lat_sep {Σ} m (Φ Ψ : iProp Σ) :
    lat m Φ -∗
    lat m Ψ -∗
    lat m (Φ ∗ Ψ).
  Proof.
    iIntros "HΦ HΨ". destruct m; iFrame.
  Qed.
End lat.

Section handler.
  Context {Σ : gFunctors}.

  Program Definition laterH (m : later_modality) : iHandler Σ laterE :=
    IHandler (λ A e,
      match e with
      | ELater => λ Φ _, lat m (Φ ())
      end
    )%I _.
  Next Obligation.
    iIntros (???????) "HΦwand _". destruct e.
    iIntros "HΦ". by iApply (lat_mono with "HΦwand").
  Qed.
  Global Instance laterH_Sequential m :
    Sequential (laterH m).
  Proof.
    by iIntros (A [] Φ s) "HH".
  Qed.
End handler.

Section wpi_later.
  Context `{!invGS_gen hlc Σ} {E : Type → Type} {H : iHandler Σ E} {m : later_modality}.
  Context `{laterE -< E} `{inH Σ laterE E (laterH m) H}.

  Lemma wpi_later M (Φ : () → iProp Σ) :
    (lat m (|={M}=> Φ ())) -∗
    WPi (trigger ELater) @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply is_inH. simpl. iApply (lat_mono with "[Hfupd]"); last done.
    iIntros "HΦ". iApply wpi_ret. by iMod "Hfupd".
  Qed.
End wpi_later.
