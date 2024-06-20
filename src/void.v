From ITree Require Import ITree Eqit.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop fancy_updates.
From iris.itree Require Import wpi itree handler.

(* TODO: rename to emptyE *)
Inductive voidE : Type → Type :=.

Section handler.
  Context {Σ : gFunctors}.

  Program Definition voidH : iHandler Σ voidE :=
    IHandler (λ A e, match e with end )%I _.
  Next Obligation. by move => ? []. Qed.
  Global Instance voidH_Sequential :
    Sequential voidH.
  Proof. by iIntros (A [] Φ s) "HH". Qed.
End handler.

Definition insert_voidE {E R} (t : itree E R) : itree (E +' voidE) R :=
  translate inl1 t.

Section adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS_gen hlc Σ} {H : iHandler Σ E}.

  Theorem voidE_adequacy_empty (t : itree E R) Φ :
    WPi t @ H; ∅ {{ Φ }} -∗
    WPi insert_voidE t @ H ⊕ voidH; ∅ {{ Φ }}.
  Proof.
    iRevert (t Φ). rewrite /insert_voidE. iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". wpi_norm. by iApply wpi_ret'.
    - iIntros "!>" (Φ t) "Hwp". wpi_norm. by iApply wpi_update.
    - iIntros "!>" (Φ A e k) "HH". wpi_norm.
      iApply wpi_vis => /=. iMod "HH". iModIntro.
      iApply ihandler_mono; last done.
      + iIntros (a) "Hwp". by iApply wpi_update_post.
      + iIntros "!>" (a) "Hwp". iApply wpi_clear_mask.
        iMod "Hwp". iModIntro. iApply wpi_wand; last done.
        iIntros (r []).
  Qed.

  Theorem voidE_adequacy (t : itree E R) Φ M :
    WPi t @ H; M {{ Φ }} -∗
    WPi insert_voidE t @ H ⊕ voidH; M {{ Φ }}.
  Proof.
    iIntros "Hwp".
    rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iPoseProof voidE_adequacy_empty as "Had". iSpecialize ("Had" with "Hwp").
    iApply wpi_wand; last done. iIntros (r). eauto.
  Qed.

  Theorem voidE_terminates_empty_mask (t : itree voidE R) Φ :
    WPi t @ voidH; ∅ {{ Φ }} -∗
    |={∅}=> ∃ v, ⌜t ≈ Ret v⌝ ∗ Φ v.
  Proof.
    iRevert (t Φ). iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) ">$". by iModIntro.
    - iIntros "!>" (Φ t) ">>[% [% $]]". iModIntro. by rewrite tau_eutt.
    - iIntros "!>" (Φ A [] k) "HH".
  Qed.

  Theorem voidE_terminates (t : itree voidE R) Φ M :
    WPi t @ voidH; M {{ Φ }} -∗
    |={M, ∅}=> ∃ v, ⌜t ≈ Ret v⌝ ∗ |={∅,M}=> Φ v.
  Proof.
    iIntros "Hwp".
    rewrite -wpi_clear_mask. iMod "Hwp".
    iMod (voidE_terminates_empty_mask with "Hwp") as (? ?) "$".
    done.
  Qed.
End adequacy.
