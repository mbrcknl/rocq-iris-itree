(* Adapted from [iris/iris_heap_lang/lib/spin_lock.v]. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Import lib.token.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export invariants.

From iris.itree.heaplang Require Export definition lang program_logic tactics.
From iris.itree Require Import heap step.

Local Definition newlock : val := λ: <>, ref #false.
Local Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Local Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Local Definition release : val := λ: "l", "l" <- #false.

(** The CMRA we need. *)
Class spin_lockG Σ := LockG { #[local] lock_tokG :: tokenG Σ }.

Definition spin_lockΣ : gFunctors := #[tokenΣ].

Global Instance subG_spin_lockΣ {Σ} : subG spin_lockΣ Σ → spin_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!invGS_gen hlc Σ, !heaplangHGS Σ, !spin_lockG Σ}.
  Let N := nroot .@ "spin_lock".

  Local Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    ∃ b : bool, l ↦ #b ∗ if b then True else token γ ∗ R.

  Local Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    ∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv γ l R).

  Local Definition locked (γ : gname) : iProp Σ := token γ.

  Local Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

  (** The main proofs. *)
  Local Lemma is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ∗-∗ R2) -∗ is_lock γ lk R2.
  Proof.
    iDestruct 1 as (l ->) "#Hinv"; iIntros "#HR".
    iExists l; iSplit; [done|]. iApply (inv_iff with "Hinv").
    iIntros "!> !>"; iSplit; iDestruct 1 as (b) "[Hl H]";
      iExists b; iFrame "Hl"; destruct b;
      first [done|iDestruct "H" as "[$ ?]"; by iApply "HR"].
  Qed.

  Local Lemma newlock_spec m (R : iProp Σ):
    R -∗
    WP newlock #() @ m; ⊤ {{ lk, ∃ γ, is_lock γ lk R }}.
  Proof.
    iIntros "HR". rewrite /newlock /=.
    iApply wp_App. iApply lat_intro. simpl.
    iApply wp_fupd.
    iApply wp_Alloc; first done. iApply lat_intro. simpl. iIntros (l) "Hloc".
    iMod token_alloc as (γ) "Hγ".
    iMod (inv_alloc N _ (lock_inv γ l R) with "[HR Hloc Hγ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iExists γ. iExists l. eauto.
  Qed.

  Local Lemma try_acquire_spec γ lk R Φ :
    is_lock γ lk R -∗
    (∀ b, (if b is true then locked γ ∗ R else True) -∗ Φ #b) -∗
    WP try_acquire lk @ Later; ⊤ {{ Φ }}.
  Proof.
    iIntros "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    iApply wp_App. iApply lat_intro. simpl.
    wp_bind (CmpXchg _ _ _). iInv N as ([]) "[>Hl HR]".
    - iApply (wp_CmpXchg_fail with "Hl"); eauto.
      { solve_ndisj. }
      { repeat constructor. }
      iNext. iIntros "Hl".
      iModIntro. iSplitL "Hl". { iNext. iExists true; eauto. }
      iApply wp_Snd.
      iNext. by iApply "HΦ".
    - iApply (wp_CmpXchg_suc with "Hl"); eauto.
      { solve_ndisj. }
      { repeat constructor. }
      iApply lat_intro.
      iIntros "Hl".
      iDestruct "HR" as "[>Hγ HR]".
      iModIntro. iSplitL "Hl". { iNext; iExists true; eauto. }
      rewrite /locked.
      iApply wp_Snd. simpl.
      iApply "HΦ". by iFrame.
  Qed.

  Local Lemma acquire_spec γ lk R Φ :
    is_lock γ lk R -∗
    (locked γ ∗ R -∗ Φ #()) -∗
    WP acquire lk @ Later; ⊤ {{ Φ }}.
  Proof.
    iIntros "#Hl HΦ". iLöb as "IH". iApply wp_App. iNext.
    simpl. 
    wp_apply (try_acquire_spec with "Hl"). iIntros ([]).
    - iIntros "[Hlked HR]".
      iApply wp_IfTrue. iNext. iApply wp_val. iApply "HΦ". by iFrame.
    - iIntros "_".
      iApply wp_IfFalse. iNext.
      iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Local Lemma release_spec γ lk R :
    is_lock γ lk R ∗ locked γ ∗ R -∗
    WP release lk @ Later; ⊤ {{ v, ⌜v = #()⌝ }}.
  Proof.
    iIntros "(Hlock & Hlocked & HR)".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /release /=. iApply wp_App. iNext. iInv N as (b) "[>Hl _]".
    wp_apply (wp_Store with "Hl").
    { solve_ndisj. }
    iIntros (r ->) "Hl".
    iModIntro. by iFrame.
  Qed.
End proof.
