(* Adapted from [iris/iris_heap_lang/lib/spawn.v]. *)

From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

From iris.itree.heaplang Require Export definition lang program_logic tactics.
From iris.itree Require Import heap step.

Definition spawn_ : val :=
  λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #())) ;; "c".
Definition join : val :=
  rec: "join" "c" :=
    match: !"c" with
      SOME "x" => "x"
    | NONE => "join" "c"
    end.

(** The CMRA & functor we need. *)
(* Not bundling heapGS, as it may be shared with other users. *)
Class spawnG Σ := SpawnG { spawn_tokG : inG Σ (exclR unitO) }.
Local Existing Instance spawn_tokG.

Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!invGS_gen hlc Σ, !heaplangHGS Σ, !spawnG Σ}.

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ lv, l ↦ lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ own γ (Excl ()))).

Definition inv_name : namespace :=
  nroot .@ "spawn_".

Definition join_handle (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ, own γ (Excl ()) ∗ inv inv_name (spawn_inv γ l Ψ).

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn__spec (Ψ : val → iProp Σ) (f : val) :
  WP f #() @ Later; ⊤ {{ Ψ }} -∗
  WP spawn_ f @ Later; ⊤ {{ v, ∃ (l : loc), ⌜v = #l⌝ ∧ join_handle l Ψ }}.
Proof.
  iIntros "Hf". rewrite /spawn_ /=.
  iApply wp_App. iApply lat_intro. simpl.
  wp_apply wp_InjL. wp_apply wp_Alloc; try done. iIntros (l) "Hl".
  wp_apply wp_Rec. wp_apply wp_App. simpl.
  iApply fupd_wp.
  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iMod (inv_alloc inv_name _ (spawn_inv γ l Ψ) with "[Hl]") as "#?".
  { iNext. iExists NONEV. iFrame; eauto. }
  iModIntro. wp_apply (wp_Fork with "[Hγ]").
  { iApply lat_intro.
    wp_apply wp_Rec. wp_apply wp_App. simpl.
    iApply wp_val. iExists l. iSplit; first done.
    rewrite /join_handle. eauto.
  }
  wp_bind (f _)%E. iApply wp_wand; last done. iIntros (v) "HΨ".
  wp_apply wp_InjR.
  iInv inv_name as (v') "[>Hl _]".
  iApply (wp_Store with "Hl").
  { solve_ndisj. }
  iNext. iIntros (r ->) "Hl". 
  iModIntro. iSplitL; last done. iNext. rewrite /spawn_inv.
  iExists (InjRV v). iFrame. iRight.
  iExists _. iSplitR; first done. by iLeft.
Qed.

Lemma join_spec (Ψ : val → iProp Σ) l :
  join_handle l Ψ -∗
  WP join #l @ Later; ⊤ {{ Ψ  }}.
Proof.
  iIntros "[%γ [Hγ #?]]".
  iLöb as "IH". rewrite /join.
  iApply wp_App. simpl. iNext.
  wp_bind (! _)%E. iInv inv_name as (v) "[>Hl Hinv]".
  iApply (wp_Load with "Hl").
  { solve_ndisj. }
  iNext. iIntros "Hl". 
  iDestruct "Hinv" as "[%|Hinv]"; subst.
  - iModIntro. iSplitL "Hl"; [iNext; iExists _; iFrame; eauto|].
    iApply wp_CaseL. iNext.
    wp_apply wp_Rec. wp_apply wp_App. simpl.
    iApply ("IH" with "Hγ").
  - iDestruct "Hinv" as (v' ->) "[HΨ|Hγ']".
    + iModIntro. iSplitL "Hl Hγ"; [iNext; iExists _; iFrame; eauto|].
      iApply wp_CaseR. iNext.
      wp_apply wp_Rec. wp_apply wp_App. simpl.
      by iApply wp_val.
    + iCombine "Hγ Hγ'" gives %[].
Qed.
End proof.
