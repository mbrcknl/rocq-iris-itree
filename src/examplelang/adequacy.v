From ITree Require Import ITree Recursion RecursionFacts InterpFacts TranslateFacts Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.bi Require Import weakestpre.
From iris.itree Require Import wpi ub itree choice state step handler void heap.
From iris.itree.threadpool Require Import ctrace handler interleaving.
From iris.itree.examplelang Require Import lang program_logic.

(** An execution outcome of a ExampleLang program. *)
Definition Outcome R : Type :=
  (heap.heap val * (R + last_thread_killed + ub_crash)).
(** An execution of a ExampleLang program. *)
Definition Execution R : Type :=
  itree voidE (Outcome R).

Definition examplelang_irel {R} (σ : heap.heap val) (n : option nat) (t : itree exampleE R)
  (te : Execution R) : Prop :=
  ∃ t1 t2 t3,
    threadpool_irel t t1 ∧
    ub_irel t1 t2 ∧
    state_irel σ t2 t3 ∧
    demonic_irel (insert_voidE t3) te.

Section adequacy.
  Context {Σ} `{!invGS Σ} `{!exampleHGS Σ}.

  Lemma wp_adequacy_irel R t σ te (Φ : R → iProp Σ) n :
    examplelang_irel σ n t te →
    state_interp σ -∗
    WPi t @ exampleH; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ x, ⌜te ≈ Ret x⌝ ∗
      match x with
      | (_, inr UbCrash) => |={∅, ⊤}=> False
      | (σ, inl (inl v)) => |={∅, ⊤}=> state_interp σ ∗ Φ v
      | (σ, inl (inr LastThreadKilled)) => |={∅, ⊤}=> state_interp σ
      end.
  Proof.
    iIntros ((?&?&?&?&->&?&?)) "Hs Hwp".
    iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (ub_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (heap_adequacy with "Hs Hwp") as "Hwp"; [done|].
    rewrite -wpi_clear_mask. iMod "Hwp".
    iDestruct (wpi_insert_voidE with "Hwp") as "Hwp".
    iDestruct (demonic_adequacy with "Hwp") as "Hwp"; [done|].
    iApply void_adequacy_empty.
    iApply wpi_wand; last done.
    iIntros (?) "HΦ". repeat case_match; eauto.
    - by iMod "HΦ" as "[$ _]".
    - by iMod "HΦ" as "[_ $]".
  Qed.
End adequacy.
