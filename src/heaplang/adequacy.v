From ITree Require Import ITree Recursion RecursionFacts InterpFacts TranslateFacts Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi ub itree choice state later handler void.
From iris.itree.threadpool Require Import ctrace handler interleaving.
From iris.itree.heaplang Require Import lang.

Definition heaplang_irel {R} (σ : state) (n : option nat) (t : itree heaplangE R)
  (te : itree voidE ((state * (R + last_thread_killed)) + later_exhausted + ub_crash)) : Prop :=
  ∃ t1 t2 t3,
    threadpool_irel t t1 ∧
    demonic_irel t1 t2 ∧
    state_irel σ t2 t3 ∧
    te = ub_ifn (insert_voidE (later_ifn n t3)).

Definition heaplang_eval (e : expr) (σ : state) (n : option nat)
  (* TODO: Can remove the itree here? How would we represent diverging
  programs when not using later? *)
  (exec: itree voidE ((state * (val + last_thread_killed)) + later_exhausted + ub_crash)) : Prop :=
  heaplang_irel σ n (v ← compile_expr e ; yield_if_not_val e ;; Ret v) exec.

Section adequacy.
  Context {Σ} `{!invGS Σ} `{!heaplangHGS Σ}.

  Lemma heaplang_adequacy_irel R t σ te (Φ : R → iProp Σ) n lat :
    heaplang_irel σ n t te →
    (lat = Later → is_Some n) →
    state_interp σ -∗
    £ (default 0 n) -∗
    WPi t @ heaplangH lat; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ v, ⌜te ≈ Ret v⌝ ∗
      match v with
      | inr UbCrash => False
      | inl (inr LaterExhausted) => ⌜is_Some n⌝
      | inl (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros ((?&?&?&?&?&?&Hte) ?) "Hs Hlc Hwp".
    iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (demonic_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (state_adequacy with "Hs Hwp") as "Hwp"; [done|].
    rewrite -wpi_clear_mask. iMod "Hwp".
    iDestruct (later_adequacy_empty with "Hwp Hlc") as "Hwp"; [done|].
    iDestruct (voidE_adequacy with "Hwp") as "Hwp".
    iDestruct (ub_adequacy with "Hwp") as "Hwp".
    iApply voidE_terminates_empty_mask.
    by rewrite Hte.
  Qed.

  Lemma heaplang_adequacy_eval e σ te (Φ : val → iProp Σ) n lat :
    heaplang_eval e σ n te →
    (lat = Later → is_Some n) →
    state_interp σ -∗
    £ (default 0 n) -∗
    heap_inv -∗
    WP e @ lat; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ v, ⌜te ≈ Ret v⌝ ∗
      match v with
      | inr UbCrash => False
      | inl (inr LaterExhausted) => ⌜is_Some n⌝
      | inl (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros (? ?) "Hs Hlc Hinv Hwp".
    iApply (heaplang_adequacy_irel with "Hs Hlc"); [done..|].
    iApply wpi_bind. iApply wpi_wand. 2: { rewrite wp_heaplang_eq. by iApply "Hwp". }
    iIntros (?) "?". iApply wpi_bind. iApply wpi_yield_if_not_val. by iApply wpi_ret.
  Qed.
End adequacy.
