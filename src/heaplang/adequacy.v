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
  heaplang_irel σ n (compile_expr_yield e) exec.

Section adequacy.
  Context {Σ} `{!invGS Σ} `{!heaplangHGS Σ}.

  Lemma heaplang_adequacy_irel R t σ te (Φ : R → iProp Σ) n m :
    heaplang_irel σ n t te →
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    state_interp σ -∗
    WPi t @ heaplangH m; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ v, ⌜te ≈ Ret v⌝ ∗
      match v with
      | inr UbCrash => False
      | inl (inr LaterExhausted) => ⌜is_Some n⌝
      | inl (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros ((?&?&?&?&?&?&Hte)) "Hlc Hs Hwp".
    iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (demonic_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (state_adequacy with "Hs Hwp") as "Hwp"; [done|].
    rewrite -wpi_clear_mask. iMod "Hwp".
    iDestruct (later_adequacy_empty with "Hlc Hwp") as "Hwp".
    iDestruct (wpi_insert_voidE with "Hwp") as "Hwp".
    iDestruct (ub_adequacy with "Hwp") as "Hwp".
    iApply void_adequacy_empty.
    by rewrite Hte.
  Qed.

  Lemma heaplang_adequacy_eval e σ te (Φ : val → iProp Σ) n m :
    heaplang_eval e σ n te →
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    state_interp σ -∗
    heap_inv -∗
    WP e @ m; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ v, ⌜te ≈ Ret v⌝ ∗
      match v with
      | inr UbCrash => False
      | inl (inr LaterExhausted) => ⌜is_Some n⌝
      | inl (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros (?) "Hlc Hs Hinv Hwp".
    iApply (heaplang_adequacy_irel with "Hlc Hs"); [done..|].
    iApply wpi_bind. iApply wpi_wand. 2: { rewrite wp_heaplang_eq. by iApply "Hwp". }
    iIntros (?) "?". iApply wpi_bind. iApply wpi_yield_if_not_val. by iApply wpi_ret.
  Qed.
End adequacy.
