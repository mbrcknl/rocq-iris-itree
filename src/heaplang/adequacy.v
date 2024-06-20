From ITree Require Import ITree Recursion RecursionFacts InterpFacts TranslateFacts Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi ub itree choice state later handler void.
From iris.itree.threadpool Require Import ctrace handler interleaving.
From iris.itree.heaplang Require Import lang.

Definition heaplang_irel {R} (t : itree heaplangE R) (σ : state) (n : option nat)
  (te : itree voidE (option ((state * (R + last_thread_killed)) + later_exhausted))) : Prop :=
  ∃ t1 t2 t3,
    interleaves 0 [t] t1 ∧
    demonic_instantiates t1 t2 ∧
    eval σ t2 t3 ∧
   (* We need to insert voidE such that the type of sandbox works out. *)
    te ≈ sandbox (insert_voidE (later_ifn n t3)).

Definition heaplang_eval (e : expr) (σ : state) (n : option nat)
  (* TODO: Can remove the itree here? How would we represent diverging
  programs when not using later? *)
  (exec: itree voidE (option ((state * (val + last_thread_killed)) + later_exhausted))) : Prop :=
  heaplang_irel (v ← compile_expr e ; yield_if_not_val e ;; Ret v) σ n exec.

Section adequacy.
  Context {Σ} `{!invGS Σ} `{!heaplangHGS Σ}.

  Lemma heaplang_adequacy_irel R t σ te (Φ : R → iProp Σ) n lat :
    heaplang_irel t σ n te →
    (lat = Later ↔ is_Some n) →
    state_interp σ -∗
    £ (default 0 n) -∗
    WPi t @ heaplangH lat; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ v, ⌜te ≈ Ret v⌝ ∗
      match v with
      | None => False
      | Some (inr LaterExhausted) => ⌜lat = Later⌝
      | Some (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros ((?&?&?&?&?&?&Hte) ?) "Hs Hlc Hwp".
    iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (demonicH_adequate with "Hwp") as "Hwp"; [done|].
    iDestruct (wpi_state with "Hs Hwp") as "Hwp"; [done|].
    rewrite -wpi_clear_mask. iMod "Hwp".
    iDestruct (later_adequacy_empty with "Hwp Hlc") as "Hwp"; [done|].
    iDestruct (voidE_adequacy with "Hwp") as "Hwp".
    iDestruct (ub_adequacy with "Hwp") as "Hwp".
    iApply voidE_terminates_empty_mask.
    by rewrite Hte.
  Qed.

  Lemma heaplang_adequacy_eval e σ te (Φ : val → iProp Σ) n lat :
    heaplang_eval e σ n te →
    (lat = Later ↔ is_Some n) →
    state_interp σ -∗
    £ (default 0 n) -∗
    heap_inv -∗
    WP e @ lat; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ v, ⌜te ≈ Ret v⌝ ∗
      match v with
      | None => False
      | Some (inr LaterExhausted) => ⌜lat = Later⌝
      | Some (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros (? ?) "Hs Hlc Hinv Hwp".
    iApply (heaplang_adequacy_irel with "Hs Hlc"); [done..|].
    iApply wpi_bind. iApply wpi_wand. 2: { rewrite wp_heaplang_eq. by iApply "Hwp". }
    iIntros (?) "?". iApply wpi_bind. iApply wpi_yield_if_not_val. by iApply wpi_ret.
  Qed.
End adequacy.
