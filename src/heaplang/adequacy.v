From ITree Require Import ITree Recursion RecursionFacts InterpFacts TranslateFacts Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.itree Require Import wpi ub itree choice state later handler.
From iris.itree.threadpool Require Import ctrace handler interleaving.
From iris.itree.heaplang Require Import lang.

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

Lemma normalize_itree_translate_Ret {E F R} h (x : R) :
  NormalizeITree true (translate (E:=E) (F:=F) h (Ret x)) (Ret x).
Proof. constructor. by rewrite translate_ret. Qed.
Global Hint Resolve normalize_itree_translate_Ret : itree_auto.

Lemma normalize_itree_translate_Tau {E F R} h (t : itree E R) t' p :
  NormalizeITree p (translate h t) t' →
  NormalizeITree true (translate (E:=E) (F:=F) h (Tau t)) t'.
Proof. move => [Heq]. constructor. by rewrite -Heq translate_tau tau_eutt. Qed.
Global Hint Resolve normalize_itree_translate_Tau : itree_auto.

Lemma normalize_itree_translate_Vis {E F R} A e h (k : A →itree E R) t' p :
  NormalizeITree p (Vis (h _ e) (λ x, translate h (k x))) t' →
  NormalizeITree true (translate (E:=E) (F:=F) h (Vis e k)) t'.
Proof. move => [Heq]. constructor. by rewrite -Heq translate_vis. Qed.
Global Hint Resolve normalize_itree_translate_Vis : itree_auto.


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


Definition heaplang_irel {R} (t : itree heaplangE R) (σ : state) (n : option nat)
  (te : itree voidE (option ((state * (R + last_thread_killed)) + later_exhausted))) : Prop :=
  ∃ t1 t2 t3,
    interleaves 0 [t] t1 ∧
    demonic_instantiates t1 t2 ∧
    eval σ t2 t3 ∧
    te ≈ sandbox (insert_voidE (later_ifn n t3)).

Definition heaplang_eval (e : expr) (σ : state) (n : option nat)
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
      | Some (inr _) => ⌜lat = Later⌝
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
    WPi compile_expr e @ heaplangH lat; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ v, ⌜te ≈ Ret v⌝ ∗
      match v with
      | None => False
      | Some (inr _) => ⌜lat = Later⌝
      | Some (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros (? ?) "Hs Hlc Hwp".
    iApply (heaplang_adequacy_irel with "Hs Hlc"); [done..|].
    iApply wpi_bind. iApply wpi_wand; [|done]. iIntros (?) "?".
  Admitted.
End adequacy.
