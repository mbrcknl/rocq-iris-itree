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

Definition totally_adequate {R} (σ : state) (t : itree heaplangE R) (φ : R → Prop) : Prop :=
  ∀ te, heaplang_irel σ None t te → ∃ x, te ≈ Ret x ∧
    match x with
    | inr UbCrash => False
    | inl (inr LaterExhausted) => False
    | inl (inl (σ, inl v)) => φ v
    | inl (inl (σ, inr _)) => True
    end.

Definition partially_adequate {R} (σ : state) (t : itree heaplangE R) (φ : R → Prop) : Prop :=
  ∀ n te x, heaplang_irel σ (Some n) t te ∧ te ≈ Ret x →
    match x with
    | inr UbCrash => False
    | inl (inr LaterExhausted) => True
    | inl (inl (σ, inl v)) => φ v
    | inl (inl (σ, inr _)) => True
    end.

(* FIXME: would be nice to have (put LaterE as the last event and prove
          the following intermediate lemma)
Lemma remove_timeout {R E} (t : itree (LaterE +' E) R) n r :
  later_ifn n t ≈ Ret(inl r) →
  later_ifn None t ≈ Ret(inl r).
Proof. ... Qed.
Lemma totally_adequate_weaken {R} σ (t : itree heaplangE R) φ :
  totally_adequate σ t φ →
  partially_adequate σ t φ.
Proof.
  intros Htotal n te [[x|[]]|[]] [Hrel Heutt].
  specialize (Htotal te Hrel).
  - case_match. case_match; eauto.
*)

Section adequacy.
  Context {Σ} `{!invGS Σ} `{!heaplangHGS Σ}.

  Lemma heaplang_adequacy_irel R t σ te (Φ : R → iProp Σ) n m :
    heaplang_irel σ n t te →
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    state_interp σ -∗
    WPi t @ heaplangH m; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ x, ⌜te ≈ Ret x⌝ ∗
      match x with
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
    |={⊤, ∅}=> ∃ x, ⌜te ≈ Ret x⌝ ∗
      match x with
      | inr UbCrash => False
      | inl (inr LaterExhausted) => ⌜is_Some n⌝
      | inl (inl σr) => |={∅, ⊤}=> let (σ, r) := σr in state_interp σ ∗
          match r with | inl v => Φ v | inr _ => True end
      end.
  Proof.
    iIntros (?) "Hlc Hs Hinv Hwp".
    iApply (heaplang_adequacy_irel with "Hlc Hs"); [done..|].
    iApply wpi_bind. iApply wpi_wand. 2: { rewrite wp_heaplang_unfold. by iApply "Hwp". }
    iIntros (?) "?". iApply wpi_bind. iApply wpi_yield_if_not_val. by iApply wpi_ret.
  Qed.
End adequacy.

Section soundness.
  Context {Σ} `{!invGpreS Σ} `{!heaplangHGpreS Σ}.

  Lemma heaplang_partial_soundness e σ φ :
    (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Later; ⊤ {{ v, ⌜φ v⌝ }}) →
    partially_adequate σ (compile_expr_yield e) φ.
  Proof.
    intros Hwp n te x [Hirel Heutt].
    apply: (heaplang_soundness n). iIntros (? ?) "#Hinv Hst Hlc".
    iDestruct (Hwp _ _) as "Hwp".
    iDestruct (heaplang_adequacy_eval with "[Hlc] Hst Hinv Hwp") as "Had".
    { apply Hirel. }
    { by iIntros ([]). }
    iMod "Had" as "[%y [%Heutt' Had]]".
    rewrite Heutt in Heutt'. apply eutt_inv_Ret in Heutt' as <-.
    repeat case_match.
    - iMod "Had" as "[_ Had]". iApply step_fupdN_intro; first done. 
      iApply fupd_mask_intro; first done. by iIntros "_ !>".
    - iApply step_fupdN_intro; first done. iModIntro. by iModIntro.
    - iApply step_fupdN_intro; first done. iModIntro. by iModIntro.
    - iApply step_fupdN_intro; first done. iModIntro. by iModIntro.
  Qed.

  Lemma heaplang_total_soundness e σ φ :
    (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Identity; ⊤ {{ v, ⌜φ v⌝ }}) →
    totally_adequate σ (compile_expr_yield e) φ.
  Proof.
    intros Hwp te Hirel.
    apply: (heaplang_soundness 0). iIntros (? ?) "#Hinv Hst Hlc".
    iDestruct (Hwp _ _) as "Hwp".
    iDestruct (heaplang_adequacy_eval with "[Hlc] Hst Hinv Hwp") as "Had".
    { apply Hirel. }
    { iIntros ([=]). }
    iMod "Had" as "[%x [%Heutt Had]]".
    iApply step_fupdN_intro; first done. 
    iExists x. repeat case_match; eauto.
    - iMod "Had" as "[_ %Hφ]".
      iApply fupd_mask_intro; first done. by iIntros "_".
    - iDestruct "Had" as "%Had". destruct Had as [? [=]].
  Qed.
End soundness.

Instance state_EqDecision :
  EqDecision state.
Proof.
  intros [σ1 p1] [σ2 p2].
  destruct (decide (σ1 = σ2)) as [Heq|Hneq].
  - destruct (decide (p1 = p2)) as [Heq'|Hneq'].
    * left. by f_equiv.
    * right. intros Heq'. by injection Heq' as -> ->.
  - right. intros Heq. by injection Heq as -> ->.
Qed.

Section trace.
  Context {R : Type}.

  (** Extract a trace for the interpreted ITree. *)
  Definition interp_tr_heaplang σ n (tr : ctrace sequential_heaplangE R) : option (trace voidE ((state * (R + last_thread_killed)) + later_exhausted + ub_crash)) :=
    (λ tr', interp_tr_ub (insert_voidE_tr (interp_tr_later n tr'))) <$> (interp_tr_state σ (interp_tr (sequencify tr))).

  (** Construct a relational interpretation from a trace. *)
  Lemma heaplang_trace (tr : ctrace sequential_heaplangE R) (t : itree heaplangE R) tr' σ n :
    interp_tr_heaplang σ n tr = Some tr' →
    is_ctrace tr 0 [t] →
    ∃ (te : itree voidE ((state * (R + last_thread_killed)) + later_exhausted + ub_crash)),
      heaplang_irel σ n t te ∧ is_trace tr' te.
  Proof.
    intros Heq Htr.
    rewrite /interp_tr_heaplang in Heq.
    destruct (interp_tr_state σ (interp_tr (sequencify tr))) as [tr''|] eqn:Heq'; try discriminate.
    simpl in Heq. injection Heq as <-.
    apply threadpool_trace in Htr as (t1&Hint&Htr).
    eapply demonic_trace in Htr as (t2&Hinst&Htr).
    apply state_trace with (s := σ) (tr' := tr'') in Htr as (t3&Heval&Htr); last done.
    apply later_trace with (n := n) in Htr.
    apply insert_voidE_trace in Htr.
    apply ub_trace in Htr.
    exists (ub_ifn (insert_voidE (later_ifn n t3))). split; last done.
    exists t1, t2, t3.
    split; first done.
    split; first done.
    split; first done.
    done.
  Qed.
End trace.
