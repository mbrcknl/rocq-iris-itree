From ITree Require Import ITree Recursion RecursionFacts InterpFacts TranslateFacts Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi ub itree choice state step handler void heap.
From iris.itree.threadpool Require Import ctrace handler interleaving.
From iris.itree.heaplang Require Import lang program_logic.

(** An execution outcome of a HeapLang program. *)
Definition Outcome R : Type :=
  (heap.heap val * (R + last_thread_killed + ub_crash)) + step_exhausted.
(** An execution of a HeapLang program. *)
Definition Execution R : Type :=
  itree voidE (Outcome R).

Definition heaplang_irel {R} (σ : heaplang_heap) (n : option nat) (t : itree heaplangE R)
  (te : Execution R) : Prop :=
  ∃ t1 t2 t3 t4,
    threadpool_irel t t1 ∧
    ub_irel t1 t2 ∧
    state_irel σ t2 t3 ∧
    demonic_irel t3 t4 ∧
    step_irel n (insert_voidE t4) te.

Definition heaplang_eval (e : expr) (σ : heaplang_heap) (n : option nat)
  (* TODO: Can remove the itree here? How would we represent diverging
  programs when not using later? *)
  (exec: Execution val) : Prop :=
  heaplang_irel σ n (compile_expr_yield e) exec.

Definition relationally_adequate (n : option nat) (e : expr) (σ : heaplang_heap) (φ : val → Prop) : Prop :=
  ∀ te, heaplang_eval e σ n te → ∃ x, te ≈ Ret x ∧
    match x with
    | inr StepExhausted => is_Some n
    | inl (_, inr UbCrash) => False
    | inl (_, inl (inl v)) => φ v
    | inl (_, inl (inr _)) => True
    end.

(** Intuitively, [e] is totally adequate with respect to heap [σ] and
postcondition [φ] when any execution of [e] terminates without reaching [ub]
with a return value satisfying [φ].  *)
Definition totally_adequate (e : expr) (σ : heaplang_heap) (φ : val → Prop) : Prop :=
  relationally_adequate None e σ φ.

(** Intuitively, [e] is partially adequate with respect to heap [σ] and
postcondition [φ] when no execution of [e] reaches [ub], and any execution that
that terminates returns a value satisfying [φ]. *)
Definition partially_adequate (e : expr) (σ : heaplang_heap) (φ : val → Prop) : Prop :=
  ∀ n, relationally_adequate (Some n) e σ φ.

(* FIXME: would be nice to have (put stepE as the last event and prove
          the following intermediate lemma)
Lemma remove_timeout {R E} (t : itree (stepE +' E) R) n r :
  step_ifn n t ≈ Ret(inl r) →
  step_ifn None t ≈ Ret(inl r).
Proof. ... Qed.
Lemma totally_adequate_weaken {R} σ (t : itree heaplangE R) φ :
  totally_adequate σ t φ →
  partially_adequate σ t φ.
Proof.
  intros Htotal n te [[x|[]]|[]] [Hrel Heutt].
  specialize (Htotal te Hrel).
  - case_match. case_match; eauto.
*)


Section soundness.
  (** Lemma for initializing the ghost state for [WP]. *)
  Lemma heaplangH_init `{!invGS_gen hlc Σ} `{!heaplangHGpreS Σ} σ :
    ⊢ |={∅}=> ∃ _ : heaplangHGS Σ, state_interp σ ∗ [∗ map] k↦v ∈ σ, k ↦? v.
  Proof.
    iMod (heapH_init) as "[%HS [#Hinv [Hst Hpointsto]]]".
    iExists (HeapLangHGS Σ HS).
    by iFrame.
  Qed.

  (** Lemma useful for extract a proposition in classical logic [P] from a
  proof inside the program logic. *)
  Lemma heaplang_soundness n (σ : heaplang_heap) `{!invGpreS Σ} `{!heaplangHGpreS Σ} P:
    (∀ {HG : invGS Σ} {HS : heaplangHGS Σ},
      ⊢ state_interp σ -∗ £ n ={⊤,∅}=∗ |={∅}▷=>^n ⌜P⌝) →
    P.
  Proof.
    move => Hwp.
    eapply uPred.pure_soundness.
    eapply (step_fupdN_soundness_lc _ n n) => ?/=.
    iIntros "Hlc". iMod (fupd_mask_subseteq ∅) as "Hm"; [done|].
    iMod heaplangH_init as (?) "[? ?]".
    iMod "Hm". iApply (Hwp with "[$] [$]").
  Qed.
End soundness.


Section adequacy.
  Context {Σ} `{!invGS Σ} `{!heaplangHGS Σ}.

  Lemma wp_adequacy_irel R t σ te (Φ : R → iProp Σ) n m :
    heaplang_irel σ n t te →
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    state_interp σ -∗
    WPi t @ heaplangH m; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ x, ⌜te ≈ Ret x⌝ ∗
      match x with
      | inr StepExhausted => ⌜is_Some n⌝
      | inl (_, inr UbCrash) => |={∅, ⊤}=> False
      | inl (σ, inl (inl v)) => |={∅, ⊤}=> state_interp σ ∗ Φ v
      | inl (σ, inl (inr LastThreadKilled)) => |={∅, ⊤}=> state_interp σ
      end.
  Proof.
    iIntros ((?&?&?&?&?&->&?&?&->)) "Hlc Hs Hwp".
    iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (ub_adequacy with "Hwp") as "Hwp"; [done|].
    iDestruct (heap_adequacy with "Hs Hwp") as "Hwp"; [done|].
    iDestruct (demonic_adequacy with "Hwp") as "Hwp"; [done|].
    rewrite -wpi_clear_mask. iMod "Hwp".
    iDestruct (wpi_insert_voidE with "Hwp") as "Hwp".
    iDestruct (step_adequacy_empty with "Hlc Hwp") as "Hwp"; [done|].
    iApply void_adequacy_empty.
    iApply wpi_wand; last done.
    iIntros (?) "HΦ". repeat case_match; eauto.
    - by iMod "HΦ" as "[$ _]".
    - by iMod "HΦ" as "[_ $]".
  Qed.

  Lemma wp_adequacy_eval e σ te (Φ : val → iProp Σ) n m :
    heaplang_eval e σ n te →
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    state_interp σ -∗
    WP e @ m; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> ∃ x, ⌜te ≈ Ret x⌝ ∗
      match x with
      | inr StepExhausted => ⌜is_Some n⌝
      | inl (_, inr UbCrash) => |={∅, ⊤}=> False
      | inl (σ, inl (inl v)) => |={∅, ⊤}=> state_interp σ ∗ Φ v
      | inl (σ, inl (inr LastThreadKilled)) => |={∅, ⊤}=> state_interp σ
      end.
  Proof.
    iIntros (?) "Hlc Hs Hwp".
    iApply (wp_adequacy_irel with "Hlc Hs"); [done..|].
    iApply wpi_bind. iApply wpi_wand. 2: { rewrite wp_heaplang_unfold. by iApply "Hwp". }
    iIntros (?) "?". iApply wpi_bind. iApply wpi_yield_if_not_val. by iApply wpi_ret.
  Qed.
End adequacy.

Section soundness.
  Context {Σ} `{!invGpreS Σ} `{!heaplangHGpreS Σ}.

  Lemma wp_partial_soundness e σ φ :
    (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Later; ⊤ {{ v, ⌜φ v⌝ }}) →
    partially_adequate e σ φ.
  Proof.
    intros Hwp n te Heval.
    apply: (heaplang_soundness n). iIntros (? ?) "Hst Hlc".
    iDestruct (Hwp _ _) as "Hwp".
    iDestruct (wp_adequacy_eval with "[Hlc] Hst Hwp") as "Had".
    { apply Heval. }
    { by iIntros ([]). }
    iMod "Had" as "[%x [%Heutt Had]]".
    iApply step_fupdN_intro; first done. 
    iExists x.
    repeat case_match; eauto.
    iMod "Had" as "[_ %Had]".
    iApply fupd_mask_intro; first done. iIntros "_ !>". iPureIntro.
    simplify_eq. split; first done. by repeat case_match.
    iMod "Had" as "[]".
  Qed.

  Lemma wp_total_soundness e σ φ :
    (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Identity; ⊤ {{ v, ⌜φ v⌝ }}) →
    totally_adequate e σ φ.
  Proof.
    intros Hwp te Hirel.
    apply: (heaplang_soundness 0). iIntros (? ?) "Hst Hlc".
    iDestruct (Hwp _ _) as "Hwp".
    iDestruct (wp_adequacy_eval with "[Hlc] Hst Hwp") as "Had".
    { apply Hirel. }
    { iIntros ([=]). }
    iMod "Had" as "[%x [%Heutt Had]]".
    iApply step_fupdN_intro; first done. 
    iExists x. repeat case_match; eauto.
    - iMod "Had" as "[_ %Hφ]".
      iApply fupd_mask_intro; first done. by iIntros "_".
    - by iMod "Had" as "%Had".
    - iDestruct "Had" as "%Had". destruct Had as [? [=]].
  Qed.
End soundness.

Section trace.
  Context {R : Type}.

  (** Extract a trace for the interpreted ITree. *)
  Definition interp_tr_heaplang σ n (tr : ctrace sequential_heaplangE R) : option (trace voidE (Outcome R)) :=
    interp_tr_step n <$> (insert_voidE_tr <$> (interp_tr <$> (interp_tr_state σ (interp_tr_ub (sequencify tr))))).

  (** Construct a relational interpretation from a trace. *)
  Lemma heaplang_trace (tr : ctrace sequential_heaplangE R) (t : itree heaplangE R) tr' σ n :
    interp_tr_heaplang σ n tr = Some tr' →
    is_ctrace tr 0 [t] →
    ∃ (te : Execution R),
      heaplang_irel σ n t te ∧ is_trace tr' te.
  Proof.
    intros Heq Htr.
    rewrite /interp_tr_heaplang in Heq.
    destruct (interp_tr_state σ (interp_tr_ub (sequencify tr))) as [tr''|] eqn:Heq'; try discriminate.
    simpl in Heq. injection Heq as <-.
    apply threadpool_trace in Htr as (t1&Hint&Htr).
    apply ub_trace in Htr as (t2&Hub&Htr).
    apply state_trace with (s := σ) (tr' := tr'') in Htr as H; last done.
    clear Htr. destruct H as (t3&Hst&Htr).
    eapply demonic_trace in Htr as (t4&Hinst&Htr).
    apply insert_voidE_trace in Htr.
    apply step_trace with (n := n) in Htr as (t5&Hlat&Htr).
    exists t5. split; last done.
    by exists t1, t2, t3, t4.
  Qed.
End trace.
