From ITree Require Import ITree Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi ub itree choice state later handler void interpreter.
From iris.itree.threadpool Require Import handler interleaving scheduler.
From iris.itree.heaplang Require Import lang adequacy.

Definition heaplang_ifn {R} (σ : state) (n : option nat) (t : itree heaplangE R) :
  itree voidE ((state * (R + last_thread_killed)) + later_exhausted + ub_crash) :=
  ub_ifn (insert_voidE (later_ifn n (state_ifn σ (demonic_ifn (threadpool_ifn t))))).

Lemma heaplang_ifn_irel {R} (t : itree heaplangE R) (σ : state) (n : option nat) :
  heaplang_irel σ n t (heaplang_ifn σ n t).
Proof.
  eexists. eexists. eexists.
  split; first apply threadpool_ifn_irel.
  split; first apply demonic_ifn_irel.
  split; first apply state_ifn_irel.
  reflexivity.
Qed.

Variant timeout := Timeout.

Definition heaplang_eval_itree σ n e :=
  heaplang_ifn σ (Some n) (v ← compile_expr e ; yield_if_not_val e ;; Ret v).

Definition heaplang_interpreter σ (n : nat) (e : expr) : (state * (val + last_thread_killed)) + ub_crash + timeout :=
  match exec n (heaplang_eval_itree σ n e) with
  | None => inr Timeout
  | Some (inl (inr LaterExhausted)) => inr Timeout
  | Some (inl (inl r)) => inl (inl r)
  | Some (inr UbCrash) => inl (inr UbCrash)
  end.

Lemma heaplang_interpreter_adequacy `{!invGS Σ} `{!heaplangHGS Σ} m e σ n Φ :
  state_interp σ -∗
  £ n -∗
  heap_inv -∗
  WP e @ m; ⊤ {{ Φ }} -∗
  |={⊤, ∅}=>
    match heaplang_interpreter σ n e with
    | inr Timeout => True
    | inl (inr UbCrash) => False
    | inl (inl (σ, r)) => state_interp σ ∗
        match r with | inl v => Φ v | inr LastThreadKilled => True end
    end.
Proof.
  iIntros "Hstate Hlc Hinv Hwp".
  iDestruct (heaplang_adequacy_eval e σ (heaplang_eval_itree σ n e) with "Hstate [Hlc] Hinv Hwp") as "Heval".
  { apply heaplang_ifn_irel. }
  { eauto. }
  { done. }
  iMod "Heval" as "[%v [%Heval HΦ]]".
  rewrite /heaplang_interpreter. destruct (exec n (heaplang_eval_itree σ n e)) eqn:Heq.
  * apply exec_eutt with (t' := (Ret v)) in Heq as [n' Heq]; last done.
    destruct n'; first done. injection Heq as <-.
    destruct v.
    + destruct s.
      -- iMod "HΦ". destruct p as [σ0 [v|[]]]; iApply fupd_mask_intro; eauto.
      -- by destruct l.
    + by destruct u.
  * destruct v; eauto.
Qed.

Lemma heaplang_interpreter_soundness `{!invGpreS Σ} `{!heaplangHGpreS Σ} m e σ n φ :
  (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ m; ⊤ {{ v, ⌜φ v⌝ }}) →
  match heaplang_interpreter σ n e with
  | inr Timeout => True
  | inl (inr UbCrash) => False
  | inl (inl (_, inl v)) => φ v
  | inl (inl (_, inr LastThreadKilled)) => True
  end.
Proof.
  intros Hwp. apply: (heaplang_soundness n).
  iIntros (? ?) "#Hinv Hstate Hlc".
  iDestruct Hwp as "Hwp".
  iDestruct (heaplang_interpreter_adequacy m e σ n with "Hstate Hlc Hinv Hwp") as "Hφ".
  iMod "Hφ". iModIntro.
  iApply step_fupdN_intro; first done. iModIntro.
  destruct (heaplang_interpreter σ n e) as [[[σ' [v|[]]]|[]]|[]]; eauto.
  iDestruct "Hφ" as "[_ $]".
Qed.
