From ITree Require Import ITree Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi ub itree choice state later handler void interpreter.
From iris.itree.threadpool Require Import handler interleaving scheduler.
From iris.itree.heaplang Require Import lang adequacy.

Definition heaplang_ifn {R} (σ : state) (later_fuel : option nat) (t : itree heaplangE R) :
  itree voidE ((state * (R + last_thread_killed)) + later_exhausted + ub_crash) :=
  ub_ifn (insert_voidE (later_ifn later_fuel (state_ifn σ (demonic_ifn (threadpool_ifn t))))).

Lemma heaplang_ifn_irel {R} (t : itree heaplangE R) (σ : state) (later_fuel : option nat) :
  heaplang_irel σ later_fuel t (heaplang_ifn σ later_fuel t).
Proof.
  eexists. eexists. eexists.
  split; first apply threadpool_ifn_irel.
  split; first apply demonic_ifn_irel.
  split; first apply state_ifn_irel.
  reflexivity.
Qed.

Variant timeout := Timeout.

Definition heaplang_eval_itree σ later_fuel e :=
  heaplang_ifn σ later_fuel (compile_expr_yield e).

Definition heaplang_interpreter σ (fuel : nat) (later_fuel : option nat) (e : expr) : (state * (val + last_thread_killed)) + later_exhausted + ub_crash + timeout :=
  match exec fuel (heaplang_eval_itree σ later_fuel e) with
  | None => inr Timeout
  | Some x => inl x
  end.

Lemma heaplang_interpreter_adequacy `{!invGS Σ} `{!heaplangHGS Σ} m e σ fuel later_fuel Φ :
  (⌜m = Later⌝ → match later_fuel with Some n => £ n | None => False end) -∗
  state_interp σ -∗
  heap_inv -∗
  WP e @ m; ⊤ {{ Φ }} -∗
  |={⊤, ∅}=>
    match heaplang_interpreter σ fuel later_fuel e with
    | inr Timeout => True
    | inl (inr UbCrash) => False
    | inl (inl (inr LaterExhausted)) => ⌜is_Some later_fuel⌝
    | inl (inl (inl (σ, r))) => state_interp σ ∗
        match r with | inl v => Φ v | inr LastThreadKilled => True end
    end.
Proof.
  iIntros "Hlc Hstate Hinv Hwp".
  iMod (heaplang_adequacy_eval e σ (heaplang_eval_itree σ later_fuel e) with "[Hlc] Hstate Hinv Hwp") as "[%v [%Heval HΦ]]".
  { apply heaplang_ifn_irel. }
  { eauto. }
  apply exec_ret in Heval as [n Heq].
  rewrite /heaplang_interpreter. destruct (exec fuel (heaplang_eval_itree σ later_fuel e)) eqn:Heq'.
  * apply exec_agree with (m := fuel) (r1 := s) in Heq as ->.
    destruct v.
    + destruct s.
      -- iMod "HΦ". destruct p as [σ0 [v|[]]]; iApply fupd_mask_intro; eauto.
      -- by destruct l.
    + by destruct u.
    + done.
  * destruct v; eauto.
Qed.

Lemma heaplang_interpreter_adequacy_termination `{!invGS Σ} `{!heaplangHGS Σ} e σ Φ :
  state_interp σ -∗
  heap_inv -∗
  WP e @ Identity; ⊤ {{ Φ }} -∗
  |={⊤, ∅}=>
    ⌜∃ n, ∀ fuel, fuel ≥ n →
      match heaplang_interpreter σ fuel None e with
      | inr Timeout => False
      | inl _ => True
      end⌝.
Proof.
  iIntros "Hstate Hinv Hwp".
  iMod (heaplang_adequacy_eval e σ (heaplang_eval_itree σ None e) with "[] Hstate Hinv Hwp") as "[%v [%Heval HΦ]]".
  { apply heaplang_ifn_irel. }
  { iIntros ([=]). }
  apply exec_ret in Heval as [fuel Heq].
  iModIntro. iExists fuel. iIntros (fuel' Hlt).
  rewrite /heaplang_interpreter (exec_stable fuel' fuel) // Heq //.
Qed.

Lemma heaplang_interpreter_soundness_termination `{!invGpreS Σ} `{!heaplangHGpreS Σ} e σ φ :
  (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Identity; ⊤ {{ v, ⌜φ v⌝ }}) →
  ∃ n, ∀ fuel, fuel ≥ n → match heaplang_interpreter σ fuel None e with
  | inr Timeout => False
  | inl _ => True
  end.
Proof.
  intros Hwp. apply: (heaplang_soundness 0).
  iIntros (? ?) "#Hinv Hstate Hlc".
  iDestruct Hwp as "Hwp".
  by iDestruct (heaplang_interpreter_adequacy_termination e σ with "Hstate Hinv Hwp") as "Hφ".
Qed.
