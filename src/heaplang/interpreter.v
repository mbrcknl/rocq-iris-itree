From ITree Require Import ITree Eqit.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import wpi ub itree choice state later handler void interpreter.
From iris.itree.threadpool Require Import handler interleaving scheduler.
From iris.itree.heaplang Require Import lang adequacy.

(** Interpretation function for [heaplangE], obtained compositionally by
composing interpretation functions for the various event types. *)
Definition heaplang_ifn {R} (σ : state) (later_fuel : option nat) (t : itree heaplangE R) :
  itree voidE ((state * (R + last_thread_killed)) + later_exhausted + ub_crash) :=
  ub_ifn (insert_voidE (later_ifn later_fuel (state_ifn σ (demonic_ifn (threadpool_ifn t))))).

(** The function [heaplang_ifn] instantiates the relation [heaplang_irel]. *)
Lemma heaplang_ifn_irel {R} (t : itree heaplangE R) (σ : state) (later_fuel : option nat) :
  heaplang_irel σ later_fuel t (heaplang_ifn σ later_fuel t).
Proof.
  eexists. eexists. eexists.
  split; first apply threadpool_ifn_irel.
  split; first apply demonic_ifn_irel.
  split; first apply state_ifn_irel.
  reflexivity.
Qed.

(** Return type to mark that we exceeded the limit for the number of steps. *)
Variant timeout := Timeout.

(** Convert an heaplang expression [e] to an ITree and evaluate it. *)
Definition heaplang_eval_itree σ later_fuel e : itree voidE ((state * (val + last_thread_killed)) + later_exhausted + ub_crash) :=
  heaplang_ifn σ later_fuel (compile_expr_yield e).

(** Evaluate a heaplang expression [e] at state [σ] in [fuel] computation steps
or less.

There is also a parameter [later_fuel], which optionally controls the number of
[step]s we can encounter. While [fuel] is closer to a measure of the actual
computational effort, [later_fuel] sets a limit for the number of opsem steps
in the evaluation of [e]. *)
Definition heaplang_interpreter σ (fuel : nat) (later_fuel : option nat) (e : expr) : (state * (val + last_thread_killed)) + later_exhausted + ub_crash + timeout :=
  match exec fuel (heaplang_eval_itree σ later_fuel e) with
  | None => inr Timeout
  | Some x => inl x
  end.

(** Adequacy theorem for the interpreter, a corollary to the adequacy theorems
proven in [heaplang/adequacy.v].

This is only partial adequacy, meaning that it does not provide any termination
guarantee. This is instead proven in [heaplang_interpreter_adequacy_termination]. *)
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

(** A version of [heaplang_interpreter_adequacy] outside of the Iris logic. *)
Lemma heaplang_interpreter_soundness `{!invGpreS Σ} `{!heaplangHGpreS Σ} m e σ fuel later_fuel φ :
  (m = Later → is_Some later_fuel) →
  (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ m; ⊤ {{ v, ⌜φ v⌝ }}) →
  match heaplang_interpreter σ fuel later_fuel e with
  | inr Timeout => True
  | inl (inr UbCrash) => False
  | inl (inl (inr LaterExhausted)) => is_Some later_fuel
  | inl (inl (inl (σ, inl v))) => φ v
  (* TODO: This case is never reached. Maybe it would make sense to strengthen
  the [True] to [False], incurring extra proof effort. *)
  | inl (inl (inl (σ, inr LastThreadKilled))) => True
  end.
Proof.
  intros Hfuel Hwp. apply: (heaplang_soundness (default 0 later_fuel)).
  iIntros (? ?) "#Hinv Hstate Hlc".
  iDestruct Hwp as "Hwp".
  iDestruct (heaplang_interpreter_adequacy m e σ fuel later_fuel with "[Hlc] Hstate Hinv Hwp") as "Hφ".
  { iIntros (->). destruct later_fuel; first done. by odestruct (Hfuel _). }
  repeat case_match.
  - iMod "Hφ" as "[_ %Hφ]". iModIntro. by iApply step_fupdN_intro.
  - iMod "Hφ" as "[_ %Hφ]". iModIntro. by iApply step_fupdN_intro.
  - iMod "Hφ" as "%Hlater_fuel". iModIntro. by iApply step_fupdN_intro.
  - iMod "Hφ" as "[]".
  - iMod "Hφ". iModIntro. by iApply step_fupdN_intro.
Qed.

(** If you prove the [WP] of an expression [e] in the termination sensitive
mode [m = Identity], the interpreter will eventually terminate, given enough
fuel. *)
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

(** A version of [heaplang_interpreter_adequacy_termination] outside of the
Iris logic. *)
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
