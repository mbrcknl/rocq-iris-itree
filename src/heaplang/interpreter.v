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
  heaplang_ifn σ later_fuel (v ← compile_expr e ; yield_if_not_val e ;; Ret v).

Definition heaplang_interpreter σ (fuel : nat) (later_fuel : option nat) (e : expr) : (state * (val + last_thread_killed)) + later_exhausted + ub_crash + timeout :=
  match exec fuel (heaplang_eval_itree σ later_fuel e) with
  | None => inr Timeout
  | Some x => inl x
  end.

Lemma heaplang_interpreter_adequacy `{!invGS Σ} `{!heaplangHGS Σ} m e σ fuel later_fuel Φ :
  (m = Later → is_Some later_fuel) →
  state_interp σ -∗
  £ (default 0 later_fuel) -∗
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
  iIntros (Hlat) "Hstate Hlc Hinv Hwp".
  iDestruct (heaplang_adequacy_eval e σ (heaplang_eval_itree σ later_fuel e) with "Hstate [Hlc] Hinv Hwp") as "Heval".
  { apply heaplang_ifn_irel. }
  { eauto. }
  { done. }
  iMod "Heval" as "[%v [%Heval HΦ]]".
  rewrite /heaplang_interpreter. destruct (exec fuel (heaplang_eval_itree σ later_fuel e)) eqn:Heq.
  * apply exec_eutt with (t' := (Ret v)) in Heq as [n' Heq]; last done.
    destruct n'; first done. injection Heq as <-.
    destruct v.
    + destruct s.
      -- iMod "HΦ". destruct p as [σ0 [v|[]]]; iApply fupd_mask_intro; eauto.
      -- by destruct l.
    + by destruct u.
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
  iMod lc_zero as "Hlc".
  iDestruct (heaplang_adequacy_eval e σ (heaplang_eval_itree σ None e) with "Hstate [Hlc] Hinv Hwp") as "Heval".
  { apply heaplang_ifn_irel. }
  { intros. discriminate. }
  { done. }
  iMod "Heval" as "[%v [%Heval HΦ]]".
  symmetry in Heval. apply exec_eutt with (r := v) (n := 1) in Heval as [fuel Heq]; last done.
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

From iris.heap_lang Require Import proofmode notation.

Compute heaplang_interpreter inhabitant 99 (ref #1).
Compute heaplang_interpreter inhabitant 99 (let: "x" := ref #1 in !"x").
Compute heaplang_interpreter inhabitant 99 (let: "x" := ref #1 in "x" <- !"x";; !"x").
Compute heaplang_interpreter inhabitant 99 (let: "x" := ref #1 in !"x").
