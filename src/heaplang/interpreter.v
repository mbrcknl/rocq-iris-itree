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

(* FIXME: Order arguments consistently. *)

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

(** The interpreter produces an execution. *)
Lemma heaplang_interpreter_execution e σ fuel later_fuel x :
  heaplang_interpreter σ fuel later_fuel e = inl x →
  ∃ te, te ≈ Ret x ∧ heaplang_eval e σ later_fuel te.
Proof.
  intros Hint.
  exists (heaplang_eval_itree σ later_fuel e).
  rewrite /heaplang_interpreter in Hint.
  case_match eqn:Heq'; last discriminate.
  apply exec_spec in Heq'. simplify_eq.
  split; first done.
  apply heaplang_ifn_irel.
Qed.

(** Partial soundness theorem for the interpreter. *)
Lemma heaplang_interpreter_partial_soundness e σ fuel later_fuel φ :
  partially_adequate e σ φ →
  match heaplang_interpreter σ fuel (Some later_fuel) e with
  | inr Timeout => True
  | inl (inr UbCrash) => False
  | inl (inl (inr LaterExhausted)) => True
  | inl (inl (inl (σ, inl v))) => φ v
  (* TODO: This case is never reached. Maybe it would make sense to strengthen
  the [True] to [False], incurring extra proof effort. *)
  | inl (inl (inl (σ, inr LastThreadKilled))) => True
  end.
Proof.
  intros Had.
  destruct (heaplang_interpreter _ _ _ _) as [x|] eqn:Heq; last by case_match.
  apply heaplang_interpreter_execution in Heq as (te&Heutt&Heval).
  ospecialize (Had later_fuel te x _); first eauto.
  repeat case_match; eauto.
Qed.

(** Total soundness theorem for the interpreter. *)
Lemma heaplang_interpreter_total_soundness e σ φ :
  totally_adequate e σ φ →
  ∃ n, ∀ fuel, fuel ≥ n →
  match heaplang_interpreter σ fuel None e with
  | inr Timeout => False
  | inl (inr UbCrash) => False
  | inl (inl (inr LaterExhausted)) => False
  | inl (inl (inl (σ, inl v))) => φ v
  (* TODO: This case is never reached. Maybe it would make sense to strengthen
  the [True] to [False], incurring extra proof effort. *)
  | inl (inl (inl (σ, inr LastThreadKilled))) => True
  end.
Proof.
  intros Had.
  odestruct (Had (heaplang_eval_itree σ None e) _) as (x&Heutt&Hφ).
  { apply heaplang_ifn_irel. }
  apply exec_ret in Heutt as [fuel Heq].
  exists fuel. intros fuel' Hlt.
  rewrite /heaplang_interpreter (exec_stable fuel' fuel) // Heq //.
  by repeat case_match.
Qed.
