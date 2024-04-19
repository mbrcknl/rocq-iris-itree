From iris.itree Require Import wpi.
From iris.itree.threadpool Require Import trace.
From iris.itree.heaplang Require Import lang.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.program_logic Require Import language.

Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

(* TODO: The idea is to add that if [tp'] has nowhere to step then [tr] ends in
*        UB, and if [tp'] returns a value, then so does [tr]. *)
Lemma has_trace n tp σ tp' σ' κ :
  nsteps n (tp, σ) κ (tp', σ') →
  length tp > 0 →
  ∃ tr i, is_ctrace tr i (map compile_expr tp).
Proof.
  revert tp σ tp' σ' κ. induction n; intros tp σ tp' σ' κ Hstep Hne.
  { exists CTCut, 0. destruct tp as [|t tp]. { simpl in Hne. lia. }
    exists (compile_expr t). split; first done. constructor. }
  inversion Hstep as [|m [tp1 σ1] [tp2 σ2] [tp3 σ3] ? ? Hstep' Hstep'']. subst.
  inversion Hstep' as [e1 σ1 e2 σ2' efs t1 t2 Htp' Htp2' Hprim].
  injection Htp'. intros -> ->. clear Htp'.
  injection Htp2'. intros -> ->. clear Htp2'.
  inversion Hprim as [K e1' e2' He1 He2 Hbase]. subst. simpl in K, e1', e2'.
  clear Hstep'' Hstep' Hprim.
  rewrite map_app /=.
  Set Typeclasses Debug.
  rewrite compile_expr_bind.
  induction K.
  -

Lemma adequacy_not_stuck e σ M Φ :
  ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap) -∗
  heap_inv -∗
  WPi compile_expr e @ heaplangH; M {{ Φ }} -∗
  |={M}=> ⌜not_stuck e σ⌝.
Proof.
  iIntros "Hauth #Hinv Hwp".
  iInduction e as [] "IH" forall (σ) "Hauth".
  - iModIntro. iPureIntro. by left.
  - 
    rewrite /compile_expr rec_as_interp /=.
    setoid_rewrite interp_vis.
    simpl.
