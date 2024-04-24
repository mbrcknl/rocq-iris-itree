From iris.itree Require Import wpi ub.
From iris.itree.threadpool Require Import trace.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.program_logic Require Import language.
From iris.itree.threadpool Require Import handler.
From iris.itree.heaplang Require Import lang.
Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

Lemma compile_Fork {R} e (k : val → itree heaplangE R) :
  (v ← compile_expr (Fork e) ; k v)%itree ≈ vis EFork (λ thread,
    match thread with
    | CurrentThread => k (LitV LitUnit)
    | NewThread =>
        v ← compile_expr e;
        kill_thread
    end
  )%itree.
Proof.
  rewrite /compile_expr !rec_as_interp interp_bind.
  setoid_rewrite interp_trigger. simpl.
  rewrite -bind_trigger bind_bind. f_equiv. intros [|].
  - rewrite interp_ret bind_ret_l //.
  - rewrite rec_as_interp interp_bind bind_bind. f_equiv. intros v.
    rewrite /kill_thread. rewrite interp_vis /= bind_vis bind_vis.
    apply eqit_VisF. intros [].
Qed.

Lemma trace_base_Fork {R} tid (tp : list (itree heaplangE R)) tr e k :
  tp !! tid = Some (v ← compile_expr (Fork e) ; k v)%itree →
  is_ctrace tr tid (<[tid := k (LitV LitUnit)]>tp ++ [(compile_expr e ;; kill_thread)%itree]) →
  is_ctrace (CTFork (compile_expr e ;; kill_thread) tr) tid tp.
Proof.
  intros Htp Htr. eapply is_ctrace_insert; first done; first apply compile_Fork; eauto.
  eexists. split. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1. }
  constructor.
  rewrite /compile_expr rec_as_interp //. rewrite list_insert_insert.
  destruct Htr as (t'&Ht'&Htr).
  simpl in Ht'.
  rewrite lookup_app_l in Ht'; last rewrite insert_length -lookup_lt_is_Some //.
  rewrite list_lookup_insert in Ht'; last by apply lookup_lt_is_Some_1.
  by injection Ht' as <-.
Qed.

Lemma base_BinOp op v1 v2 v3 :
  bin_op_eval op v1 v2 = Some v3 →
  compile_expr (BinOp op (Val v1) (Val v2)) ≈ Ret v3.
Proof.
  intros Hop.
  rewrite /compile_expr !rec_as_interp interp_bind interp_ret bind_ret_l /=
    interp_bind interp_ret bind_ret_l interp_bind interp_ret bind_ret_l
    interp_bind interp_ret bind_ret_l Hop interp_ret //.
Qed.

Lemma base_Beta f_ x_ e v :
  compile_expr (App (Val (RecV f_ x_ e)) (Val v))
  ≈ let e' := (subst' x_ v (subst' f_ (RecV f_ x_ e) e))
     in yield_if_not_val e' ;; compile_expr e'.
Proof.
  rewrite /compile_expr !rec_as_interp interp_bind interp_ret bind_ret_l /=
    interp_bind interp_ret bind_ret_l interp_bind interp_ret bind_ret_l
    interp_bind interp_ret bind_ret_l interp_bind /yield_if_not_val.
  destruct (is_value _) eqn:Heq.
  - rewrite interp_ret !bind_ret_l rec_as_interp.
    setoid_rewrite interp_trigger. rewrite /= rec_as_interp //.
  - setoid_rewrite interp_trigger. f_equiv; first done. by intros _.
Qed.

Lemma step_in_thread {R} e1 σ1 κs e2 σ2 efs tr tid tid' tp (k : val → itree heaplangE R) :
  base_step e1 σ1 κs e2 σ2 efs →
  is_ctrace tr tid' (<[tid:=(v ← compile_expr e2 ; yield_if_not_val e2 ;; k v)%itree]>tp
                    ++ map (λ e, compile_expr e ;; kill_thread)%itree efs) →
  tp !! tid = Some (v ← compile_expr e1 ; yield_if_not_val e1 ;; k v)%itree →
  ∃ tr', is_postfix tr tr' ∧ is_ctrace tr' tid tp.
Proof.
  intros Hbase Htr Htp.
  inversion Hbase; subst; simpl in Htr; rewrite ?app_nil_r in Htr.
  - admit.
  - admit.
  - admit.
  - admit.
  - pose (e' := subst' x v2 (subst' f (RecV f x e0) e0)).
    exists (CTYield tid' tr). split; first repeat constructor.
    destruct (is_value e') eqn:Hval.
    * eapply is_ctrace_insert; first done.
      { simpl. rewrite base_Beta. simpl.
        rewrite /yield_if_not_val. rewrite /e' in Hval. rewrite Hval. rewrite bind_ret_l.
        reflexivity. }
      rewrite /e' in Hval. apply is_value_val in Hval as [v Heq].
      rewrite Heq in Htr. rewrite Heq.
      rewrite compile_expr_val. rewrite compile_expr_val in Htr.
      simpl in Htr.
      rewrite bind_ret_l. rewrite !bind_ret_l in Htr.
      apply ctrace_yield with (t := k v).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      by rewrite list_insert_insert.
    * eapply is_ctrace_insert; first done.
      { simpl. rewrite base_Beta. simpl. rewrite /yield_if_not_val. rewrite /e' in Hval.
        rewrite Hval. reflexivity. }
      rewrite /e' in Hval. rewrite /yield_if_not_val in Htr. rewrite Hval in Htr.
      rewrite bind_bind.
      apply ctrace_yield with (t := (v ← compile_expr e'; trigger EYield ;; k v)%itree).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      by rewrite list_insert_insert.
  - admit.
  - exists (CTYield tid' tr). split; first repeat constructor.
    rewrite compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (trigger EYield ;; k v')%itree); first done.
    { rewrite base_BinOp // bind_ret_l  //. }
    eapply ctrace_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* AllocN *) admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - exists (CTFork (compile_expr e ;; kill_thread) (CTYield tid' tr)).
    split; first repeat constructor.
    rewrite compile_expr_val !bind_ret_l in Htr.
    eapply trace_base_Fork; first apply Htp.
    eapply ctrace_yield.
    { rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
      rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite insert_app_l; last rewrite insert_length -lookup_lt_is_Some //.
    rewrite list_insert_insert //.
Admitted.

Lemma base_step_in_thread_completed {R} e1 σ1 κs e2 σ2 efs tr tid tid' (tp : list (itree heaplangE R)) :
  base_step e1 σ1 κs e2 σ2 efs →
  is_value e2 →
  is_ctrace tr tid' (delete tid tp ++ map (λ e, compile_expr e ;; kill_thread)%itree efs) →
  tp !! tid = Some (compile_expr e1 ;; kill_thread)%itree →
  ∃ tr', is_postfix tr tr' ∧ is_ctrace tr' tid tp.
Admitted.

Lemma base_step_in_thread_not_completed {R} e1 σ1 κs e2 σ2 efs tr tid tid' (tp : list (itree heaplangE R)) :
  base_step e1 σ1 κs e2 σ2 efs →
  ~is_value e2 →
  is_ctrace tr tid' (<[tid:=(compile_expr e2 ;; kill_thread)%itree]>tp ++ map (λ e, compile_expr e ;; kill_thread)%itree efs) →
  tp !! tid = Some (compile_expr e1 ;; kill_thread)%itree →
  ∃ tr', is_postfix tr tr' ∧ is_ctrace tr' tid tp.
Admitted.

(* TODO: The idea is to add that if [tp'] has nowhere to step then [tr] ends in
*        UB, and if [tp'] returns a value, then so does [tr]. *)
Lemma has_trace n tp σ tp' σ' κ :
  nsteps n (tp, σ) κ (tp', σ') →
  length tp > 0 →
  ∃ tr i, is_ctrace tr i (map compile_expr (filter unevaluated tp)).
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
  setoid_rewrite compile_expr_bind.
Admitted.
