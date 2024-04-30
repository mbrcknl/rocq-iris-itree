From iris.itree Require Import wpi ub itree.
From iris.itree.threadpool Require Import trace.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.program_logic Require Import language.
From iris.itree.threadpool Require Import handler.
From iris.itree.heaplang Require Import lang.
Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

Lemma compile_Fork_value {R} e (k : val → itree heaplangE R) :
  is_value e = true →
  (v ← compile_expr (Fork e) ; k v)%itree ≈ k (LitV LitUnit).
Admitted.

Lemma compile_Fork {R} e (k : val → itree heaplangE R) :
  (v ← compile_expr (Fork e) ; k v)%itree ≈ vis EFork (λ thread,
    match thread with
    | CurrentThread => k (LitV LitUnit)
    | NewThread =>
        v ← compile_expr e;
        yield_if_not_val e;;
        kill_thread
    end
  )%itree.
Proof.
  rewrite /compile_expr. simpl_itree. simpl_itree.
  rewrite -bind_trigger. f_equiv. intros [|].
  - by simpl_itree.
  - simpl_itree. f_equiv. intros v. rewrite /kill_thread.
      rewrite /yield_if_not_val. destruct (is_value _) eqn:Hval.
      * rewrite /kill_thread. simpl_itree. rewrite -bind_trigger. f_equiv; first done.
        intros [].
      * rewrite /kill_thread. simpl_itree. f_equiv; first done.
        intros []. rewrite -bind_trigger. f_equiv; first done. intros [].
Qed.

Lemma trace_base_Fork {R} tid (tp : list (itree heaplangE R)) tr e k :
  tp !! tid = Some (v ← compile_expr (Fork e) ; k v)%itree →
  is_ctrace tr tid (<[tid := k (LitV LitUnit)]>tp ++ [(compile_expr e ;; yield_if_not_val e ;; kill_thread)%itree]) →
  is_ctrace (CTFork (compile_expr e ;; yield_if_not_val e ;; kill_thread) tr) tid tp.
Proof.
  intros Htp Htr. eapply is_ctrace_insert; first done; first apply compile_Fork; eauto.
  eexists. split. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1. }
  constructor.
  rewrite /compile_expr //. rewrite list_insert_insert.
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
  rewrite /compile_expr. simpl_itree. rewrite Hop. by simpl_itree.
Qed.

Lemma base_Beta f_ x_ e v :
  compile_expr (App (Val (RecV f_ x_ e)) (Val v))
  ≈ let e' := (subst' x_ v (subst' f_ (RecV f_ x_ e) e))
     in yield_if_not_val e' ;; compile_expr e'.
Proof.
  rewrite /compile_expr. simpl_itree. rewrite /yield_if_not_val.
  destruct (is_value _) eqn:Heq; by simpl_itree.
Qed.

Definition compile_tp (tp : list expr) : list (itree heaplangE ()) :=
  map (λ e, compile_expr e ;; yield_if_not_val e ;; kill_thread)%itree tp.

Lemma compile_tp_app (tp tp' : list expr) :
  compile_tp (tp ++ tp') = compile_tp tp ++ compile_tp tp'.
Admitted.

Lemma step_in_thread e1 σ1 κs e2 σ2 efs tr tid tid' tp (k : val → itree heaplangE ()) :
  base_step e1 σ1 κs e2 σ2 efs →
  is_ctrace tr tid' (<[tid:=(v ← compile_expr e2 ; yield_if_not_val e2 ;; k v)%itree]>tp
                    ++ compile_tp efs) →
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
      apply is_ctrace_yield with (t := k v).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      by rewrite list_insert_insert.
    * eapply is_ctrace_insert; first done.
      { simpl. rewrite base_Beta. simpl. rewrite /yield_if_not_val. rewrite /e' in Hval.
        rewrite Hval. reflexivity. }
      rewrite /e' in Hval. rewrite /yield_if_not_val in Htr. rewrite Hval in Htr.
      rewrite bind_bind.
      apply is_ctrace_yield with (t := (v ← compile_expr e'; trigger EYield ;; k v)%itree).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      by rewrite list_insert_insert.
  - admit.
  - exists (CTYield tid' tr). split; first repeat constructor.
    rewrite compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (trigger EYield ;; k v')%itree); first done.
    { rewrite base_BinOp // bind_ret_l  //. }
    eapply is_ctrace_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
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
  - exists (CTFork (compile_expr e ;; yield_if_not_val e ;; kill_thread) (CTYield tid' tr)).
    split; first repeat constructor.
    rewrite compile_expr_val !bind_ret_l in Htr.
    eapply trace_base_Fork; first apply Htp.
    eapply is_ctrace_yield.
    { rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
      rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite insert_app_l; last rewrite insert_length -lookup_lt_is_Some //.
    rewrite list_insert_insert //.
Admitted.

Lemma base_step_not_value e1 σ1 κs e2 σ2 tfs :
  base_step e1 σ1 κs e2 σ2 tfs →
  is_value e1 = false.
Admitted.

Lemma lt_gt n m :
  n < m ↔ m > n.
Admitted.

Lemma fill_is_not_value K e :
  length K > 0 →
  is_value (ectx_language.fill K e) = false.
Admitted.

(* TODO: The idea is to add that if [tp'] has nowhere to step then [tr] ends in
*        UB, and if [tp'] returns a value, then so does [tr]. *)
  Search nsteps.
Lemma has_trace n tp σ tp' σ' κ :
  language.nsteps n (tp, σ) κ (tp', σ') →
  length (compile_tp tp) > 0 →
  ∃ tr tid, is_ctrace (R := ()) tr tid (compile_tp tp).
Proof.
  revert tp σ tp' σ' κ. induction n as [|n IH]; intros tp σ tp' σ' κ Hstep Hne.
  { exists CTCut, 0. apply is_ctrace_CTCut. rewrite map_length.
    rewrite /compile_tp map_length in Hne. lia. }
  inversion Hstep as [|m [tp1 σ1] [tp2 σ2] [tp3 σ3] ? ? Hstep'' Hstep']. subst.
  inversion Hstep'' as [e1' σ1 e2' σ2' efs tpa tpb Htp' Htp2' Hprim].
  injection Htp'. intros -> ->. clear Htp'.
  injection Htp2'. intros -> ->. clear Htp2'.
  inversion Hprim as [K e1 e2 He1 He2 Hbase]. subst. simpl in K, e1, e2.
  clear Hstep'' Hprim.
  destruct (decide (length K = 0)) as [HK|HK].
  - apply nil_length_inv in HK as ->. simpl. simpl in *.
    apply IH in Hstep' as [tr [tid Htr]]; last first.
    { rewrite /compile_tp map_length app_length /= app_length.
      rewrite /compile_tp map_length app_length /= in Hne.
      lia.
    }
    apply step_in_thread with (tp := (compile_tp tpa ++ (v ← compile_expr e1; yield_if_not_val e1;; kill_thread)%itree :: compile_tp tpb)) (tid := length (compile_tp tpa)) (tid' := tid) (k := λ v, kill_thread) (tr := tr) in Hbase as [tr' [_ Htr']].
    * exists tr'. exists (length (compile_tp tpa)). rewrite compile_tp_app //.
    * replace (length (compile_tp tpa)) with (length (compile_tp tpa) + 0) by lia.
      rewrite compile_tp_app in Htr.
      rewrite insert_app_r /= -app_assoc /=.
      by rewrite /= compile_tp_app in Htr.
    * rewrite lookup_app_r // Nat.sub_diag //.
  - apply IH in Hstep' as [tr [tid Htr]]; last first.
    { rewrite -lt_gt -Nat.neq_0_lt_0. intros Hemp%nil_length_inv.
      rewrite !compile_tp_app /= in Hemp.
      apply app_eq_nil in Hemp as [_ [=]].
    }
    rewrite compile_tp_app /= compile_tp_app in Htr.
    rewrite compile_tp_app /=.
    apply step_in_thread with (tp := (compile_tp tpa ++ (v ← compile_expr e1; yield_if_not_val e1;; compile_expr (fill K (Val v));; trigger EYield;; kill_thread)%itree :: compile_tp tpb)) (tid := length (compile_tp tpa)) (tid' := tid) (k := λ v, (compile_expr (fill K (Val v));; trigger EYield;; kill_thread)%itree) (tr := tr) in Hbase as [tr' [_ Htr']].
    * exists tr'. exists (length (compile_tp tpa)).
      rewrite /= compile_expr_bind.
      + setoid_rewrite fill_not_val; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
        rewrite bind_bind. by setoid_rewrite bind_bind.
      + admit.
      + rewrite -lt_gt -Nat.neq_0_lt_0 //.
    * replace (length (compile_tp tpa)) with (length (compile_tp tpa) + 0) by lia.
      rewrite insert_app_r /= -app_assoc /=.
      rewrite compile_expr_bind in Htr.
      + setoid_rewrite fill_not_val in Htr; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
        by repeat setoid_rewrite bind_bind in Htr.
      + admit.
      + rewrite -lt_gt -Nat.neq_0_lt_0 //.
    * rewrite lookup_app_r // Nat.sub_diag //.
Admitted.
