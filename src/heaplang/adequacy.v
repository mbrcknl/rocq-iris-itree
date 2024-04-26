From iris.itree Require Import wpi ub.
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
  is_value e = false →
  (v ← compile_expr (Fork e) ; k v)%itree ≈ vis EFork (λ thread,
    match thread with
    | CurrentThread => k (LitV LitUnit)
    | NewThread =>
        v ← compile_expr e;
        kill_thread
    end
  )%itree.
Proof.
  intros Hval.
  rewrite /compile_expr !rec_as_interp /= Hval interp_bind.
  setoid_rewrite interp_trigger. simpl.
  rewrite -bind_trigger bind_bind. f_equiv. intros [|].
  - rewrite interp_ret bind_ret_l //.
  - rewrite rec_as_interp interp_bind bind_bind. f_equiv. intros v.
    rewrite /kill_thread. rewrite interp_vis /= bind_vis bind_vis.
    apply eqit_VisF. intros [].
Qed.

Lemma trace_base_Fork {R} tid (tp : list (itree heaplangE R)) tr e k :
  is_value e = false →
  tp !! tid = Some (v ← compile_expr (Fork e) ; k v)%itree →
  is_ctrace tr tid (<[tid := k (LitV LitUnit)]>tp ++ [(compile_expr e ;; kill_thread)%itree]) →
  is_ctrace (CTFork (compile_expr e ;; kill_thread) tr) tid tp.
Proof.
  intros Hval Htp Htr. eapply is_ctrace_insert; first done; first apply compile_Fork; eauto.
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

Definition compile_tp (tp : list expr) : list (itree heaplangE ()) :=
  map (λ e, compile_expr e ;; kill_thread)%itree (List.filter (λ e, negb (is_value e)) tp).

Lemma compile_tp_app (tp tp' : list expr) :
  compile_tp (tp ++ tp') = compile_tp tp ++ compile_tp tp'.
Admitted.

Lemma compile_tp_cons (e : expr) (tp : list expr) :
  compile_tp (e :: tp) = if is_value e then compile_tp tp else (compile_expr e ;; kill_thread)%itree :: compile_tp tp.
Admitted.

Lemma compile_tp_empty (tp : list expr) :
  Forall is_value tp →
  compile_tp tp = [].
Admitted.
Lemma compile_tp_empty_inv (tp : list expr) :
  compile_tp tp = [] →
  Forall is_value tp.
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
  - destruct (is_value e) eqn:Hval.
    * rewrite /compile_tp in Htr. simpl in Htr. rewrite Hval /= in Htr.
      exists (CTYield tid' tr).
      split; first repeat constructor.
      eapply is_ctrace_insert; first done; first apply compile_Fork_value; first done.
      simpl.
      eapply is_ctrace_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      rewrite compile_expr_val !bind_ret_l in Htr.
      by rewrite /= app_nil_r in Htr.
    * exists (CTFork (compile_expr e ;; kill_thread) (CTYield tid' tr)).
      split; first repeat constructor.
      rewrite compile_expr_val !bind_ret_l in Htr.
      eapply trace_base_Fork; first done; first apply Htp.
      eapply is_ctrace_yield.
      { rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
        rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite insert_app_l; last rewrite insert_length -lookup_lt_is_Some //.
      rewrite list_insert_insert //. by rewrite /compile_tp /= Hval /= in Htr.
Admitted.

Lemma base_step_in_thread_completed e1 σ1 κs e2 σ2 efs tr tid tid' (tp : list (itree heaplangE ())) :
  base_step e1 σ1 κs e2 σ2 efs →
  is_value e2 →
  is_ctrace tr tid' (delete tid tp ++ compile_tp efs) →
  tp !! tid = Some (compile_expr e1 ;; kill_thread)%itree →
  ∃ tr', is_postfix tr tr' ∧ is_ctrace tr' tid tp.
Admitted.

Lemma base_step_in_thread_not_completed e1 σ1 κs e2 σ2 efs tr tid tid' (tp : list (itree heaplangE ())) :
  base_step e1 σ1 κs e2 σ2 efs →
  ~is_value e2 →
  is_ctrace tr tid' (<[tid:=(compile_expr e2 ;; kill_thread)%itree]>tp ++ compile_tp efs) →
  tp !! tid = Some (compile_expr e1 ;; kill_thread)%itree →
  ∃ tr', is_postfix tr tr' ∧ is_ctrace tr' tid tp.
Admitted.

Lemma base_step_in_thread_last_thread {R} e1 σ1 κs e2 σ2 efs tid :
  base_step e1 σ1 κs e2 σ2 efs →
  is_value e2 →
  Forall is_value efs →
  ∃ tr, is_ctrace (R := R) tr tid [(compile_expr e1 ;; kill_thread)%itree].
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
    remember (length (List.filter (λ e : expr, negb (is_value e)) tp)).
    rewrite /compile_tp map_length -Heqn in Hne. lia. }
  inversion Hstep as [|m [tp1 σ1] [tp2 σ2] [tp3 σ3] ? ? Hstep'' Hstep']. subst.
  inversion Hstep'' as [e1' σ1 e2' σ2' efs tpa tpb Htp' Htp2' Hprim].
  injection Htp'. intros -> ->. clear Htp'.
  injection Htp2'. intros -> ->. clear Htp2'.
  inversion Hprim as [K e1 e2 He1 He2 Hbase]. subst. simpl in K, e1, e2.
  clear Hstep'' Hprim.
  destruct (decide (length K = 0)) as [HK|HK].
  - apply nil_length_inv in HK as ->. simpl. simpl in *.
    destruct (is_value e2) eqn:Hval.
    * destruct (decide (Forall is_value tpa ∧ Forall is_value tpb ∧ Forall is_value efs)) as [[Htp1val [Htp2val Hefsval]]|Hval'].
      + rewrite compile_tp_app compile_tp_cons !compile_tp_empty // app_nil_l.
        assert (Hbase' := Hbase). apply base_step_not_value in Hbase' as ->.
        eapply base_step_in_thread_last_thread with (tid := 0) in Hbase as [tr Htr]; eauto.
      + apply IH in Hstep' as [tr [tid Htr]]; last first.
        { rewrite -lt_gt -Nat.neq_0_lt_0. intros Hemp%nil_length_inv.
          rewrite app_comm_cons !compile_tp_app in Hemp.
          apply app_eq_nil in Hemp as [Htpa [Htpb Hefs]%app_eq_nil].
          rewrite compile_tp_cons Hval in Htpb.
          apply Hval'.
          split; first by apply compile_tp_empty_inv.
          split; first by apply compile_tp_empty_inv.
          by apply compile_tp_empty_inv.
        }
        odestruct (base_step_in_thread_completed _ _ _ _ _ _ _ (length (compile_tp tpa)) _ _ Hbase _ _ _) as [tr' [_ Htr']]; eauto; last first.
        { rewrite compile_tp_app lookup_app_r // Nat.sub_diag compile_tp_cons.
          assert (Hbase' := Hbase). by apply base_step_not_value in Hbase' as ->. }
        rewrite compile_tp_app compile_tp_cons.
        apply base_step_not_value in Hbase as ->.
        rewrite delete_middle -app_assoc.
        by rewrite compile_tp_app compile_tp_cons Hval compile_tp_app in Htr.
      * apply IH in Hstep' as [tr [tid Htr]]; last first.
        { rewrite -lt_gt -Nat.neq_0_lt_0. intros Hemp%nil_length_inv.
          rewrite app_comm_cons !compile_tp_app in Hemp.
          apply app_eq_nil in Hemp as [Htpa [Htpb Hefs]%app_eq_nil].
          rewrite compile_tp_cons Hval in Htpb.
          discriminate.
        }
        odestruct (base_step_in_thread_not_completed _ _ _ _ _ _ _ (length (compile_tp tpa)) _ _ Hbase _ _ _) as [tr' [_ Htr']]; eauto.
        1:{ rewrite Hval. eauto. }
        2:{ rewrite compile_tp_app lookup_app_r // Nat.sub_diag compile_tp_cons.
          assert (Hbase' := Hbase). by apply base_step_not_value in Hbase' as ->. }
        rewrite compile_tp_app compile_tp_cons.
        apply base_step_not_value in Hbase as ->.
        Search insert length.
        replace (length (compile_tp tpa)) with (length (compile_tp tpa) + 0) by lia.
        rewrite insert_app_r /= -app_assoc.
        by rewrite compile_tp_app compile_tp_cons Hval compile_tp_app in Htr.
  - apply IH in Hstep' as [tr [tid Htr]]; last first.
    { rewrite -lt_gt -Nat.neq_0_lt_0. intros Hemp%nil_length_inv.
      rewrite app_comm_cons !compile_tp_app compile_tp_cons in Hemp.
      apply app_eq_nil in Hemp as [Htpa [Htpb Hefs]%app_eq_nil].
      rewrite fill_is_not_value in Htpb; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
      discriminate.
    }
    rewrite compile_tp_app compile_tp_cons fill_is_not_value  in Htr; last first.
    { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
    rewrite compile_expr_bind in Htr; last first.
    { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
    { admit. }
    rewrite compile_tp_app compile_tp_cons fill_is_not_value; last first.
    { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
    apply step_in_thread with (tp := (compile_tp tpa ++ (v ← compile_expr e1; yield_if_not_val e1;; compile_expr (fill K (Val v));; kill_thread)%itree :: compile_tp tpb)) (tid := length (compile_tp tpa)) (tid' := tid) (k := λ v, (compile_expr (fill K (Val v));; kill_thread)%itree) (tr := tr) in Hbase as [tr' [_ Htr']].
    * exists tr'. exists (length (compile_tp tpa)).
      rewrite compile_expr_bind.
      + rewrite bind_bind. by setoid_rewrite bind_bind.
      + admit.
      + rewrite -lt_gt -Nat.neq_0_lt_0 //.
    * replace (length (compile_tp tpa)) with (length (compile_tp tpa) + 0) by lia.
      rewrite compile_tp_app in Htr.
      rewrite insert_app_r /= -app_assoc /=.
      rewrite bind_bind in Htr.
      by setoid_rewrite bind_bind in Htr.
    * rewrite lookup_app_r // Nat.sub_diag //.
Admitted.
