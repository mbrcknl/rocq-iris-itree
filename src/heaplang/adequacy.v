From iris.itree Require Import wpi ub itree choice state.
From iris.itree.threadpool Require Import ctrace.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.program_logic Require Import language.
From iris.itree.threadpool Require Import handler interleaving.
From iris.itree.heaplang Require Import lang.
From Paco Require Import paco.
From Paco Require Import paco2.
Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

Instance state_EqDecision :
  EqDecision state.
Proof.
  intros [σ1 p1] [σ2 p2].
  destruct (decide (σ1 = σ2)) as [Heq|Hneq].
  - destruct (decide (p1 = p2)) as [Heq'|Hneq'].
    * left. by f_equiv.
    * right. intros Heq'. by injection Heq' as -> ->.
  - right. intros Heq. by injection Heq as -> ->.
Qed.

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
Proof. rewrite /compile_tp map_app //. Qed.

Lemma compile_tp_len tp :
  length (compile_tp tp) = length tp.
Proof. rewrite /compile_tp map_length //. Qed.

Definition can_step (e : expr) σ : Prop :=
  ∃ e' κ σ' efs, prim_step e σ κ e' σ' efs.
Definition stuck e σ : Prop :=
  is_value e = false ∧ ~ can_step e σ.

Global Instance can_step_dec e σ : Decision (can_step e σ).
Admitted.
Global Instance stuck_dec e σ : Decision (stuck e σ).
Proof.
  destruct (decide (is_value e = false)).
  - destruct (decide (can_step e σ)).
    * right. by intros [_ Hstep].
    * left. by split.
  - right. by intros [Hval _].
Qed.

Lemma stuck_false e σ κ e' σ' efs :
  stuck e σ →
  prim_step e σ κ e' σ' efs →
  False.
Proof.
  intros [_ Hstuck] Hstep. apply Hstuck. by exists e', κ, σ', efs.
Qed.

(* TODO: [stuck] already exists in Iris [language.v]. Also,
[subredexes_are_values] may be the same as [Basic]. [is_value] is also captured
essentially by [to_val]. *)

Inductive Basic : expr → Prop :=
  | BasicVar x :
    Basic (Var x)
  | BasicRec f x e :
    Basic (Rec f x e)
  | BasicApp v1 v2 :
    Basic (App (Val v1) (Val v2))
  | BasicUnOp op v :
    Basic (UnOp op (Val v))
  | BasicBinOp op v1 v2 :
    Basic (BinOp op (Val v1) (Val v2))
  | BasicIf v0 e1 e2 :
    Basic (If (Val v0) e1 e2)
  | BasicPair v1 v2 :
    Basic (Pair (Val v1) (Val v2))
  | BasicFst v :
    Basic (Fst (Val v))
  | BasicSnd v :
    Basic (Snd (Val v))
  | BasicInjL v :
    Basic (InjL (Val v))
  | BasicInjR v :
    Basic (InjR (Val v))
  | BasicCase v0 e1 e2 :
    Basic (Case (Val v0) e1 e2)
  | BasicFork e :
    Basic (Fork e)
  | BasicAllocN nv v :
    Basic (AllocN (Val nv) (Val v))
  | BasicFree v :
    Basic (Free (Val v))
  | BasicLoad v :
    Basic (Load (Val v))
  | BasicStore v1 v2 :
    Basic (Store (Val v1) (Val v2))
  | BasicXchg v1 v2 :
    Basic (Xchg (Val v1) (Val v2))
  | BasicCmpXchg v1 v2 v3 :
    Basic (CmpXchg (Val v1) (Val v2) (Val v3))
  | BasicFAA v1 v2 :
    Basic (FAA (Val v1) (Val v2)).

Lemma can_step_fill K e σ :
  can_step e σ →
  can_step (fill K e) σ.
Proof.
  intros (?&?&?&?&?). do 4 eexists. by apply fill_prim_step.
Qed.

Lemma stuck_fill K e σ :
  stuck (fill K e) σ →
  is_value e = false →
  stuck e σ.
Proof.
  intros [_ Hstep] Hval.
  split; first done. intros Hstep'.
  apply Hstep. by apply can_step_fill.
Qed.

Lemma stuck_basic e σ :
  stuck e σ →
  ∃ K e', e = fill K e' ∧ Basic e' ∧ stuck e' σ.
Proof.
  intros Hstuck.
  induction e.
  - destruct Hstuck as [Hval _]. discriminate.
  - exists [], (Var x). split; first done. by split; first constructor.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - destruct (is_value e2) eqn:Hval2; first destruct (is_value e1) eqn:Hval1.
    * apply is_value_val in Hval2 as [v2 ->].
      apply is_value_val in Hval1 as [v1 ->].
      exists [], (App (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply is_value_val in Hval2 as [v2 ->].
      apply stuck_fill with (K := [AppLCtx v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [AppLCtx v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill with (K := [AppRCtx e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [AppRCtx e1]), e'.
      rewrite fill_app. subst. eauto.
Admitted.

Lemma is_ctrace_ub tp tid (k : void → itree heaplangE ()) :
  tp !! tid = Some (x ← trigger EUb ; k x)%itree →
  is_ctrace (CTVisEmpty void (subevent _ EUb)) tid tp.
Proof.
  intros Htp.
  eapply is_ctrace_insert; first done.
  { rewrite bind_vis //. }
  eexists. split.
  - rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1.
  - by constructor.
Qed.

Definition thread_stuck (tp : list expr) σ :=
  ∃ tid e, tp !! tid = Some e ∧ stuck e σ.
Global Instance thread_stuck_dec tp σ : Decision (thread_stuck tp σ).
Admitted.

Definition trace_invariant σ tp' σ' (tr : ctrace (demonicE +' stateE state +' ubE) ()) :=
  (thread_stuck tp' σ' → is_postfix_ctrace (CTVisEmpty void (subevent _ EUb)) tr) ∧
  is_Some (interp_tr_state σ (interp_tr (sequencify tr))).

Lemma stuck_ub tp tid e σ :
  tp !! tid = Some e →
  stuck e σ →
  ∃ tr, trace_invariant σ tp σ tr ∧ is_ctrace tr tid (compile_tp tp).
Proof.
  intros Htp (K&e'&->&Hbasic&Hstuck)%stuck_basic.
  destruct Hbasic as [x|f x e0|v1 v2 | | | | | | | | | | | | | | | | | ].
  - exists (CTVisEmpty void (subevent _ EUb)).
    split; first split; eauto. { intros _. constructor. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap Htp //. }
    { rewrite compile_expr_bind'; first done. admit. }
    rewrite /compile_expr. simpl_itree.
    eapply is_ctrace_ub.
    rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - exists (CTVisEmpty void (subevent _ EUb)).
    split; first split; eauto. { intros _. constructor. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap Htp //. }
    { rewrite compile_expr_bind'; first done. admit. }
    destruct (val_to_RecV v1) as [[[f x] e]|] eqn:Heq.
    destruct v1; try discriminate.
    * eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * rewrite /compile_expr. simpl_itree. rewrite Heq /=. simpl_itree.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  -
Admitted.

Lemma step_in_thread e1 σ1 κs e2 σ2 efs tr tid tid' tp (k : val → itree heaplangE ()) tp' σ' :
  base_step e1 σ1 κs e2 σ2 efs →
  is_ctrace tr tid' (<[tid:=(v ← compile_expr e2 ; yield_if_not_val e2 ;; k v)%itree]>tp
                    ++ compile_tp efs) →
  trace_invariant σ2 tp' σ' tr →
  tp !! tid = Some (v ← compile_expr e1 ; yield_if_not_val e1 ;; k v)%itree →
  ∃ tr', trace_invariant σ1 tp' σ' tr' ∧ is_ctrace tr' tid tp.
Proof.
  intros Hbase Htr [Hub Hstinv] Htp.
  inversion Hbase; subst; simpl in Htr; rewrite ?app_nil_r in Htr.
  - admit.
  - admit.
  - admit.
  - admit.
  - pose (e' := subst' x v2 (subst' f (RecV f x e0) e0)).
    exists (CTYield tid' tr). split; first split; eauto.
    { intros Hstuck. constructor. by apply Hub. }
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
  - exists (CTYield tid' tr). split; first split; eauto.
    { intros Hstuck. constructor. by apply Hub. }
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
    split; first split; eauto.
    { intros Hstuck. repeat constructor. by apply Hub. }
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
Proof. intros Hbase. by destruct Hbase. Qed.

Lemma lt_gt n m :
  n < m ↔ m > n.
Proof. lia. Qed.

Lemma fill_is_not_value K e :
  length K > 0 →
  is_value (ectx_language.fill K e) = false.
Proof.
  induction (length K) as [|n IH] eqn:Heq. { lia. }
  intros _.
  unshelve epose (split_last K _) as Hsplit; first lia. destruct Hsplit as (Ki&K'&->).
  rewrite /= fill_app /=.
  by destruct Ki.
Qed.

(* TODO: Idea: make κ = [] *)
Lemma has_trace n tp σ tp' σ' κ :
  language.nsteps n (tp, σ) κ (tp', σ') →
  length (compile_tp tp) > 0 →
  ∃ tr tid,
    trace_invariant σ tp' σ' tr ∧
    is_ctrace (R := ()) tr tid (compile_tp tp).
Proof.
  revert tp σ tp' σ' κ. induction n as [|n IH]; intros tp σ tp' σ' κ Hstep Hne.
  { destruct (decide (thread_stuck tp σ)) as [(tid&e&Htp&Hstuck)|].
    * apply stuck_ub with (tp := tp) (tid := tid) in Hstuck as (tr&Hinv&Htr); last done.
      exists tr, tid. split; last done. inversion Hstep; subst. done.
    * inversion Hstep; subst.
      exists CTCut, 0. split; first split.
      + by intros Hstuck.
      + done.
      + apply is_ctrace_CTCut. rewrite map_length. rewrite compile_tp_len in Hne. lia.
  }
  inversion Hstep as [|m [tp1 σ1] [tp2 σ2] [tp3 σ3] ? ? Hstep'' Hstep']. subst.
  inversion Hstep'' as [e1' σ1 e2' σ2' efs tpa tpb Htp' Htp2' Hprim].
  injection Htp'. intros -> ->. clear Htp'.
  injection Htp2'. intros -> ->. clear Htp2'.
  inversion Hprim as [K e1 e2 He1 He2 Hbase]. subst. simpl in K, e1, e2.
  clear Hstep'' Hprim.
  destruct (decide (length K = 0)) as [HK|HK].
  - apply nil_length_inv in HK as ->. simpl. simpl in *.
    apply IH in Hstep' as [tr [tid [Hinv Htr]]]; last first.
    { rewrite compile_tp_len app_length /= app_length.
      rewrite compile_tp_len app_length /= in Hne.
      lia.
    }
    apply step_in_thread with (tp := (compile_tp tpa ++ (v ← compile_expr e1; yield_if_not_val e1;; kill_thread)%itree :: compile_tp tpb)) (tid := length (compile_tp tpa)) (tid' := tid) (k := λ v, kill_thread) (tr := tr) (tp' := tp') (σ' := σ') in Hbase as [tr' [Hinv' Htr']].
    * exists tr'. exists (length (compile_tp tpa)). rewrite compile_tp_app. eauto.
    * replace (length (compile_tp tpa)) with (length (compile_tp tpa) + 0) by lia.
      rewrite compile_tp_app in Htr.
      rewrite insert_app_r /= -app_assoc /=.
      by rewrite /= compile_tp_app in Htr.
    * done.
    * by apply list_lookup_middle.
  - apply IH in Hstep' as [tr [tid [Hinv Htr]]]; last first.
    { rewrite -lt_gt -Nat.neq_0_lt_0. intros Hemp%nil_length_inv.
      rewrite !compile_tp_app /= in Hemp.
      apply app_eq_nil in Hemp as [_ [=]].
    }
    rewrite compile_tp_app /= compile_tp_app in Htr.
    rewrite compile_tp_app /=.
    apply step_in_thread with (tp := (compile_tp tpa ++ (v ← compile_expr e1; yield_if_not_val e1;; compile_expr (fill K (Val v));; trigger EYield;; kill_thread)%itree :: compile_tp tpb)) (tid := length (compile_tp tpa)) (tid' := tid) (k := λ v, (compile_expr (fill K (Val v));; trigger EYield;; kill_thread)%itree) (tr := tr) (tp' := tp') (σ' := σ') in Hbase as [tr' [Hinv' Htr']].
    * exists tr'. exists (length (compile_tp tpa)).
      split; first done.
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
    * done.
Admitted.

Definition trace_ends_in_ub {E R} `{ubE -< E} (tr : trace E R) :=
  is_postfix (TVisEmpty void (subevent _ EUb)) tr.

Lemma interp_tr_state_ub {E R S} `{EqDecision S} `{ubE -< E} σ (tr : trace (stateE S +' E) R) tr' :
  trace_ends_in_ub tr →
  interp_tr_state σ tr = Some tr' →
  trace_ends_in_ub tr'.
Proof.
  revert σ tr'. induction tr; intros σ tr' Hub Hst.
  - inversion Hub.
  - destruct e as [e|e]; first destruct e as [|σ'].
    * simpl in Hst. destruct (decide (a = σ)) as [->|]; last discriminate.
      apply IHtr with (σ := σ); last done. by inversion Hub.
    * inversion Hub; simplify_K; simplify_K; subst. by eapply IHtr.
    * simpl in Hst. destruct (interp_tr_state σ tr) as [tr''|] eqn:Heq.
      + simpl in Heq. injection Hst as <-. constructor.
        by apply IHtr with (σ := σ); first by inversion Hub.
      + discriminate.
  - inversion Hub; simplify_K; simplify_K; subst.
    injection Hst as <-. simplify_K. constructor.
  - inversion Hub.
Qed.

Lemma interp_tr_ub {E E' R} `{ubE -< E'} (tr : trace (E +' E') R) :
  trace_ends_in_ub tr →
  trace_ends_in_ub (interp_tr tr).
Proof.
  intros Hub.
  rewrite /trace_ends_in_ub.
  replace (TVisEmpty void (subevent void EUb))
    with (interp_tr (R := R) (TVisEmpty void (subevent void EUb : (E +' E') void)))
    by done.
  by apply interp_tr_is_postfix.
Qed.

Lemma sequencify_ub {E E' R} `{ubE -< E'} (tr : ctrace (E +' E') R) :
  is_postfix_ctrace (CTVisEmpty void (subevent _ EUb)) tr →
  trace_ends_in_ub (sequencify tr).
Proof.
  intros Hub.
  rewrite /trace_ends_in_ub.
  replace (TVisEmpty void (subevent void EUb))
    with (sequencify (R := R) (CTVisEmpty void (subevent void EUb : (E +' E') void)))
    by done.
  by apply sequencify_is_postfix.
Qed.

Lemma is_trace_ub {R} (t : itree ubE R) tr :
  trace_ends_in_ub tr →
  is_trace tr t →
  t ≈ ub.
Proof.
  intros Hub Htr. pfold. rewrite /eqit_. induction Htr.
  - inversion Hub.
  - by destruct e.
  - inversion Hub. destruct e. constructor. by intros.
  - inversion Hub.
  - constructor; first done. by apply IHHtr.
Qed.

Lemma ub_execution n e σ tp' σ' κ :
  language.nsteps n ([e], σ) κ (tp', σ') →
  thread_stuck tp' σ' →
  ∃ t1 t2 t3,
    (* TODO: consisting naming for interpreation relations *)
    (* TODO: abstraction for this composite relation *)
    interleaves (R := ()) 0 [compile_expr e ;; yield_if_not_val e ;; kill_thread]%itree t1 ∧
    demonic_instantiates t1 t2 ∧
    eval σ t2 t3 ∧
    (* TODO: use UB adequacy *)
    t3 ≈ ub.
Proof.
  intros Hsteps Hstuck.
  apply has_trace in Hsteps as (tr&tid&[Hub [tr' Hst]]&Htr); last eauto.
  apply Hub in Hstuck as Hub'.
  apply interleaving_extending_trace in Htr as (t1&Hint&Htr).
  exists t1.
  eapply instantiation_extending_trace in Htr as (t2&Hinst&Htr).
  exists t2.
  eapply eval_trace with (s := σ) in Htr as (t3&Heval&Htr); last done.
  exists t3.
  split.
  { destruct (interleaves_lookup _ _ _ Hint) as [t Hidx].
    by destruct tid.
  }
  split; first done.
  split; first done.
  eapply is_trace_ub; last done.
  eapply interp_tr_state_ub; last done. apply interp_tr_ub. by apply sequencify_ub.
Qed.

Lemma ub_execution_wpi `{!invGS_gen hlc Σ} n e σ tp' σ' κ :
  language.nsteps n ([e], σ) κ (tp', σ') →
  thread_stuck tp' σ' →
  state_interp σ -∗
  (* TODO: Clean up *)
  WPi (compile_expr e;; yield_if_not_val e;; kill_thread : itree heaplangE ()) @ heaplangH ; ⊤ {{ _, True }} -∗
  |={⊤}=> False.
Proof.
  iIntros (Hstep Hstuck) "Hstate Hwp".
  apply ub_execution in Hstep as (t1&t2&t3&Hint&Hinst&Heval&Hub); last done.
  (* TODO: Name these adequacy theorems consistently. *)
  iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; first apply Hint.
  iDestruct (demonicH_adequate with "Hwp") as "Hwp"; first apply Hinst.
  iDestruct (wpi_state with "Hstate Hwp") as "Hwp"; first apply Heval.
  rewrite Hub /ub -wpi_vis' /=. by iMod "Hwp".
Qed.
