From iris.itree Require Import wpi ub itree choice state.
From iris.itree.threadpool Require Import ctrace.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.program_logic Require Import language.
(* TODO: make the import order less brittle *)
From iris.itree.heaplang Require Import decide.
From iris.itree Require Import later handler.
From iris.itree.threadpool Require Import handler interleaving.
From iris.itree.heaplang Require Import lang.
From Paco Require Import paco.
From Paco Require Import paco2.

Set Default Proof Using "Type*".

Section adequacy.
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
    | CurrentThread => step ;; k (LitV LitUnit)
    | NewThread => compile_expr_kill e
    end
  )%itree.
Proof.
  rewrite /compile_expr_kill/compile_expr_yield/compile_expr. eutt_norm/=. simpl. eutt_norm.
  rewrite -bind_trigger. f_equiv. intros [|].
  - eutt_norm. rewrite /step_ret. by eutt_norm.
  - eutt_norm. f_equiv. intros v. rewrite /kill_thread.
    f_equiv. intros _. rewrite -!bind_trigger. eutt_norm. by f_equiv.
Qed.

Lemma trace_base_Fork {R} tid (tp : list (itree heaplangE R)) tr e k :
  tp !! tid = Some (v ← compile_expr (Fork e) ; k v)%itree →
  is_ctrace tr tid (<[tid := (step ;; k (LitV LitUnit))%itree]>tp ++ [compile_expr_kill e]) →
  is_ctrace (CTFork (compile_expr_kill e) tr) tid tp.
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

Lemma base_UnOp op v v' :
  un_op_eval op v = Some v' →
  compile_expr (UnOp op (Val v)) ≈ step_ret v'.
Proof.
  intros Hop.
  rewrite /compile_expr. eutt_norm/=. rewrite Hop. by eutt_norm/=.
Qed.

Lemma base_BinOp op v1 v2 v3 :
  bin_op_eval op v1 v2 = Some v3 →
  compile_expr (BinOp op (Val v1) (Val v2)) ≈ step_ret v3.
Proof.
  intros Hop.
  rewrite /compile_expr. eutt_norm/=. rewrite Hop. by eutt_norm/=.
Qed.

Lemma base_Beta f_ x_ e v :
  compile_expr (App (Val (RecV f_ x_ e)) (Val v))
  ≈ let e' := (subst' x_ v (subst' f_ (RecV f_ x_ e) e))
     in step_if_not_val e' ;; yield_if_not_val e' ;; compile_expr e'.
Proof.
  rewrite /compile_expr. eutt_norm/=. setoid_rewrite interp_recursive_call. by eutt_norm/=.
Qed.

Definition compile_tp' (tp : list expr) : list (itree heaplangE val) :=
  map compile_expr_kill tp.
Definition compile_tp (tp : list expr) : list (itree heaplangE val) :=
  map (λ '(tid, e),
    v ← compile_expr_yield e ;
    match tid with
    | 0 => Ret v
    | _ => kill_thread
    end
  )%itree (enumerate tp).

Lemma compile_tp_len tp :
  length (compile_tp tp) = length tp.
Proof. rewrite /compile_tp map_length enumerate_length //. Qed.
Lemma compile_tp'_app tp tp' :
  compile_tp' (tp ++ tp') = compile_tp' tp ++ compile_tp' tp'.
Proof. rewrite /compile_tp' map_app //. Qed.
Lemma compile_tp'_cons e tp :
  compile_tp' (e :: tp) = compile_tp' [e] ++ compile_tp' tp.
Proof. done. Qed.
Lemma compile_tp_cons e tp :
  compile_tp (e :: tp) = compile_tp [e] ++ compile_tp' tp.
Proof.
  rewrite /compile_tp /=. f_equiv.
  replace 1 with (S 0) by done.
  generalize 0. induction tp as [|e' tp IH]; first done. intros n.
  simpl. f_equiv; first done. apply IH.
Qed.
Lemma compile_tp_app tp tp' :
  length tp ≠ 0 →
  compile_tp (tp ++ tp') = compile_tp tp ++ compile_tp' tp'.
Proof.
  destruct tp as [|e tp]; first done. intros _.
  rewrite compile_tp_cons /= compile_tp_cons /= compile_tp'_app //.
Qed.


Lemma stuck_false (e : expr) σ κ e' σ' efs :
  stuck e σ →
  prim_step e σ κ e' σ' efs →
  False.
Proof.
  intros [_ Hstuck] Hstep. by apply Hstuck in Hstep.
Qed.

Lemma stuck_fill' K e σ :
  stuck (fill K e) σ →
  to_val e = None →
  stuck e σ.
Proof.
  intros [_ Hirr] Hval.
  split; first by inversion e. apply not_reducible.
  intros Hred. apply (reducible_fill (K := fill K)) in Hred.
  by apply not_reducible in Hirr.
Qed.

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
    Basic (FAA (Val v1) (Val v2))
  | BasicResolve e1 e2 e3 :
    Basic (Resolve e1 e2 e3).

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
  - destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (App (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply stuck_fill' with (K := [AppLCtx v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [AppLCtx v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [AppRCtx e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [AppRCtx e1]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (UnOp op (Val v)).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [UnOpCtx op]) (e := e) in Hstuck; last done.
      apply IHe in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [UnOpCtx op]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (BinOp op (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply stuck_fill' with (K := [BinOpLCtx op v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [BinOpLCtx op v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [BinOpRCtx op e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [BinOpRCtx op e1]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e1) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (If (Val v) e2 e3).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [IfCtx e2 e3]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [IfCtx e2 e3]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (Pair (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply stuck_fill' with (K := [PairLCtx v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [PairLCtx v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [PairRCtx e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [PairRCtx e1]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (Fst (Val v)).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [FstCtx]) (e := e) in Hstuck; last done.
      apply IHe in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [FstCtx]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (Snd (Val v)).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [SndCtx]) (e := e) in Hstuck; last done.
      apply IHe in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [SndCtx]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (InjL (Val v)).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [InjLCtx]) (e := e) in Hstuck; last done.
      apply IHe in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [InjLCtx]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (InjR (Val v)).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [InjRCtx]) (e := e) in Hstuck; last done.
      apply IHe in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [InjRCtx]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e1) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (Case (Val v) e2 e3).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [CaseCtx e2 e3]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [CaseCtx e2 e3]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (AllocN (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply stuck_fill' with (K := [AllocNLCtx v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [AllocNLCtx v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [AllocNRCtx e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [AllocNRCtx e1]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (Free (Val v)).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [FreeCtx]) (e := e) in Hstuck; last done.
      apply IHe in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [FreeCtx]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e) as [v|] eqn:Hval.
    * apply of_to_val in Hval as <-.
      exists [], (Load (Val v)).
      split; first done. split; first constructor. done.
    * apply stuck_fill' with (K := [LoadCtx]) (e := e) in Hstuck; last done.
      apply IHe in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [LoadCtx]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (Store (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply stuck_fill' with (K := [StoreLCtx v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [StoreLCtx v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [StoreRCtx e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [StoreRCtx e1]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e3) as [v3|] eqn:Hval3; first destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval3 as <-.
      apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (CmpXchg (Val v1) (Val v2) (Val v3)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval3 as <-.
      apply stuck_fill' with (K := [CmpXchgLCtx v2 v3]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [CmpXchgLCtx v2 v3]), e'.
      rewrite fill_app. subst. eauto.
    * apply of_to_val in Hval3 as <-.
      apply stuck_fill' with (K := [CmpXchgMCtx e1 v3]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [CmpXchgMCtx e1 v3]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [CmpXchgRCtx e1 e2]) (e := e3) in Hstuck; last done.
      apply IHe3 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [CmpXchgRCtx e1 e2]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (Xchg (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply stuck_fill' with (K := [XchgLCtx v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [XchgLCtx v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [XchgRCtx e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [XchgRCtx e1]), e'.
      rewrite fill_app. subst. eauto.
  - destruct (to_val e2) as [v2|] eqn:Hval2; first destruct (to_val e1) as [v1|] eqn:Hval1.
    * apply of_to_val in Hval2 as <-.
      apply of_to_val in Hval1 as <-.
      exists [], (FAA (Val v1) (Val v2)).
      split; first done. split; first constructor. done.
    * apply of_to_val in Hval2 as <-.
      apply stuck_fill' with (K := [FaaLCtx v2]) (e := e1) in Hstuck; last done.
      apply IHe1 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [FaaLCtx v2]), e'.
      rewrite fill_app. subst. eauto.
    * apply stuck_fill' with (K := [FaaRCtx e1]) (e := e2) in Hstuck; last done.
      apply IHe2 in Hstuck as (K&e'&Hfill&Hbasic&Hstuck').
      exists (K ++ [FaaRCtx e1]), e'.
      rewrite fill_app. subst. eauto.
  - exists [], (Fork e). split; first done. by split; first constructor.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    apply NewProphS with (p := fresh (σ.(used_proph_id))). apply is_fresh.
  - exists [], (Resolve e1 e2 e3). split; first done. by split; first constructor.
Qed.

Definition ctrace_ub {R} : ctrace (demonicE +' stateE state +' laterE +' ubE) R :=
  CTVisEmpty void (subevent _ EUb).

Lemma is_ctrace_ub {A R} tp tid (k : A → itree heaplangE R) :
  tp !! tid = Some (ITree.bind ub k)%itree →
  is_ctrace ctrace_ub tid tp.
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
Proof.
  induction tp as [|e tp].
  - right. intros (?&?&[=]&?).
  - destruct IHtp as [Hstuck|Hstuck].
    * left. destruct Hstuck as (tid&e'&Htp&Hstuck). exists (S tid), e'. eauto.
    * destruct (decide (stuck e σ)).
      + left. exists 0, e. eauto.
      + right. intros (tid&e'&Htp&Hstuck').
        destruct tid. { by injection Htp as ->. }
        apply Hstuck. exists tid, e'. eauto.
Qed.

Variant Terminal (R : Type) :=
  | TermRet (r : R)
  | TermUb.
Global Arguments TermRet {_}.
Global Arguments TermUb {_}.
Definition terminal_trace {E R} `{ubE -< E} (tx : Terminal R) : trace E R :=
  match tx with
  | TermRet r => TRet r
  | TermUb => TVisEmpty void (subevent _ EUb)
  end.
Definition terminal_ctrace {E R} `{ubE -< E} (tx : Terminal R) : ctrace E R :=
  match tx with
  | TermRet r => CTRet r
  | TermUb => CTVisEmpty void (subevent _ EUb)
  end.

Instance Terminal_FMap : FMap Terminal :=
  λ _ _ f tx,
    match tx with
    | TermRet r => TermRet (f r)
    | TermUb => TermUb
    end.

Definition trace_terminates_in {E R} `{ubE -< E} (tr : trace E R) (tx : Terminal R) :=
  is_postfix (terminal_trace tx) tr.
Definition ctrace_terminates_in {E R} `{ubE -< E} (tr : ctrace E R) (tx : Terminal R) :=
  is_postfix_ctrace (terminal_ctrace tx) tr.

Variant tp_termination : list expr → state → Terminal val → Prop :=
  | tp_termination_TermUb tp σ :
    thread_stuck tp σ →
    tp_termination tp σ TermUb
  | tp_termination_TermRet v tp σ :
    tp_termination (Val v :: tp) σ (TermRet v).

(* TODO: Factor this event type into its own definition. *)
Definition trace_invariant_postfix (tx : Terminal val) (tr : ctrace (demonicE +' stateE state +' laterE +' ubE) val) :=
  ctrace_terminates_in tr tx.
Definition trace_invariant_state σ (tr : ctrace (demonicE +' stateE state +' laterE +' ubE) val) :=
  match (interp_tr_state σ (interp_tr (sequencify tr))) with
  | Some _ => true
  | None => false
  end.
(* TODO: Add invariant about the final state reached in trace. Should be σ'. *)
Definition trace_invariant σ (tx : Terminal val) (tr : ctrace (demonicE +' stateE state +' laterE +' ubE) val) :=
  trace_invariant_postfix tx tr ∧
  trace_invariant_state σ tr.

Lemma trace_invariant_postfix_postfix tx tr tr' :
  is_postfix_ctrace tr tr' →
  trace_invariant_postfix tx tr →
  trace_invariant_postfix tx tr'.
Proof.
  intros Hpost Htinv. rewrite /trace_invariant_postfix/ctrace_terminates_in.
  rewrite /trace_invariant_postfix/ctrace_terminates_in in Htinv.
  by etransitivity.
Qed.

Lemma tp_termination_ub (tp : list expr) (σ : state) :
  tp_termination tp σ TermUb →
  thread_stuck tp σ.
Proof. by inversion 1. Qed.

Lemma is_ctrace_ret tp σ v :
  tp_termination tp σ (TermRet v) →
  is_ctrace (CTRet v) 0 (compile_tp tp).
Proof.
  intros Hterm.
  inversion Hterm. subst.
  rewrite /compile_tp. rewrite /compile_expr_yield //. simpl_itree.
  exists (Ret v). split; first done. constructor.
Qed.

Lemma trace_invariant_ret tp σ v :
  tp_termination tp σ (TermRet v) →
  trace_invariant σ (TermRet v) (CTRet v).
Proof.
  intros Hterm. inversion Hterm. subst.
  split; last done.
  constructor.
Qed.

Lemma UnOp_stuck op v σ :
  stuck (UnOp op (Val v)) σ →
  un_op_eval op v = None.
Proof.
  intros [_ Hstuck].
  destruct (un_op_eval op v) as [w|] eqn:Heq; last done.
  apply except. eapply Hstuck.
  eapply Ectx_step with (K := []); eauto.
  by constructor.
Qed.

Lemma BinOp_stuck op v1 v2 σ :
  stuck (BinOp op (Val v1) (Val v2)) σ →
  bin_op_eval op v1 v2 = None.
Proof.
  intros [_ Hstuck].
  destruct (bin_op_eval op v1 v2) as [w|] eqn:Heq; last done.
  apply except. eapply Hstuck.
  eapply Ectx_step with (K := []); eauto.
  by constructor.
Qed.

Lemma enumerate_from_lookup' {A} (n : nat) (xs : list A) (idx : nat) :
  (enumerate_from n xs) !! idx = (λ x, (n + idx, x)) <$> (xs !! idx).
Proof.
  revert idx n.
  induction xs as [|x xs IH]; first done.
  intros idx n.
  destruct idx as [|idx']; first by replace (n + 0) with n by lia.
  rewrite enumerate_from_cons /= IH.
  destruct (xs !! idx'); last done.
  simpl. f_equiv. f_equiv. lia.
Qed.
Lemma enumerate_lookup' {A} (xs : list A) (idx : nat) :
  (enumerate xs) !! idx = (λ x, (idx, x)) <$> (xs !! idx).
Proof. apply enumerate_from_lookup'. Qed.

Definition ctrace_step_yield (tid : nat) (tr : ctrace (demonicE +' stateE state +' laterE +' ubE) val) :=
  CTVis () (subevent _ ELater) () (CTYield tid tr).
Lemma is_ctrace_step_yield tid tid' tp tr t :
  tp !! tid = Some (step ;; yield ;; t)%itree →
  is_ctrace tr tid' (<[tid := t]>tp) →
  is_ctrace (ctrace_step_yield tid' tr) tid tp.
Proof.
  intros Htp Htr. rewrite /ctrace_step_yield.
  eapply is_ctrace_insert; first done. { eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  rewrite list_insert_insert.
  eapply is_ctrace_yield.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  by rewrite list_insert_insert.
Qed.

Lemma state_invariant_yield tid σ tr :
  trace_invariant_state σ tr →
  trace_invariant_state σ (CTYield tid tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant_state. rewrite /trace_invariant_state in Hinv.
  rewrite /ctrace_step_yield /=. by destruct (interp_tr_state _ _).
Qed.

Lemma state_invariant_step_yield tid σ tr :
  trace_invariant_state σ tr →
  trace_invariant_state σ (ctrace_step_yield tid tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant_state. rewrite /trace_invariant_state in Hinv.
  rewrite /ctrace_step_yield /=. by destruct (interp_tr_state _ _).
Qed.

Definition ctrace_store' l x σ (tr : ctrace (demonicE +' stateE state +' laterE +' ubE) val) :=
  CTVis state (subevent _ EGetState) σ (CTVis () (subevent _ (ESetState (state_upd_heap <[l:=x]> σ))) () tr).
Definition ctrace_store l x σ (tr : ctrace (demonicE +' stateE state +' laterE +' ubE) val) :=
  ctrace_store' l (Some x) σ tr.
Definition ctrace_load σ (tr : ctrace (demonicE +' stateE state +' laterE +' ubE) val) :=
  CTVis state (subevent _ EGetState) σ tr.

Definition ctrace_store'_ub σ : ctrace (demonicE +' stateE state +' laterE +' ubE) val :=
  CTVis state (subevent _ EGetState) σ ctrace_ub.
Definition ctrace_store_ub σ :=
  ctrace_store'_ub σ.
Definition ctrace_load_ub σ : ctrace (demonicE +' stateE state +' laterE +' ubE) val:=
  CTVis state (subevent _ EGetState) σ ctrace_ub.

Lemma is_ctrace_store' σ l x v tid tp tr k :
  σ.(heap) !! l = Some (Some v) →
  tp !! tid = Some (ITree.bind (store' l x) k)%itree →
  is_ctrace tr tid (<[tid := k v]>tp) →
  is_ctrace (ctrace_store' l x σ tr) tid tp.
Proof.
  intros Hl Htp Htr.
  eapply is_ctrace_insert; first done. { rewrite /store'. eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  rewrite list_insert_insert Hl /=. simpl_itree.
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  rewrite list_insert_insert //.
Qed.
Lemma is_ctrace_store σ l x v tid tp tr k :
  σ.(heap) !! l = Some (Some v) →
  tp !! tid = Some (ITree.bind (store l x) k)%itree →
  is_ctrace tr tid (<[tid := k v]>tp) →
  is_ctrace (ctrace_store l x σ tr) tid tp.
Proof.
  intros Hl Htp Htr.
  by eapply is_ctrace_store'.
Qed.
Lemma is_ctrace_load σ l v tid tp tr k :
  σ.(heap) !! l = Some (Some v) →
  tp !! tid = Some (ITree.bind (load l) k)%itree →
  is_ctrace tr tid (<[tid := k v]>tp) →
  is_ctrace (ctrace_load σ tr) tid tp.
Proof.
  intros Hl Htp Htr.
  eapply is_ctrace_insert; first done. { rewrite /load. eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  rewrite list_insert_insert Hl /=. by simpl_itree.
Qed.

Lemma is_ctrace_store'_ub σ l x tid tp k :
  σ.(heap) !! l = Some None ∨ σ.(heap) !! l = None →
  tp !! tid = Some (ITree.bind (store' l x) k)%itree →
  is_ctrace (ctrace_store'_ub σ) tid tp.
Proof.
  intros Hl Htp.
  eapply is_ctrace_insert; first done. { rewrite /store'. eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  destruct Hl as [Hl|Hl].
  - rewrite list_insert_insert Hl /ub.
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  - rewrite list_insert_insert Hl /ub.
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
Qed.
Lemma is_ctrace_store_ub σ l x tid tp k :
  σ.(heap) !! l = Some None ∨ σ.(heap) !! l = None →
  tp !! tid = Some (ITree.bind (store l x) k)%itree →
  is_ctrace (ctrace_store_ub σ) tid tp.
Proof.
  intros Hl Htp.
  eapply is_ctrace_insert; first done. { rewrite /store. eutt_norm. reflexivity. }
  eapply is_ctrace_store'_ub; first done.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
Qed.
Lemma is_ctrace_load_ub σ l tid tp k :
  σ.(heap) !! l = Some None ∨ σ.(heap) !! l = None →
  tp !! tid = Some (ITree.bind (load l) k)%itree →
  is_ctrace (ctrace_store_ub σ) tid tp.
Proof.
  intros Hl Htp.
  eapply is_ctrace_insert; first done. { rewrite /load. eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  destruct Hl as [Hl|Hl].
  - rewrite list_insert_insert Hl /ub.
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  - rewrite list_insert_insert Hl /ub.
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
Qed.

Lemma state_invariant_store' l x σ tr :
  trace_invariant_state (state_upd_heap <[l:=x]> σ) tr →
  trace_invariant_state σ (ctrace_store' l x σ tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant_state. rewrite /trace_invariant_state in Hinv.
  simpl. rewrite decide_True //.
Qed.
Lemma state_invariant_store l x σ tr :
  trace_invariant_state (state_upd_heap <[l:=Some x]> σ) tr →
  trace_invariant_state σ (ctrace_store l x σ tr).
Proof.
  intros Hinv. by apply state_invariant_store'.
Qed.
Lemma state_invariant_load σ tr :
  trace_invariant_state σ tr →
  trace_invariant_state σ (ctrace_load σ tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant_state. rewrite /trace_invariant_state in Hinv.
  simpl. rewrite decide_True //.
Qed.

Lemma stuck_ub tp σ :
  tp_termination tp σ TermUb →
  ∃ tid tr, trace_invariant σ TermUb tr ∧ is_ctrace tr tid (compile_tp tp).
Proof.
  intros Hterm.
  assert (Hterm' := Hterm).
  apply tp_termination_ub in Hterm' as (tid&e&Htp&(K&e'&->&Hbasic&Hstuck)%stuck_basic).
  exists tid.
  destruct Hbasic as [x|f x e0|v1 v2 | | | | | | | | | | | | | | | | | | ].
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    rewrite /compile_expr. is_ctrace_norm/=.
    eapply is_ctrace_ub.
    rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    destruct (val_to_RecV v1) as [[[f x] e]|] eqn:Heq.
    * destruct v1; try discriminate.
      eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    rewrite /compile_expr. is_ctrace_norm/=.
    apply UnOp_stuck in Hstuck as ->.
    is_ctrace_norm/=. eapply is_ctrace_ub.
    rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    rewrite /compile_expr. is_ctrace_norm/=.
    apply BinOp_stuck in Hstuck as ->.
    is_ctrace_norm/=. eapply is_ctrace_ub.
    rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    destruct (val_to_bool v0) as [|] eqn:Heq.
    * destruct v0; try discriminate. destruct l; try discriminate.
      destruct b0;
      eapply stuck_false in Hstuck as [];
      eapply Ectx_step with (K := []); eauto;
      constructor.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    destruct (val_to_pair v) as [[x y]|] eqn:Heq.
    * destruct v; try discriminate.
      eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    destruct (val_to_pair v) as [[x y]|] eqn:Heq.
    * destruct v; try discriminate.
      eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    destruct (val_to_sum v0) as [[x|y]|] eqn:Heq.
    * destruct v0; try discriminate.
      eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * destruct v0; try discriminate.
      eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - exists ctrace_ub.
    split; first split.
    { constructor. }
    { done. }
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
    destruct (val_to_int nv) as [n|] eqn:Heq.
    * destruct nv; try discriminate. destruct l; try discriminate.
      injection Heq as ->.
      destruct (decide (0 < n)%Z).
      + eapply stuck_false in Hstuck as [].
        eapply Ectx_step with (K := []); eauto.
        apply AllocNS with (l := Loc.fresh (dom σ.(heap))); first done.
        intros i Hlower Hupper.  apply not_elem_of_dom_1. by apply Loc.fresh_fresh.
      + rewrite /compile_expr. is_ctrace_norm/=. rewrite assert_False /=. is_ctrace_norm/=.
        eapply is_ctrace_ub.
        rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. done.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - destruct (val_to_loc v) as [l|] eqn:Heq.
    * destruct (σ.(heap) !! l) as [[x|]|] eqn:Hheap.
      + destruct v; try discriminate.
        destruct l0; try discriminate.
        injection Heq as <-.
        eapply stuck_false in Hstuck as [].
        eapply Ectx_step with (K := []); eauto.
        by eapply FreeS.
      + exists (ctrace_store'_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_store'_ub; first by left.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_store'_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_store'_ub; first by right.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first split.
      { constructor. }
      { done. }
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
      rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - destruct (val_to_loc v) as [l|] eqn:Heq.
    * destruct (σ.(heap) !! l) as [[x|]|] eqn:Hheap.
      + destruct v; try discriminate.
        destruct l0; try discriminate.
        injection Heq as <-.
        eapply stuck_false in Hstuck as [].
        eapply Ectx_step with (K := []); eauto.
        by eapply LoadS.
      + exists (ctrace_load_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_load_ub; first by left.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_load_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_load_ub; first by right.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first split.
      { constructor. }
      { done. }
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
      rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - destruct (val_to_loc v1) as [l|] eqn:Heq.
    * destruct (σ.(heap) !! l) as [[x|]|] eqn:Hheap.
      + destruct v1; try discriminate.
        destruct l0; try discriminate.
        injection Heq as <-.
        eapply stuck_false in Hstuck as [].
        eapply Ectx_step with (K := []); eauto.
        by eapply StoreS.
      + exists (ctrace_store_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_store_ub; first by left.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_store_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_store_ub; first by right.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first split.
      { constructor. }
      { done. }
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
      rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - destruct (val_to_loc v1) as [l|] eqn:Heq.
    * destruct (σ.(heap) !! l) as [[x|]|] eqn:Hheap.
      + destruct v1; try discriminate.
        destruct l0; try discriminate.
        injection Heq as <-.
        eapply stuck_false in Hstuck as [].
        eapply Ectx_step with (K := []); eauto.
        by eapply XchgS.
      + exists (ctrace_store_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_store_ub; first by left.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_store_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_store_ub; first by right.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first split.
      { constructor. }
      { done. }
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
      rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - destruct (val_to_loc v1) as [l|] eqn:Heq.
    * destruct (σ.(heap) !! l) as [[x|]|] eqn:Hheap.
      + destruct (decide (vals_compare_safe x v2)).
        ++ destruct v1; try discriminate.
           destruct l0; try discriminate.
           injection Heq as <-.
           eapply stuck_false in Hstuck as [].
           eapply Ectx_step with (K := []); eauto.
           by eapply CmpXchgS.
        ++ exists (ctrace_load σ ctrace_ub).
           split; first split.
           +++ repeat constructor.
           +++ rewrite /trace_invariant_state /= decide_True //.
           +++ eapply is_ctrace_insert.
               { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
               { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
               rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
               eapply is_ctrace_load; first done.
               { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
               is_ctrace_norm/=. rewrite assert_False // /ub.
               eapply is_ctrace_ub.
               rewrite list_lookup_insert // insert_length compile_tp_len -lookup_lt_is_Some //.
      + exists (ctrace_load_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_load_ub; first by left.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_load_ub σ).
        split; first split.
        ++ repeat constructor.
        ++ rewrite /trace_invariant_state /= decide_True //.
        ++ eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           eapply is_ctrace_load_ub; first by right.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first split.
      { constructor. }
      { done. }
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
      rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - destruct (val_to_int v2) as [n|] eqn:Heq'.
    * destruct (val_to_loc v1) as [l|] eqn:Heq.
      + destruct (σ.(heap) !! l) as [[x|]|] eqn:Hheap.
        ++ destruct (val_to_int x) as [y|] eqn:Heq''.
           +++ destruct v1; try discriminate.
               destruct l0; try discriminate.
               destruct v2; try discriminate.
               destruct l1; try discriminate.
               destruct x; try discriminate.
               destruct l1; try discriminate.
               injection Heq as <-.
               eapply stuck_false in Hstuck as [].
               eapply Ectx_step with (K := []); eauto.
               by eapply FaaS.
           +++ exists (ctrace_load σ ctrace_ub).
               split; first split.
               ++++ repeat constructor.
               ++++ rewrite /trace_invariant_state /= decide_True //.
               ++++ eapply is_ctrace_insert.
                    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
                    { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
                    rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
                    eapply is_ctrace_load; first done.
                    { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
                    is_ctrace_norm/=. rewrite Heq''.
                    eapply is_ctrace_ub.
                    rewrite list_lookup_insert // insert_length compile_tp_len -lookup_lt_is_Some //.
        ++ exists (ctrace_load_ub σ).
           split; first split.
           +++ repeat constructor.
           +++ rewrite /trace_invariant_state /= decide_True //.
           +++ eapply is_ctrace_insert.
               { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
               { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
               rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
               eapply is_ctrace_load_ub; first by left.
               { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
        ++ exists (ctrace_load_ub σ).
           split; first split.
           +++ repeat constructor.
           +++ rewrite /trace_invariant_state /= decide_True //.
           +++ eapply is_ctrace_insert.
               { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
               { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
               rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
               eapply is_ctrace_load_ub; first by right.
               { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists ctrace_ub.
        split; first split.
        { constructor. }
        { done. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
        eapply is_ctrace_ub.
        rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
    * exists ctrace_ub.
      split; first split.
      { constructor. }
      { done. }
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind'; first done. admit. }
      rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq' /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - admit.
Admitted.

Program Definition to_free_location n v σ ρs l efs (Hbase : base_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ ρs (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) efs) : free_locations n σ :=
  exist (λ l, bool_decide (∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ.(heap) !! (l +ₗ i) = None))) l _.
Next Obligation. intros. simpl. apply bool_decide_pack. by inversion Hbase. Qed.
Lemma AllocN_free_locations n v σ ρs l efs :
  base_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ ρs (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) efs →
  ∃ (l' : free_locations n σ), `l' = l.
Proof. intros Hbase. by exists (to_free_location n v σ ρs l efs Hbase). Qed.

Lemma step_in_thread e1 σ1 κs e2 σ2 efs tr tid tid' tp (k : val → itree heaplangE val) tx :
  base_step e1 σ1 κs e2 σ2 efs →
  is_ctrace tr tid' (<[tid:=(v ← compile_expr_yield e2 ; k v)%itree]>tp
                    ++ compile_tp' efs) →
  trace_invariant σ2 tx tr →
  tp !! tid = Some (v ← compile_expr_yield e1 ; k v)%itree →
  ∃ tr', trace_invariant σ1 tx tr' ∧ is_ctrace tr' tid tp.
Proof.
  intros Hbase Htr (Hub&Hstinv) Htp.
  inversion Hbase; subst; simpl in Htr; rewrite ?app_nil_r in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (RecV f x e)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (PairV v1 v2)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (InjLV v)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (InjRV v)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - pose (e' := subst' x v2 (subst' f (RecV f x e0) e0)).
    destruct (to_val e') as [v|] eqn:Hval.
    * exists (CTYield tid' tr). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { by apply state_invariant_yield. }
      eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield /= base_Beta /= /step_if_not_val /yield_if_not_val.
        rewrite /e' in Hval. rewrite Hval. rewrite bind_ret_l.
        eutt_norm/=. reflexivity. }
      rewrite /e' in Hval. apply of_to_val in Hval as Heq.
      rewrite -Heq in Htr. rewrite -Heq. rewrite /compile_expr. is_ctrace_norm/=. simpl_itree in Htr.
      apply is_ctrace_yield with (t := k v).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      by rewrite list_insert_insert.
    * exists (ctrace_step_yield tid' tr). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { by apply state_invariant_step_yield. }
      eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield /= base_Beta /= /yield_if_not_val /step_if_not_val.
        rewrite /e' in Hval. rewrite Hval. eutt_norm/=. reflexivity. }
      rewrite /e' in Hval. rewrite /compile_expr_yield /yield_if_not_val /step_if_not_val in Htr.
      rewrite Hval in Htr.
      rewrite bind_bind in Htr. setoid_rewrite bind_bind in Htr. setoid_rewrite bind_ret_l in Htr.
      apply is_ctrace_step_yield with (t := (v ← compile_expr e'; yield ;; k v)%itree).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert //.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (step ;; yield ;; k v')%itree); first done.
    { rewrite /compile_expr_yield base_UnOp //. eutt_norm/=. rewrite /step_ret. by eutt_norm/=. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (step ;; yield ;; k v')%itree); first done.
    { rewrite /compile_expr_yield base_BinOp //. eutt_norm/=. rewrite /step_ret. by eutt_norm/=. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - destruct (to_val e2) eqn:Hval.
    * exists (CTYield tid' tr). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { by apply state_invariant_yield. }
      apply of_to_val in Hval as <-.
      eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield/compile_expr/=. eutt_norm/=. reflexivity. }
      apply is_ctrace_yield with (t := k v).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
    * exists (ctrace_step_yield tid' tr). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { by apply state_invariant_step_yield. }
      eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
        rewrite /yield_if_not_val /step_if_not_val Hval /=. reflexivity. }
      rewrite /compile_expr_yield/yield_if_not_val Hval in Htr. simpl_itree in Htr.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
  - destruct (to_val e2) eqn:Hval.
    * exists (CTYield tid' tr). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { by apply state_invariant_yield. }
      apply of_to_val in Hval as <-.
      eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
        rewrite /step_if_not_val /=. reflexivity. }
      apply is_ctrace_yield with (t := k v).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
    * exists (ctrace_step_yield tid' tr). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { by apply state_invariant_step_yield. }
      eapply is_ctrace_insert; first done.
      { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
        rewrite /yield_if_not_val /step_if_not_val Hval /=. reflexivity. }
      rewrite /compile_expr_yield/yield_if_not_val Hval in Htr. simpl_itree in Htr.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (step ;; yield ;; k v1)%itree); first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (step ;; yield ;; k v2)%itree); first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
      rewrite /step_if_not_val /=. reflexivity. }
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    rewrite /compile_expr_yield bind_bind in Htr.
    setoid_rewrite bind_bind in Htr. setoid_rewrite bind_ret_l in Htr.
    by rewrite interp_recursive_call.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
      rewrite /yield_if_not_val /=. reflexivity. }
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite /compile_expr_yield bind_bind in Htr.
    setoid_rewrite bind_bind in Htr. setoid_rewrite bind_ret_l in Htr.
    by rewrite list_insert_insert interp_recursive_call.
  - destruct (AllocN_free_locations _ _ _ _ _ _ Hbase) as [ll <-].
    exists (CTVis state (subevent _ EGetState) σ1 (CTVis (free_locations n σ1) (subevent _ (EDemonic (free_locations n σ1))) ll (CTVis () (subevent _ (ESetState (state_init_heap (`ll) n v σ1))) () (ctrace_step_yield tid' tr)))).
    repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { rewrite /trace_invariant_state /= decide_True //. by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    rewrite assert_True; last lia. is_ctrace_norm/=.
    eapply is_ctrace_Vis.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    eapply is_ctrace_Vis.
    { rewrite list_lookup_insert // insert_length -lookup_lt_is_Some //. }
    simpl.
    eapply is_ctrace_Vis.
    { rewrite list_insert_insert list_lookup_insert // insert_length -lookup_lt_is_Some //. }
    rewrite !list_insert_insert.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_store' l None σ1 (ctrace_step_yield tid' tr)). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { rewrite /trace_invariant_state /= decide_True //. by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_store'; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert // insert_length. by apply lookup_lt_is_Some. }
    rewrite !list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_load σ2 (ctrace_step_yield tid' tr)). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { rewrite /trace_invariant_state /= decide_True //. by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_load; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite list_insert_insert.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_store l w σ1 (ctrace_step_yield tid' tr)). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { rewrite /trace_invariant_state /= decide_True //. by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_store; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite !list_insert_insert.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_store l v2 σ1 (ctrace_step_yield tid' tr)). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { rewrite /trace_invariant_state /= decide_True //. by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_store; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite !list_insert_insert.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - destruct (decide (vl = v1)) as [->|Hneq].
    * rewrite bool_decide_eq_true_2 // in Hstinv.
      rewrite bool_decide_eq_true_2 // in Hbase.
      rewrite bool_decide_eq_true_2 // in Htr.
      exists (ctrace_load σ1 (ctrace_store l v2 σ1 (ctrace_step_yield tid' tr))). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { rewrite /trace_invariant_state /= !decide_True //. by apply state_invariant_step_yield. }
      eapply is_ctrace_insert; first done.
      { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. reflexivity. }
      eapply is_ctrace_load; first done.
      { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
      rewrite !list_insert_insert assert_True //. is_ctrace_norm/=.
      rewrite decide_True //. is_ctrace_norm/=.
      eapply is_ctrace_store; first done.
      { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
      rewrite !list_insert_insert. rewrite /step_ret. is_ctrace_norm/=.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
    * rewrite bool_decide_eq_false_2 // in Hstinv.
      rewrite bool_decide_eq_false_2 // in Hbase.
      rewrite bool_decide_eq_false_2 // in Htr.
      exists (ctrace_load σ1 (ctrace_step_yield tid' tr)). repeat split.
      { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
        repeat constructor. }
      { rewrite /trace_invariant_state /= !decide_True //. by apply state_invariant_step_yield. }
      eapply is_ctrace_insert; first done.
      { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. reflexivity. }
      eapply is_ctrace_load; first done.
      { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
      simpl. rewrite list_insert_insert. rewrite assert_True // decide_False // /step_ret. is_ctrace_norm/=.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
  - exists (ctrace_load σ1 (ctrace_store l (LitV (LitInt (i1 + i2))) σ1 (ctrace_step_yield tid' tr))). repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { rewrite /trace_invariant_state /= !decide_True //. by apply state_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. reflexivity. }
    eapply is_ctrace_load; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite list_insert_insert /step_ret. is_ctrace_norm/=.
    eapply is_ctrace_store; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite list_insert_insert.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (CTFork (compile_expr_kill e) (ctrace_step_yield tid' tr)).
    repeat split.
    { apply trace_invariant_postfix_postfix with (tr := tr); eauto.
      repeat constructor. }
    { by apply state_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield. eutt_norm/=. reflexivity. }
    eapply trace_base_Fork.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    simpl. eapply is_ctrace_step_yield.
    { rewrite lookup_app_l; last rewrite !insert_length -lookup_lt_is_Some //.
      rewrite list_lookup_insert //. rewrite insert_length. by apply lookup_lt_is_Some. }
    rewrite insert_app_l; last rewrite !insert_length -lookup_lt_is_Some //.
    rewrite !list_insert_insert //.
  - admit.
  - admit.
Admitted.

Lemma lt_gt n m :
  n < m ↔ m > n.
Proof. lia. Qed.

(* TODO: Idea: make κ = [] *)
Lemma has_trace n tp σ tp' σ' κ tx :
  language.nsteps n (tp, σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  length tp > 0 →
  ∃ tid tr,
    trace_invariant σ tx tr ∧
    is_ctrace (R := val) tr tid (compile_tp tp).
Proof.
  revert tp σ tp' σ' κ. induction n as [|n IH]; intros tp σ tp' σ' κ Hstep Hterm Hne.
  { destruct tx as [r|].
    - assert (Hterm' := Hterm).
      apply is_ctrace_ret  in Hterm as Htr.
      apply trace_invariant_ret with (σ := σ') in Hterm' as Htinv.
      exists 0, (CTRet r). inversion Hstep. subst. by split.
    - inversion Hstep; subst.
      apply stuck_ub in Hterm as (tid&tr&Hinv&Htr); eauto.
  }
  inversion Hstep as [|m [tp1 σ1] [tp2 σ2] [tp3 σ3] ? ? Hstep'' Hstep']. subst.
  inversion Hstep'' as [e1' σ1 e2' σ2' efs tpa tpb Htp' Htp2' Hprim].
  injection Htp'. intros -> ->. clear Htp'.
  injection Htp2'. intros -> ->. clear Htp2'.
  inversion Hprim as [K e1 e2 He1 He2 Hbase]. subst. simpl in K, e1, e2.
  clear Hstep'' Hprim.
  (* TODO: Use [compile_expr_bind'] *)
  destruct (decide (length K = 0)) as [HK|HK].
  - apply nil_length_inv in HK as ->. simpl. simpl in *.
    apply IH in Hstep' as [tid [tr [Hinv Htr]]]; eauto; last first.
    { rewrite app_length /= app_length.
      rewrite app_length /= in Hne.
      lia.
    }
    destruct (decide (length tpa = 0)) as [Htpa|Htpa].
    * apply nil_length_inv in Htpa as ->. simpl. simpl in *.
      apply step_in_thread with (tp := ((v ← compile_expr_yield e1 ; Ret v)%itree :: compile_tp' tpb)) (tid := 0) (tid' := tid) (k := λ v, Ret v) (tr := tr) (tx := tx) in Hbase as [tr' [Hinv' Htr']].
      + exists 0, tr'. rewrite compile_tp_cons //.
      + simpl. rewrite compile_tp_cons compile_tp'_app // in Htr.
      + done.
      + done.
    * apply step_in_thread with (tp := (compile_tp tpa ++ (compile_expr_kill e1)%itree :: compile_tp' tpb)) (tid := length (compile_tp tpa)) (tid' := tid) (k := λ v, kill_thread) (tr := tr) (tx := tx) in Hbase as [tr' [Hinv' Htr']].
      + exists (length (compile_tp tpa)), tr'. rewrite compile_tp_app //.
      + replace (length (compile_tp tpa)) with (length (compile_tp tpa) + 0) by lia.
        rewrite compile_tp_app // in Htr.
        rewrite insert_app_r /= -app_assoc /=.
        rewrite compile_tp'_cons compile_tp'_app // in Htr.
      + done.
      + by apply list_lookup_middle.
  - apply IH in Hstep' as [tid [tr [Hinv Htr]]]; eauto; last first.
    { rewrite -lt_gt -Nat.neq_0_lt_0. intros Hemp%nil_length_inv.
      apply app_eq_nil in Hemp as [_ [=]].
    }
    destruct (decide (length tpa = 0)) as [Htpa|Htpa].
    * apply nil_length_inv in Htpa as ->. simpl. simpl in *.
      apply step_in_thread with (tp := ((v ← compile_expr_yield e1; w ← compile_expr (fill K (Val v)); yield ;; Ret w)%itree :: compile_tp' tpb)) (tid := 0) (tid' := tid) (k := λ v, (w ← compile_expr (fill K (Val v)); yield ;; Ret w)%itree) (tr := tr) (tx := tx) in Hbase as [tr' [Hinv' Htr']].
      + exists 0, tr'.
        split; first done.
        rewrite compile_tp_cons /= /compile_expr_yield compile_expr_bind.
        ++ setoid_rewrite fill_not_val; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           rewrite /compile_expr_yield in Htr'. simpl_itree. simpl_itree in Htr'. done.
        ++ admit.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + simpl.
        rewrite compile_tp_cons /= /compile_expr_yield compile_expr_bind in Htr.
        ++ setoid_rewrite fill_not_val in Htr; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           do 2 setoid_rewrite bind_bind in Htr.
           simpl_itree in Htr. simpl_itree.
           by rewrite compile_tp'_app in Htr.
        ++ admit.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + done.
      + done.
    * rewrite compile_tp_app // in Htr.
      rewrite compile_tp_app //.
      apply step_in_thread with (tp := (compile_tp tpa ++ (v ← compile_expr e1; yield_if_not_val e1;; compile_expr_kill (fill K (Val v)))%itree :: compile_tp' tpb)) (tid := length tpa) (tid' := tid) (k := λ v, (compile_expr (fill K (Val v));; yield ;; kill_thread)%itree) (tr := tr) (tx := tx) in Hbase as [tr' [Hinv' Htr']].
      + exists (length tpa), tr'.
        split; first done.
        rewrite /= /compile_expr_kill/compile_expr_yield compile_expr_bind.
        ++ setoid_rewrite fill_not_val; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           rewrite /compile_expr_kill/compile_expr_yield in Htr'.
           setoid_rewrite fill_not_val in Htr'; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           simpl_itree in Htr'. simpl_itree. done.
        ++ admit.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + replace (length tpa) with (length (compile_tp tpa) + 0) by rewrite compile_tp_len //.
        rewrite insert_app_r /= -app_assoc /=.
        rewrite compile_tp'_cons compile_tp'_app /= /compile_expr_kill/compile_expr_yield compile_expr_bind in Htr.
        ++ setoid_rewrite fill_not_val in Htr; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           simpl_itree in Htr. simpl_itree. done.
        ++ admit.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + done.
Admitted.

Lemma interp_tr_state_ub {E R S} `{EqDecision S} `{ubE -< E} σ (tr : trace (stateE S +' E) R) tr' :
  trace_terminates_in tr TermUb →
  interp_tr_state σ tr = Some tr' →
  trace_terminates_in tr' TermUb.
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

Lemma interp_tr_term {E E' R} `{ubE -< E'} (tr : trace (E +' E') R) (tx : Terminal R) :
  trace_terminates_in tr tx →
  trace_terminates_in (interp_tr tr) tx.
Proof.
  intros Hterm.
  induction tr.
  - rewrite /= /trace_terminates_in. rewrite /trace_terminates_in in Hterm.
    destruct tx; inversion Hterm. subst. constructor.
  - simpl. destruct e.
    * apply IHtr. destruct tx; inversion Hterm; by simplify_K.
    * constructor. apply IHtr. destruct tx; inversion Hterm; by simplify_K.
  - rewrite /= /trace_terminates_in. rewrite /trace_terminates_in in Hterm.
    destruct tx; inversion Hterm. subst. constructor.
  - rewrite /= /trace_terminates_in. rewrite /trace_terminates_in in Hterm.
    destruct tx; inversion Hterm.
Qed.

Lemma sequencify_term {E E' R} `{ubE -< E'} (tr : ctrace (E +' E') R) (tx : Terminal R) :
  ctrace_terminates_in tr tx →
  trace_terminates_in (sequencify tr) (inl <$> tx).
Proof.
  intros Hterm.
  induction tr.
  - rewrite /= /trace_terminates_in. rewrite /trace_terminates_in in Hterm.
    destruct tx; inversion Hterm. subst. constructor.
  - simpl. constructor. apply IHtr. destruct tx; inversion Hterm; by simplify_K.
  - rewrite /= /trace_terminates_in.
    destruct tx; inversion Hterm. subst. constructor.
  - simpl. apply IHtr. destruct tx; inversion Hterm; by simplify_K.
  - simpl. apply IHtr. destruct tx; inversion Hterm; by simplify_K.
  - rewrite /= /trace_terminates_in. destruct tx; inversion Hterm.
  - simpl. apply IHtr. destruct tx; inversion Hterm; by simplify_K.
  - rewrite /= /trace_terminates_in. destruct tx; inversion Hterm.
Qed.

Lemma interp_tr_state_ret {E R S} `{EqDecision S} `{ubE -< E} σ (tr : trace (stateE S +' E) R) tr' (r : R) :
  trace_terminates_in tr (TermRet r) →
  interp_tr_state σ tr = Some tr' →
  ∃ σ, trace_terminates_in tr' (TermRet (σ, r)).
Proof.
  revert σ tr'. induction tr; intros σ tr' Hret Hst.
  - inversion Hret. injection Hst as <-. exists σ. constructor.
  - destruct e as [e|e]; first destruct e as [|σ'].
    * simpl in Hst. destruct (decide (a = σ)) as [->|]; last discriminate.
      apply IHtr with (σ := σ); last done. by inversion Hret.
    * inversion Hret; simplify_K; simplify_K; subst. by eapply IHtr.
    * simpl in Hst. destruct (interp_tr_state σ tr) as [tr''|] eqn:Heq.
      + simpl in Heq. injection Hst as <-.
        inversion Hret. subst. simplify_K.
        apply IHtr in Heq as [σ' Hterm]; last done.
        exists σ'. by constructor.
      + discriminate.
  - inversion Hret; simplify_K; simplify_K; subst.
  - inversion Hret.
Qed.

Inductive terminates_in' {R} : itree' (laterE +' ubE) R → Terminal R → Prop :=
  | terminates_in_ELater tx k :
  terminates_in' (observe (k ())) tx →
  terminates_in' (VisF (inl1 ELater) k) tx
  | terminates_in_Tau tx t :
  terminates_in' (observe t) tx →
  terminates_in' (TauF t) tx
  | terminates_in_EUb k :
  terminates_in' (VisF (inr1 EUb) k) TermUb
  | terminates_in_Ret r :
  terminates_in' (RetF r) (TermRet r).
Definition terminates_in {R} (t : itree (laterE +' ubE) R) (tx : Terminal R) : Prop :=
  terminates_in' (observe t) tx.
Fixpoint model_terminal {R} (laters : nat) (tx : Terminal R) : itree (laterE +' ubE) R :=
  match laters with
  | O =>
    match tx with
    | TermRet r => Ret r
    | TermUb => ub
    end
  | S n => step ;; model_terminal n tx
  end.
Lemma terminates_in_model {R} (t : itree (laterE +' ubE) R) tx :
  terminates_in t tx →
  ∃ n, t ≈ model_terminal n tx.
Proof.
  intros Hterm. rewrite /terminates_in in Hterm.
  remember (observe t) as ot. revert t Heqot. induction Hterm; intros t' Heqot.
  - destruct (IHHterm (k ())) as [n Heutt]; first done.
    exists (S n). simplify_obs. simpl. rewrite bind_trigger.
    f_equiv. f_equiv. by intros [].
  - destruct (IHHterm t) as [n Heutt]; first done.
    exists n. simplify_obs. by transitivity t; first by apply tau_eutt.
  - exists 0. simplify_obs. simpl. rewrite /ub. f_equiv. f_equiv. intros [].
  - exists 0. by simplify_obs.
Qed.

Lemma is_trace_term {R} (t : itree (laterE +' ubE) R) tr tx :
  trace_terminates_in tr tx →
  is_trace tr t →
  terminates_in t tx.
Proof.
  intros Hterm Htr. rewrite /terminates_in. induction Htr.
  - destruct tx; inversion Hterm. by constructor.
  - destruct e as [e|e]; destruct e, a.
    constructor. apply IHHtr. destruct tx; by inversion Hterm.
  - destruct tx; inversion Hterm. destruct e as [e|e]; first by destruct e.
    destruct e. constructor.
  - destruct tx; inversion Hterm.
  - constructor. by apply IHHtr.
Qed.

Lemma execution n e σ tp' σ' κ tx :
  language.nsteps n ([e], σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  ∃ t1 t2 t3,
    (* TODO: consisting naming for interpretion relations *)
    (* TODO: abstraction for this composite relation *)
    threadpool_irel (R := val) (compile_expr_yield e) t1 ∧
    demonic_irel t1 t2 ∧
    state_irel σ t2 t3 ∧
    (* TODO: use UB adequacy *)
    match tx with
    | TermUb => terminates_in t3 TermUb
    | TermRet r => ∃ σ', terminates_in t3 (TermRet (σ', inl r))
    end.
Proof.
  intros Hsteps Hterm.
  apply has_trace with (tx := tx) in Hsteps as (tid&tr&[Htinv Hstinv]&Htr); eauto.
  rewrite /trace_invariant_state in Hstinv.
  destruct (interp_tr_state σ (interp_tr (sequencify tr))) as [tr'|] eqn:Heq;
    rewrite Heq // in Hstinv.
  rewrite /trace_invariant_postfix in Htinv.
  apply threadpool_trace in Htr as (t1&Hint&Htr).
  exists t1.
  eapply demonic_trace in Htr as (t2&Hinst&Htr).
  exists t2.
  eapply state_trace with (s := σ) in Htr as (t3&Heval&Htr); last done.
  exists t3.
  split.
  { destruct (interleaves_lookup _ _ _ Hint) as [t Hidx].
    destruct tid; last discriminate.
    rewrite /compile_tp in Hint. simpl in Hint.
    rewrite (bisimulation_is_eq _ _ (bind_ret_r (compile_expr_yield e))) in Hint.
    apply Hint.
  }
  split; first done.
  split; first done.
  destruct tx.
  - apply sequencify_term in Htinv. apply interp_tr_term in Htinv.
    eapply interp_tr_state_ret in Htinv as [σ'' Htinv]; last done.
    exists σ''. by apply is_trace_term with (t := t3) (tr := tr') (tx := TermRet (σ'', inl r)).
  - apply is_trace_term with (t := t3) (tr := tr') (tx := TermUb); eauto.
    eapply interp_tr_state_ub; last done. apply interp_tr_term. by apply sequencify_term in Htinv.
Qed.

Lemma model_wpi {R} `{!invGS_gen hlc Σ} M n (tx : Terminal R) (Φ : R → iProp Σ) :
  WPi (model_terminal n tx) @ laterH Identity ⊕ ubH ; M {{ Φ }} -∗
  |={M}=> match tx with
  | TermUb => False
  | TermRet v => Φ v
  end.
Proof.
  induction n; iIntros "Hwp".
  - simpl. destruct tx.
    * rewrite -wpi_ret' //.
    * by iDestruct (wpi_ub with "Hwp") as "Hwp".
  - iApply IHn. rewrite /= bind_vis -wpi_vis' /= wpi_clear_mask. by simpl_itree.
Qed.

Lemma model_wpi_later' {R} `{!invGS_gen hlc Σ} n (tx : Terminal R) (Φ : R → iProp Σ) :
  WPi (model_terminal n tx) @ laterH Later ⊕ ubH ; ∅ {{ Φ }} -∗
  |={∅}=> |={∅}▷=>^n match tx with
  | TermUb => False
  | TermRet v => Φ v
  end.
Proof.
  induction n; iIntros "Hwp".
  - simpl. destruct tx.
    * rewrite -wpi_ret' //.
    * by iDestruct (wpi_ub with "Hwp") as "Hwp".
  - iModIntro. simpl. iApply IHn. rewrite /= bind_vis -wpi_vis' /=.
    iMod "Hwp". iModIntro. iNext.
    simpl_itree. iApply wpi_clear_mask. by iModIntro.
Qed.

Lemma model_wpi_later {R} `{!invGS_gen hlc Σ} M n (tx : Terminal R) (Φ : R → iProp Σ) :
  WPi (model_terminal n tx) @ laterH Later ⊕ ubH ; M {{ Φ }} -∗
  |={M, ∅}=> |={∅}▷=>^n match tx with
  | TermUb => False
  | TermRet v => |={∅, M}=> Φ v
  end.
Proof.
  iIntros "Hwp".
  iDestruct (wpi_clear_mask with "Hwp") as "Hwp".
  iDestruct (model_wpi_later' with "Hwp") as "Hpost".
  by iMod "Hpost".
Qed.

End adequacy.

Lemma execution_wpi' n e σ tp' σ' κ tx:
  language.nsteps n ([e], σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  (∀ hlc Σ (Hinv : invGS_gen hlc Σ) (Hhl : heaplangHGS Σ) Φ,
      state_interp σ -∗
  WPi (compile_expr_yield e) @ heaplangH Identity ; ⊤ {{ Φ }} -∗
  |={⊤}=> match tx with
  | TermUb => False
  | TermRet v => Φ v
  end).
Proof.
  iIntros (Hstep Hstuck ? ? ? ? ?).
  apply execution with (tx := tx) in Hstep as (t1&t2&t3&Hint&Hinst&Heval&Hterm); last done.
  iIntros "Hstate Hwp".
  (* TODO: Name these adequacy theorems consistently. *)
  iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; first apply Hint.
  iDestruct (demonic_adequacy with "Hwp") as "Hwp"; first apply Hinst.
  iDestruct (state_adequacy with "Hstate Hwp") as "Hwp"; first apply Heval.
  destruct tx.
  - destruct Hterm as [σ'' [n' ->]%terminates_in_model].
    iDestruct (model_wpi with "Hwp") as "Hwp".
    by iMod "Hwp" as "[_ HΦ]".
  - apply terminates_in_model in Hterm as [n' ->].
    by iDestruct (model_wpi with "Hwp") as "Hwp".
Qed.

Lemma execution_wpi_later' n e σ tp' σ' κ tx :
  language.nsteps n ([e], σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  ∃ n,
    (∀ hlc Σ (Hinv : invGS_gen hlc Σ) (Hhl : heaplangHGS Σ) Φ,
    state_interp σ -∗
    WPi (compile_expr_yield e) @ heaplangH Later ; ⊤ {{ Φ }} -∗
    |={⊤, ∅}=> |={∅}▷=>^n match tx with
    | TermUb => False
    | TermRet v => |={∅, ⊤}=> Φ v
    end).
Proof.
  iIntros (Hstep Hstuck).
  apply execution with (tx := tx) in Hstep as (t1&t2&t3&Hint&Hinst&Heval&Hterm); last done.
  destruct tx.
  - destruct Hterm as [σ'' [n' Ht3]%terminates_in_model].
    exists n'.
    iIntros (? ? ? ? ?) "Hstate Hwp".
    (* TODO: Name these adequacy theorems consistently. *)
    iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; first apply Hint.
    iDestruct (demonic_adequacy with "Hwp") as "Hwp"; first apply Hinst.
    iDestruct (state_adequacy with "Hstate Hwp") as "Hwp"; first apply Heval.
    rewrite Ht3.
    iDestruct (model_wpi_later with "Hwp") as "Hwp".
    iMod "Hwp". iModIntro.
    iApply step_fupdN_mono; last done. iIntros "[_ $]".
  - apply terminates_in_model in Hterm as [n' Ht3].
    exists n'.
    iIntros (? ? ? ? ?) "Hstate Hwp".
    (* TODO: Name these adequacy theorems consistently. *)
    iDestruct (threadpool_adequacy with "Hwp") as "Hwp"; first apply Hint.
    iDestruct (demonic_adequacy with "Hwp") as "Hwp"; first apply Hinst.
    iDestruct (state_adequacy with "Hstate Hwp") as "Hwp"; first apply Heval.
    rewrite Ht3.
    iDestruct (model_wpi_later with "Hwp") as "Hwp".
    iMod "Hwp". iModIntro.
    iApply step_fupdN_mono; last done. iIntros "$".
Qed.

Lemma compile_expr_execution_wpi' n e σ tp' σ' κ tx :
  language.nsteps n ([e], σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  (∀ hlc Σ (Hinv : invGS_gen hlc Σ) (Hhl : heaplangHGS Σ) Φ,
  state_interp σ -∗
  WPi (compile_expr e) @ heaplangH Identity ; ⊤ {{ Φ }} -∗
  |={⊤}=> match tx with
  | TermUb => False
  | TermRet v => Φ v
  end).
Proof.
  iIntros (Hstep Hterm ? ? ? ? ?) "Hstate Hwp".
  iApply (execution_wpi' with "Hstate"); eauto.
  iApply wpi_bind. iApply wpi_wand; last done.
  iIntros (r) "HΦ". iApply wpi_bind. rewrite /yield_if_not_val. destruct (to_val _).
  - iApply wpi_ret. by iApply wpi_ret.
  - iApply @wpi_yield. by iApply wpi_ret.
Qed.

Lemma compile_expr_execution_wpi_later n e σ tp' σ' κ tx :
  language.nsteps n ([e], σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  ∃ n,
  (∀ hlc Σ (Hinv : invGS_gen hlc Σ) (Hhl : heaplangHGS Σ) Φ,
  state_interp σ -∗
  WPi (compile_expr e) @ heaplangH Later ; ⊤ {{ Φ }} -∗
  |={⊤, ∅}=> |={∅}▷=>^n match tx with
  | TermUb => False
  | TermRet v => |={∅, ⊤}=> Φ v
  end).
Proof.
  iIntros (Hstep Hterm).
  odestruct (execution_wpi_later' _ _ _ _ _ _ _ _ _) as [n' Hwp]; eauto.
  exists n'. iIntros (? ? ? ? ?) "Hstate Hwp". iApply (Hwp with "Hstate").
  iApply wpi_bind. iApply wpi_wand; last done.
  iIntros (r) "HΦ". iApply wpi_bind. iApply wpi_yield_if_not_val.
  by iApply wpi_ret.
Qed.

From iris.program_logic Require Import adequacy.

(* TODO: deduplicate these proofs *)
Theorem heap_adequacy_later Σ `{!invGpreS Σ} `{!heaplangHGpreS Σ} e σ φ:
  (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Later; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  move => Hwp. apply adequate_alt => t2 σ2 /erased_steps_nsteps[n [κs Hsteps]].
  constructor.
  - move => ? ? ?.
    odestruct (compile_expr_execution_wpi_later _) as [n' Had]; [done| |].
    { subst. by constructor. }
    apply: (heaplang_soundness n').
    iIntros (? ?) "Hinv ??". iMod (Had with "[$] [Hinv]") as "Had".
    { iPoseProof Hwp as "Hwp". rewrite wp_heaplang_eq. by iApply "Hwp". }
    (* TODO: find a less hacky way to do this *)
    destruct n'.
    + simpl. iMod "Had". iApply fupd_mask_intro; [done|]. by iIntros "?".
    + iModIntro. iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "Had").
      iIntros ">$". iApply fupd_mask_intro; [done|]. by iIntros "?".
  - move => e2 _ /elem_of_list_lookup [? He2].
    destruct (decide (not_stuck e2 σ2)) as [?| Hstuck%not_not_stuck]; [done|].
    exfalso.
    odestruct (compile_expr_execution_wpi_later _) as [n' Had]; [done| |].
    { apply tp_termination_TermUb. eexists _, _. done. }
    apply: (heaplang_soundness n').
    iIntros (? ?) "Hinv ??". iMod (Had with "[$] [Hinv]") as "Had".
    { iPoseProof Hwp as "Hwp". rewrite wp_heaplang_eq. by iApply "Hwp". }
    iModIntro. iApply (step_fupdN_wand with "Had"). by iIntros (?).
Qed.

(* TODO: prove this via weakening *)
Theorem heap_adequacy_no_later Σ `{!invGpreS Σ} `{!heaplangHGpreS Σ} e σ φ:
  (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Identity; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  move => Hwp. apply adequate_alt => t2 σ2 /erased_steps_nsteps[n [κs Hsteps]].
  constructor.
  - move => ? ? ?.
    apply: (heaplang_soundness 0).
    iIntros (? ?) "Hinv ?? /=".
    iMod (compile_expr_execution_wpi' with "[$] [Hinv]") as "?"; [done|..].
    { subst. by constructor. }
    { iPoseProof Hwp as "Hwp". rewrite wp_heaplang_eq. by iApply "Hwp". }
    iApply fupd_mask_intro; [done|]. by iIntros "?".
  - move => e2 _ /elem_of_list_lookup [? He2].
    destruct (decide (not_stuck e2 σ2)) as [?| Hstuck%not_not_stuck]; [done|].
    exfalso.
    apply: (heaplang_soundness 0).
    iIntros (? ?) "Hinv ?? /=".
    iMod (compile_expr_execution_wpi' with "[$] [Hinv]") as "?"; [done|..].
    { apply tp_termination_TermUb. eexists _, _. done. }
    { iPoseProof Hwp as "Hwp". rewrite wp_heaplang_eq. by iApply "Hwp". }
    done.
Qed.
