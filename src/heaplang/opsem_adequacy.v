From iris.itree Require Import wpi ub itree choice state heap.
From iris.itree.threadpool Require Import ctrace.
From iris Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.program_logic Require Import language.
(* TODO: make the import order less brittle *)
From iris.itree.heaplang Require Import decide.
From iris.itree Require Import later handler void.
From iris.itree.threadpool Require Import handler interleaving.
From iris.itree.heaplang Require Import lang program_logic adequacy.
From Paco Require Import paco.
From Paco Require Import paco2.

Set Default Proof Using "Type*".

(* This file proves that our weakest precondition [WP] defined in terms of
ITrees is adequate with respect to the existing operational semantics of
heaplang. By [wp_partial_soundness], it suffices to show that partial adequacy
[partially_adequate] implies operational adequacy [adequate] (adequacy with
respect to the operational semantics). The high level structure of the proof is
a simulation. More specifically, from an operational semantics trace starting
at [e], we need to construct a relational interpretation (an execution) of its
semantic interpretation [compile_expr_yield e]. To do so, we invoke
[heaplang_trace], which in turn takes a [ctrace sequential_heaplangE val].
Thus, we need to construct such a [ctrace] from a trace in the operational
semantics. This is done inductively. *)

Lemma compile_Fork {R} e (k : val → itree heaplangE R) :
  (v ← compile_expr (Fork e) ; k v)%itree ≈ vis EFork (λ thread,
    match thread with
    | CurrentThread => later.step ;; k (LitV LitUnit)
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
  is_ctrace tr tid (<[tid := (later.step ;; k (LitV LitUnit))%itree]>tp ++ [compile_expr_kill e]) →
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
     in later.step ;; yield_if_not_val e' ;; compile_expr e'.
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
    Basic (FAA (Val v1) (Val v2)).

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
  (*
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    apply NewProphS with (p := fresh (σ.(used_proph_id))). apply is_fresh.
  - exists [], (Resolve e1 e2 e3). split; first done. by split; first constructor.
  *)
Qed.

Definition ctrace_ub {R} : ctrace sequential_heaplangE R :=
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

Definition Terminal (R : Type) : Type := R + ub_crash.
Notation TermUb := (inr UbCrash).
Notation TermRet r := (inl r).

Variant tp_termination : list expr → state → Terminal val → Prop :=
  | tp_termination_TermUb tp σ :
    thread_stuck tp σ →
    tp_termination tp σ TermUb
  | tp_termination_TermRet v tp σ :
    tp_termination (Val v :: tp) σ (TermRet v).

Definition tr_terminal (tx : Terminal val) (tr : trace voidE (Outcome val)) : bool :=
  match tx, tr with
  | TermUb, TRet (inl (_, inr UbCrash)) => true
  | TermRet r, TRet (inl (_, inl (inl r'))) => bool_decide (r = r')
  | _, _ => false
  end.

(* TODO: Factor this event type into its own definition. *)
Definition trace_invariant σ (tx : Terminal val) (opsem_steps : nat) (tr : ctrace sequential_heaplangE val) :=
  match interp_tr_heaplang σ (Some opsem_steps) tr with
  | Some tr => tr_terminal tx tr
  | None => false
  end.
Arguments trace_invariant _ _ / _ _.

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

Lemma trace_invariant_ret tp σ n v :
  tp_termination tp σ (TermRet v) →
  trace_invariant σ.(heap) (TermRet v) n (CTRet v).
Proof.
  intros Hterm. inversion Hterm. subst.
  by apply bool_decide_pack.
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

Definition ctrace_step_yield (tid : nat) (tr : ctrace sequential_heaplangE val) :=
  CTVis () (subevent _ ELater) () (CTYield tid tr).
Lemma is_ctrace_step_yield tid tid' tp tr t :
  tp !! tid = Some (later.step ;; yield ;; t)%itree →
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

Lemma trace_invariant_yield tid σ n tx tr :
  trace_invariant σ tx n tr →
  trace_invariant σ tx n (CTYield tid tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant/interp_tr_heaplang. rewrite /trace_invariant/interp_tr_heaplang in Hinv.
  rewrite /ctrace_step_yield /=. by destruct (interp_tr_state _ _).
Qed.

Lemma trace_invariant_step_yield tid σ tx n tr :
  trace_invariant σ tx n tr →
  trace_invariant σ tx (S n) (ctrace_step_yield tid tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant/interp_tr_heaplang. rewrite /trace_invariant/interp_tr_heaplang in Hinv.
  rewrite /ctrace_step_yield /=. by destruct (interp_tr_state _ _).
Qed.

Definition ctrace_get σ (tr : ctrace sequential_heaplangE val) :=
  CTVis heaplang_heap (subevent _ EGetState) σ tr.
Definition ctrace_set σ (tr : ctrace sequential_heaplangE val) :=
  CTVis () (subevent _ (ESetState σ)) () tr.
Definition ctrace_demonic (A : Type) `{EqDecision A} `{Inhabited A} (a : A) (tr : ctrace sequential_heaplangE val) :=
  CTVis A (subevent _ (EDemonic A)) a tr.

Definition ctrace_store' l x σ (tr : ctrace sequential_heaplangE val) :=
  ctrace_get σ (ctrace_set (<[l:=x]> σ) tr).
Definition ctrace_store l x σ (tr : ctrace sequential_heaplangE val) :=
  ctrace_store' l (Some x) σ tr.
Definition ctrace_load σ (tr : ctrace sequential_heaplangE val) :=
  ctrace_get σ tr.

Lemma is_ctrace_store' σ l x v tid tp tr k :
  σ !! l = Some (Some v) →
  tp !! tid = Some (ITree.bind (store' l x) k)%itree →
  is_ctrace tr tid (<[tid := k (Some v)]>tp) →
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
  σ !! l = Some (Some v) →
  tp !! tid = Some (ITree.bind (store l x) k)%itree →
  is_ctrace tr tid (<[tid := k (Some v)]>tp) →
  is_ctrace (ctrace_store l x σ tr) tid tp.
Proof.
  intros Hl Htp Htr.
  by eapply is_ctrace_store'.
Qed.
Lemma is_ctrace_load σ l v tid tp tr k :
  σ !! l = Some (Some v) →
  tp !! tid = Some (ITree.bind (load l) k)%itree →
  is_ctrace tr tid (<[tid := k (Some v)]>tp) →
  is_ctrace (ctrace_load σ tr) tid tp.
Proof.
  intros Hl Htp Htr.
  eapply is_ctrace_insert; first done. { rewrite /load. eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  rewrite list_insert_insert Hl /=. by simpl_itree.
Qed.

Definition ctrace_allocN_nondet v n σ l tr : ctrace sequential_heaplangE val :=
  (CTVis heaplang_heap (subevent _ EGetState) σ (CTVis (free_locations n σ) (subevent _ (EDemonic (free_locations n σ))) l (CTVis () (subevent _ (ESetState ((heap.heap_array (`l) (replicate n v)) ∪ σ))) () tr))).
Lemma is_ctrace_allocN_nondet n σ l v tid tp tr k :
  tp !! tid = Some (ITree.bind (allocN_nondet n v) k)%itree →
  is_ctrace tr tid (<[tid := k (`l)]>tp) →
  is_ctrace (ctrace_allocN_nondet v n σ l tr) tid tp.
Proof.
  intros Htp Htr.
  eapply is_ctrace_insert; first done.
  { rewrite /allocN_nondet. eutt_norm/=. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert // insert_length -lookup_lt_is_Some //. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert // !insert_length -lookup_lt_is_Some //. }
  by rewrite !list_insert_insert.
Qed.

Definition ctrace_store'_ub l x σ : ctrace sequential_heaplangE val :=
  ctrace_store' l x σ ctrace_ub.
Definition ctrace_store_ub l x σ :=
  ctrace_store'_ub l (Some x) σ.
Definition ctrace_load_ub σ : ctrace sequential_heaplangE val :=
  ctrace_load σ ctrace_ub.

Lemma is_ctrace_store'_ub σ l x tid tp k :
  σ !! l = Some None ∨ σ !! l = None →
  tp !! tid = Some (ITree.bind (store'_or_ub l x) k)%itree →
  is_ctrace (ctrace_store'_ub l x σ) tid tp.
Proof.
  intros Hl Htp.
  eapply is_ctrace_insert; first done. { rewrite /store'_or_ub/store'. eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  destruct Hl as [Hl|Hl].
  - rewrite list_insert_insert Hl /ub.
    eapply is_ctrace_Vis.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert // insert_length. by apply lookup_lt_is_Some. }
  - rewrite list_insert_insert Hl /ub.
    eapply is_ctrace_Vis.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert // insert_length. by apply lookup_lt_is_Some. }
Qed.
Lemma is_ctrace_store_ub σ l x tid tp k :
  σ !! l = Some None ∨ σ !! l = None →
  tp !! tid = Some (ITree.bind (store_or_ub l x) k)%itree →
  is_ctrace (ctrace_store_ub l x σ) tid tp.
Proof.
  intros Hl Htp.
  eapply is_ctrace_insert; first done. { rewrite /store. eutt_norm. reflexivity. }
  eapply is_ctrace_store'_ub; first done.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
Qed.
Lemma is_ctrace_load_ub σ l tid tp k :
  σ !! l = Some None ∨ σ !! l = None →
  tp !! tid = Some (ITree.bind (load_or_ub l) k)%itree →
  is_ctrace (ctrace_load_ub σ) tid tp.
Proof.
  intros Hl Htp.
  eapply is_ctrace_insert; first done. { rewrite /load_or_ub/load. eutt_norm. reflexivity. }
  eapply is_ctrace_Vis.
  { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  destruct Hl as [Hl|Hl].
  - rewrite list_insert_insert Hl /ub /=.
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
  - rewrite list_insert_insert Hl /ub.
    eapply is_ctrace_ub.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
Qed.

Lemma trace_invariant_demonic σ tx n tr A a `{EqDecision A} `{Inhabited A} :
  trace_invariant σ tx n tr →
  trace_invariant σ tx n (ctrace_demonic A a tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant/interp_tr_heaplang. rewrite /trace_invariant/interp_tr_heaplang in Hinv.
  simpl. destruct (interp_tr_state σ _); repeat case_match; simplify_eq; eauto.
  simpl in H1. simpl in H0. injection H0 as <-. by injection H1 as <-.
Qed.

Lemma trace_invariant_set σ tx n tr σ' :
  trace_invariant σ' tx n tr →
  trace_invariant σ tx n (ctrace_set σ' tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant/interp_tr_heaplang. rewrite /trace_invariant/interp_tr_heaplang in Hinv.
  simpl. by case_match.
Qed.
Lemma trace_invariant_get σ tx n tr :
  trace_invariant σ tx n tr →
  trace_invariant σ tx n (ctrace_get σ tr).
Proof.
  intros Hinv.
  rewrite /trace_invariant/interp_tr_heaplang. rewrite /trace_invariant/interp_tr_heaplang in Hinv.
  simpl. rewrite decide_True //.
Qed.
Lemma trace_invariant_store' l x σ tx n tr :
  trace_invariant (<[l:=x]> σ) tx n tr →
  trace_invariant σ tx n (ctrace_store' l x σ tr).
Proof.
  intros Hinv. apply trace_invariant_get. by apply trace_invariant_set.
Qed.
Lemma trace_invariant_store l x σ tx n tr :
  trace_invariant (<[l:=Some x]> σ) tx n tr →
  trace_invariant σ tx n (ctrace_store l x σ tr).
Proof.
  intros Hinv. by apply trace_invariant_store'.
Qed.
Lemma trace_invariant_load σ tx n tr :
  trace_invariant σ tx n tr →
  trace_invariant σ tx n (ctrace_load σ tr).
Proof. apply trace_invariant_get. Qed.

Lemma trace_invariant_allocN_nondet v n' σ l tx n tr :
  trace_invariant (heap.heap_array (`l) (replicate n' v) ∪ σ) tx n tr →
  trace_invariant σ tx n (ctrace_allocN_nondet v n' σ l tr).
Proof.
    intros Hinv.
    apply trace_invariant_get.
    apply trace_invariant_demonic.
    by apply trace_invariant_set.
Qed.

Lemma stuck_ub tp σ :
  tp_termination tp σ TermUb →
  ∃ tid tr, trace_invariant σ.(heap) TermUb 0 tr ∧ is_ctrace tr tid (compile_tp tp).
Proof.
  intros Hterm.
  assert (Hterm' := Hterm).
  apply tp_termination_ub in Hterm' as (tid&e&Htp&(K&e'&->&Hbasic&Hstuck)%stuck_basic).
  exists tid.
  destruct Hbasic as [x|f x e0|v1 v2 | | | | | | | | | | | | | | | | | ].
  - exists ctrace_ub.
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
    rewrite /compile_expr. is_ctrace_norm/=.
    eapply is_ctrace_ub.
    rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - eapply stuck_false in Hstuck as [].
    eapply Ectx_step with (K := []); eauto.
    by constructor.
  - exists ctrace_ub.
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
    destruct (val_to_RecV v1) as [[[f x] e]|] eqn:Heq.
    * destruct v1; try discriminate.
      eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
    rewrite /compile_expr. is_ctrace_norm/=.
    apply UnOp_stuck in Hstuck as ->.
    is_ctrace_norm/=. eapply is_ctrace_ub.
    rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
    rewrite /compile_expr. is_ctrace_norm/=.
    apply BinOp_stuck in Hstuck as ->.
    is_ctrace_norm/=. eapply is_ctrace_ub.
    rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
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
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
    destruct (val_to_pair v) as [[x y]|] eqn:Heq.
    * destruct v; try discriminate.
      eapply stuck_false in Hstuck as [].
      eapply Ectx_step with (K := []); eauto.
      by constructor.
    * rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
  - exists ctrace_ub.
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
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
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
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
    split; first done.
    eapply is_ctrace_insert.
    { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
    { rewrite /compile_expr_yield compile_expr_bind' //. }
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
      + exists (ctrace_store'_ub l None σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_store'_ub; first by left.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_store'_ub l None σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_store'_ub; first by right.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first by done.
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind' //. }
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
      + exists (ctrace_load_ub σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_load_ub; first by left.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_load_ub σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_load_ub; first by right.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first split.
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind' //. }
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
      + exists (ctrace_store_ub l v2 σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_store_ub; first by left.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_store_ub l v2 σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_store_ub; first by right.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first done.
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind' //. }
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
      + exists (ctrace_store_ub l v2 σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_store_ub; first by left.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_store_ub l v2 σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_store_ub; first by right.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first done.
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind' //. }
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
        ++ exists (ctrace_load σ.(heap) ctrace_ub).
           split.
           { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
           eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind' //. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
           rewrite /load_or_ub. is_ctrace_norm/=.
           eapply is_ctrace_load; first done.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
           is_ctrace_norm/=. rewrite assert_False // /ub.
           eapply is_ctrace_ub.
           rewrite list_lookup_insert // insert_length compile_tp_len -lookup_lt_is_Some //.
      + exists (ctrace_load_ub σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_load_ub; first by left.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists (ctrace_load_ub σ.(heap)).
        split.
        { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq /=. is_ctrace_norm/=.
        eapply is_ctrace_load_ub; first by right.
        { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
    * exists ctrace_ub.
      split; first done.
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind' //. }
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
           +++ exists (ctrace_load σ.(heap) ctrace_ub).
               split.
               { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
               eapply is_ctrace_insert.
               { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
               { rewrite /compile_expr_yield compile_expr_bind' //. }
               rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
               rewrite /load_or_ub. is_ctrace_norm/=.
               eapply is_ctrace_load; first done.
               { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
               is_ctrace_norm/=. rewrite Heq''.
               eapply is_ctrace_ub.
               rewrite list_lookup_insert // insert_length compile_tp_len -lookup_lt_is_Some //.
        ++ exists (ctrace_load_ub σ.(heap)).
           split.
           { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
           eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind' //. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
           eapply is_ctrace_load_ub; first by left.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
        ++ exists (ctrace_load_ub σ.(heap)).
           split.
           { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //. }
           eapply is_ctrace_insert.
           { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
           { rewrite /compile_expr_yield compile_expr_bind' //. }
           rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
           eapply is_ctrace_load_ub; first by right.
           { rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //. }
      + exists ctrace_ub.
        split; first done.
        eapply is_ctrace_insert.
        { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
        { rewrite /compile_expr_yield compile_expr_bind' //. }
        rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq Heq' /=. is_ctrace_norm/=.
        eapply is_ctrace_ub.
        rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
    * exists ctrace_ub.
      split; first done.
      eapply is_ctrace_insert.
      { rewrite /compile_tp list_lookup_fmap enumerate_lookup' Htp //. }
      { rewrite /compile_expr_yield compile_expr_bind' //. }
      rewrite /compile_expr. is_ctrace_norm/=. rewrite Heq' /=. is_ctrace_norm/=.
      eapply is_ctrace_ub.
      rewrite list_lookup_insert // compile_tp_len -lookup_lt_is_Some //.
Qed.

Program Definition to_free_location n v σ ρs l efs (Hbase : base_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ ρs (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) efs) : free_locations (Z.to_nat n) σ.(heap) :=
  exist _ l _.
Next Obligation.
  intros. simpl. apply bool_decide_pack. inversion Hbase.
  intros i Hlower Hupper. apply H5; lia.
Qed.
Lemma AllocN_free_locations n v σ ρs l efs :
  base_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ ρs (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) efs →
  ∃ (l' : free_locations (Z.to_nat n) σ.(heap)), `l' = l.
Proof. intros Hbase. by exists (to_free_location n v σ ρs l efs Hbase). Qed.

Lemma heap_array_heap_lang l n v :
  heap_array l (replicate n v) = heap.heap_array l (replicate n v).
Proof.
  revert l. induction n; eauto. intros l. simpl. f_equiv. apply IHn.
Qed.
Lemma state_init_heap_heap_array l n v σ :
  (state_init_heap l n v σ).(heap) = heap.heap_array l (replicate (Z.to_nat n) v) ∪ σ.(heap).
Proof.
  rewrite /state_init_heap /=. f_equiv. rewrite heap_array_heap_lang //.
Qed.

Lemma step_in_thread e1 σ1 κs e2 σ2 efs tr tid tid' tp (k : val → itree heaplangE val) tx n :
  base_step e1 σ1 κs e2 σ2 efs →
  is_ctrace tr tid' (<[tid:=(v ← compile_expr_yield e2 ; k v)%itree]>tp
                    ++ compile_tp' efs) →
  trace_invariant σ2.(heap) tx n tr →
  tp !! tid = Some (v ← compile_expr_yield e1 ; k v)%itree →
  ∃ tr', trace_invariant σ1.(heap) tx (S n) tr' ∧ is_ctrace tr' tid tp.
Proof.
  intros Hbase Htr Hinv Htp.
  inversion Hbase; subst; simpl in Htr; rewrite ?app_nil_r in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (RecV f x e)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (PairV v1 v2)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (InjLV v)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    apply is_ctrace_step_yield with (t := k (InjRV v)).
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - pose (e' := subst' x v2 (subst' f (RecV f x e0) e0)).
    exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    destruct (to_val e') as [v|] eqn:Hval.
    * eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield /= base_Beta /= /yield_if_not_val.
        rewrite /e' in Hval. rewrite Hval.
        eutt_norm/=. reflexivity. }
      rewrite /e' in Hval. apply of_to_val in Hval as Heq.
      rewrite -Heq in Htr. rewrite -Heq. rewrite /compile_expr. is_ctrace_norm/=. simpl_itree in Htr.
      apply is_ctrace_step_yield with (t := (k v)%itree).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      by rewrite list_insert_insert.
    * eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield /= base_Beta /= /yield_if_not_val.
        rewrite /e' in Hval. rewrite Hval. eutt_norm/=. reflexivity. }
      rewrite /e' in Hval. rewrite /compile_expr_yield /yield_if_not_val in Htr.
      rewrite Hval in Htr.
      rewrite bind_bind in Htr. setoid_rewrite bind_bind in Htr. setoid_rewrite bind_ret_l in Htr.
      apply is_ctrace_step_yield with (t := (v ← compile_expr e'; yield ;; k v)%itree).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert //.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (later.step ;; yield ;; k v')%itree); first done.
    { rewrite /compile_expr_yield base_UnOp //. eutt_norm/=. rewrite /step_ret. by eutt_norm/=. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (later.step ;; yield ;; k v')%itree); first done.
    { rewrite /compile_expr_yield base_BinOp //. eutt_norm/=. rewrite /step_ret. by eutt_norm/=. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    destruct (to_val e2) eqn:Hval.
    * apply of_to_val in Hval as <-.
      eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield/compile_expr/=. eutt_norm/=. reflexivity. }
      apply is_ctrace_step_yield with (t := k v).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
    * eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
        rewrite /yield_if_not_val Hval /=. reflexivity. }
      rewrite /compile_expr_yield/yield_if_not_val Hval in Htr. simpl_itree in Htr.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    destruct (to_val e2) eqn:Hval.
    * apply of_to_val in Hval as <-.
      eapply is_ctrace_insert; first done.
      { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. reflexivity. }
      apply is_ctrace_step_yield with (t := k v).
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
    * eapply is_ctrace_insert; first done.
      { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
        rewrite /yield_if_not_val Hval /=. reflexivity. }
      rewrite /compile_expr_yield/yield_if_not_val Hval in Htr. simpl_itree in Htr.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (later.step ;; yield ;; k v1)%itree); first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
    eapply is_ctrace_insert with (t' := (later.step ;; yield ;; k v2)%itree); first done.
    { rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret. eutt_norm/=.
      reflexivity. }
    eapply is_ctrace_step_yield. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    by rewrite list_insert_insert.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. reflexivity. }
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    rewrite /compile_expr_yield bind_bind in Htr.
    setoid_rewrite bind_bind in Htr. setoid_rewrite bind_ret_l in Htr.
    by rewrite interp_recursive_call.
  - exists (ctrace_step_yield tid' tr). repeat split.
    { by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
      rewrite /yield_if_not_val /=. reflexivity. }
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite /compile_expr_yield bind_bind in Htr.
    setoid_rewrite bind_bind in Htr. setoid_rewrite bind_ret_l in Htr.
    by rewrite list_insert_insert interp_recursive_call.
  - destruct (AllocN_free_locations _ _ _ _ _ _ Hbase) as [ll <-].
    exists (ctrace_allocN_nondet v (Z.to_nat n0) σ1.(heap) ll (ctrace_step_yield tid' tr)).
    split.
    * apply trace_invariant_allocN_nondet. apply trace_invariant_step_yield.
      rewrite -state_init_heap_heap_array //.
    * eapply is_ctrace_insert; first done.
      { simpl. rewrite /compile_expr_yield/compile_expr. simpl. eutt_norm/=.
        rewrite /step_ret assert_True; last done. eutt_norm/=. reflexivity. }
      eapply is_ctrace_allocN_nondet.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by rewrite /compile_expr_yield compile_expr_val !bind_ret_l in Htr.
  - exists (ctrace_store' l None σ1.(heap) (ctrace_step_yield tid' tr)). repeat split.
    { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //.
      by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret/store'_or_ub.
      eutt_norm/=. reflexivity. }
    eapply is_ctrace_store'; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    is_ctrace_norm/=.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert // insert_length. by apply lookup_lt_is_Some. }
    rewrite !list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_load σ2.(heap) (ctrace_step_yield tid' tr)). repeat split.
    { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //.
      by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /step_ret /load_or_ub.
      eutt_norm/=. reflexivity. }
    eapply is_ctrace_load; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite list_insert_insert.
    is_ctrace_norm/=.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_store l w σ1.(heap) (ctrace_step_yield tid' tr)). repeat split.
    { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //.
      by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
      rewrite /step_ret /store_or_ub/store'_or_ub. eutt_norm/=. reflexivity. }
    eapply is_ctrace_store; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite !list_insert_insert.
    is_ctrace_norm/=.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (ctrace_store l v2 σ1.(heap) (ctrace_step_yield tid' tr)). repeat split.
    { rewrite /trace_invariant/interp_tr_heaplang /= decide_True //.
      by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=.
      rewrite /step_ret /store_or_ub/store'_or_ub. eutt_norm/=. reflexivity. }
    eapply is_ctrace_store; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite !list_insert_insert.
    is_ctrace_norm/=.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - destruct (decide (vl = v1)) as [->|Hneq].
    * rewrite bool_decide_eq_true_2 // in Hinv.
      rewrite bool_decide_eq_true_2 // in Htr.
      exists (ctrace_load σ1.(heap) (ctrace_store l v2 σ1.(heap) (ctrace_step_yield tid' tr))). repeat split.
      { rewrite /trace_invariant/interp_tr_heaplang /= !decide_True //.
        by apply trace_invariant_step_yield. }
      eapply is_ctrace_insert; first done.
      { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /load_or_ub.
        eutt_norm/=. reflexivity. }
      eapply is_ctrace_load; first done.
      { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
      is_ctrace_norm/=.
      rewrite !list_insert_insert assert_True //. is_ctrace_norm/=.
      rewrite decide_True //. is_ctrace_norm/=. rewrite /store_or_ub/store'_or_ub. is_ctrace_norm/=.
      eapply is_ctrace_store; first done.
      { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
      rewrite !list_insert_insert. rewrite /step_ret. is_ctrace_norm/=.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
    * rewrite bool_decide_eq_false_2 // in Hinv.
      rewrite bool_decide_eq_false_2 // in Htr.
      exists (ctrace_load σ1.(heap) (ctrace_step_yield tid' tr)). repeat split.
      { rewrite /trace_invariant/interp_tr_heaplang /= !decide_True //.
        by apply trace_invariant_step_yield. }
      eapply is_ctrace_insert; first done.
      { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. reflexivity. }
      rewrite /load_or_ub. is_ctrace_norm/=.
      eapply is_ctrace_load; first done.
      { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
      simpl. rewrite list_insert_insert. is_ctrace_norm/=.
      rewrite assert_True // decide_False // /step_ret. is_ctrace_norm/=.
      eapply is_ctrace_step_yield.
      { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
      rewrite list_insert_insert.
      by simpl_itree in Htr.
  - exists (ctrace_load σ1.(heap) (ctrace_store l (LitV (LitInt (i1 + i2))) σ1.(heap) (ctrace_step_yield tid' tr))). repeat split.
    { rewrite /trace_invariant/interp_tr_heaplang /= !decide_True //.
      by apply trace_invariant_step_yield. }
    eapply is_ctrace_insert; first done.
    { simpl. rewrite /compile_expr_yield/compile_expr. eutt_norm/=. rewrite /load_or_ub.
      eutt_norm/=. reflexivity. }
    eapply is_ctrace_load; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite list_insert_insert /step_ret. is_ctrace_norm/=.
    rewrite /store_or_ub/store'_or_ub. is_ctrace_norm/=.
    eapply is_ctrace_store; first done.
    { rewrite list_lookup_insert // -lookup_lt_is_Some //. }
    rewrite list_insert_insert.
    is_ctrace_norm/=.
    eapply is_ctrace_step_yield.
    { rewrite list_lookup_insert //. by apply lookup_lt_is_Some. }
    rewrite list_insert_insert.
    by simpl_itree in Htr.
  - exists (CTFork (compile_expr_kill e) (ctrace_step_yield tid' tr)).
    repeat split.
    { by apply trace_invariant_step_yield. }
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
Qed.

Lemma lt_gt n m :
  n < m ↔ m > n.
Proof. lia. Qed.

(* TODO: Idea: make κ = [] *)
Lemma simulation n tp σ tp' σ' κ tx :
  language.nsteps n (tp, σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  length tp > 0 →
  ∃ tid tr,
    trace_invariant σ.(heap) tx n tr ∧
    is_ctrace (R := val) tr tid (compile_tp tp).
Proof.
  revert tp σ tp' σ' κ. induction n as [|n IH]; intros tp σ tp' σ' κ Hstep Hterm Hne.
  { destruct tx as [r|].
    - assert (Hterm' := Hterm).
      apply is_ctrace_ret  in Hterm as Htr.
      apply trace_invariant_ret with (σ := σ') (n := 0) in Hterm' as Htinv.
      exists 0, (CTRet r). inversion Hstep. subst. by split.
    - inversion Hstep; subst. destruct u.
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
      apply step_in_thread with (tp := ((v ← compile_expr_yield e1 ; Ret v)%itree :: compile_tp' tpb)) (tid := 0) (tid' := tid) (k := λ v, Ret v) (tr := tr) (tx := tx) (n := n) in Hbase as [tr' [Hinv' Htr']].
      + exists 0, tr'. rewrite compile_tp_cons //.
      + simpl. rewrite compile_tp_cons compile_tp'_app // in Htr.
      + done.
      + done.
    * apply step_in_thread with (tp := (compile_tp tpa ++ (compile_expr_kill e1)%itree :: compile_tp' tpb)) (tid := length (compile_tp tpa)) (tid' := tid) (k := λ v, kill_thread) (tr := tr) (tx := tx) (n := n) in Hbase as [tr' [Hinv' Htr']].
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
      apply step_in_thread with (tp := ((v ← compile_expr_yield e1; w ← compile_expr (fill K (Val v)); yield ;; Ret w)%itree :: compile_tp' tpb)) (tid := 0) (tid' := tid) (k := λ v, (w ← compile_expr (fill K (Val v)); yield ;; Ret w)%itree) (tr := tr) (tx := tx) (n := n) in Hbase as [tr' [Hinv' Htr']].
      + exists 0, tr'.
        split; first done.
        rewrite compile_tp_cons /= /compile_expr_yield compile_expr_bind //.
        ++ setoid_rewrite fill_not_val; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           rewrite /compile_expr_yield in Htr'. simpl_itree. simpl_itree in Htr'. done.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + simpl.
        rewrite compile_tp_cons /= /compile_expr_yield compile_expr_bind // in Htr.
        ++ setoid_rewrite fill_not_val in Htr; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           do 2 setoid_rewrite bind_bind in Htr.
           simpl_itree in Htr. simpl_itree.
           by rewrite compile_tp'_app in Htr.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + done.
      + done.
    * rewrite compile_tp_app // in Htr.
      rewrite compile_tp_app //.
      apply step_in_thread with (tp := (compile_tp tpa ++ (v ← compile_expr_yield e1; compile_expr_kill (fill K (Val v)))%itree :: compile_tp' tpb)) (tid := length tpa) (tid' := tid) (k := λ v, (compile_expr_kill (fill K (Val v)))%itree) (tr := tr) (tx := tx) (n := n) in Hbase as [tr' [Hinv' Htr']].
      + exists (length tpa), tr'.
        split; first done.
        rewrite /= /compile_expr_kill/compile_expr_yield compile_expr_bind.
        ++ setoid_rewrite fill_not_val; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           rewrite /compile_expr_kill/compile_expr_yield in Htr'.
           setoid_rewrite fill_not_val in Htr'; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           simpl_itree in Htr'. simpl_itree. done.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + replace (length tpa) with (length (compile_tp tpa) + 0) by rewrite compile_tp_len //.
        rewrite insert_app_r /= -app_assoc /=.
        rewrite compile_tp'_cons compile_tp'_app /= /compile_expr_kill/compile_expr_yield compile_expr_bind // in Htr.
        ++ simpl_itree in Htr. simpl_itree.
           setoid_rewrite fill_not_val; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           setoid_rewrite fill_not_val in Htr; last first. { rewrite -lt_gt -Nat.neq_0_lt_0 //. }
           done.
        ++ rewrite -lt_gt -Nat.neq_0_lt_0 //.
      + done.
      + apply list_lookup_middle. rewrite compile_tp_len //.
Qed.

Lemma execution_from_opsem_trace n e σ tp' σ' κ tx :
  language.nsteps n ([e], σ) κ (tp', σ') →
  tp_termination tp' σ' tx →
  ∃ te x,
    heaplang_eval e σ.(heap) (Some n) te ∧
    te ≈ Ret x ∧
    ∃ σ',
      match tx with
      | TermUb => x = inl (σ', inr UbCrash)
      | TermRet r => x = inl (σ', inl (inl r))
      end.
Proof.
  intros Hsteps Hterm.
  apply simulation with (tx := tx) in Hsteps as (tid&tr&Hinv&Htr); eauto.
  destruct tid; last destruct Htr as [? [[=] _]].
  rewrite /trace_invariant in Hinv.
  destruct (interp_tr_heaplang σ.(heap) (Some n) tr) as [tr'|] eqn:Heq; last contradiction.
  rewrite /compile_tp in Htr. simpl_itree in Htr.
  apply heaplang_trace with (tr' := tr') (σ := σ.(heap)) (n := Some n) in Htr as (te&Hrel&Htr); eauto.
  exists te.
  destruct tx.
  - rewrite /tr_terminal in Hinv.
    destruct tr' as [x | | | ]; try contradiction.
    exists x.
    split; first done.
    split; first by apply is_trace_Ret_inv in Htr.
    destruct x; last done. destruct p as [σ_ ?]. exists σ_.
    case_match; last done. case_match; last done.
    by apply bool_decide_unpack in Hinv as ->.
  - destruct u.
    destruct tr' as [[[σ_ [[r|]|]]|] | | | ]; try contradiction.
    apply is_trace_Ret_inv in Htr.
    eexists. split; last split; eauto. exists σ_. by destruct u.
Qed.

From iris.program_logic Require Import adequacy.

Lemma partially_adequate_opsem_adequate e σ φ :
  partially_adequate e σ.(heap) φ →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Had.
  apply adequate_alt.
  setoid_rewrite erased_steps_nsteps.
  intros t2 σ2 (n&κs&Hsteps).
  split.
  - intros v2 t2' Heq.
    opose proof (execution_from_opsem_trace _ _ _ _ _ _ _ _ _) as (te&Heval&Hφ); eauto.
    { rewrite Heq. apply tp_termination_TermRet. }
    destruct Hφ as (σ'&Heutt&σ_&->).
    odestruct (Had _ _ _) as (x&Heutt'&Hφ); first done.
    rewrite Heutt in Heutt'. by apply eutt_inv_Ret in Heutt' as <-.
  - intros e2 _ [i Hidx]%elem_of_list_lookup.
    destruct (decide (not_stuck e2 σ2)) as [?| Hstuck%not_not_stuck]; [done|].
    exfalso.
    opose proof (execution_from_opsem_trace _ _ _ _ _ _ _ _ _) as (te&x&Heval&Heutt&σ'&Heq); eauto.
    { apply tp_termination_TermUb. econstructor. by eexists. }
    odestruct (Had _ _ _) as (x'&Heutt'&Hφ); first done.
    rewrite Heutt in Heutt'. apply eutt_inv_Ret in Heutt' as <-.
    rewrite Heq // in Hφ.
Qed.

(* TODO: deduplicate these proofs *)
Theorem wp_later_opsem_adequate Σ `{!invGpreS Σ} `{!heaplangHGpreS Σ} e σ φ:
  (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Later; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp.
  eapply wp_partial_soundness in Hwp.
  by apply partially_adequate_opsem_adequate in Hwp.
Qed.

(* TODO: prove this via weakening *)
Theorem wp_total_opsem_adequate Σ `{!invGpreS Σ} `{!heaplangHGpreS Σ} e σ φ:
  (∀ `{!invGS Σ} `{!heaplangHGS Σ}, ⊢ WP e @ Identity; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp.
  eapply wp_later_opsem_adequate; eauto.
  iIntros (? ?). iDestruct Hwp as "Hwp".
  by iApply wp_later_weaken.
Qed.
