From ITree Require Import ITree Eqit.
From Paco Require Import paco.
From Paco Require Import paco2.
From stdpp Require Import list.
From iris.itree.threadpool Require Import handler interleaving.
From iris.itree Require Import axioms itree trace.
Import Coq.Logic.ClassicalChoice.

Section scheduler.
  Definition scheduler {E R} : itree (threadpoolE +' E) R → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) :=
    cofix _scheduler t tp :=
        match observe t with
        | RetF r  => Ret (inl r)
        | TauF t' => Tau (_scheduler t' tp)
        | @VisF _ _ _ A (inl1 e) k =>
          (match e with
          | EFork => λ k, Tau (_scheduler (k CurrentThread) (tp ++ [k NewThread]))
          | EYield => λ k, Tau (_scheduler (k ()) tp)
          | EKillThread => λ k,
              match tp with
              | [] => Ret (inr LastThreadKilled)
              | t' :: tp' => Tau (_scheduler t' tp')
              end
          end : (A → _) → _) k
        | VisF (inr1 e) k => Vis e (λ a, _scheduler (k a) tp)
        end.
  Notation scheduler_ t tp :=
      match observe t with
      | RetF r  => Ret (inl r)
      | TauF t' => Tau (scheduler t' tp)
      | @VisF _ _ _ A (inl1 e) k =>
        (match e with
        | EFork => λ k, Tau (scheduler (k CurrentThread) (tp ++ [k NewThread]))
        | EYield => λ k, Tau (scheduler (k ()) tp)
        | EKillThread => λ k,
            match tp with
            | [] => Ret (inr LastThreadKilled)
            | t' :: tp' => Tau (scheduler t' tp')
            end
        end : (A → _) → _) k
      | VisF (inr1 e) k => Vis e (λ a, scheduler (k a) tp)
      end.

  Lemma unfold_scheduler {E R} (t : itree (threadpoolE +' E) R) tp :
    scheduler t tp = scheduler_ t tp.
  Proof.
    apply bisimulation_is_eq. apply observing_sub_eqit; constructor; reflexivity.
  Qed.

  Lemma list_delete_insert {A} idx x (xs : list A) :
    delete idx (<[idx := x]> xs) = delete idx xs.
  Proof.
    induction idx as [|idx IH] in xs |- *.
    - destruct xs as [|x' xs']; done.
    - destruct xs as [|x' xs'].
      * done.
      * simpl. f_equiv. apply IH.
  Qed.

  Lemma list_delete_empty {A} idx (xs : list A) :
    delete idx xs = [] →
    length xs <= 1.
  Proof.
    intros Hemp.
    destruct (decide (idx < length xs)).
    - replace (length xs) with (length (delete idx xs) + 1).
      * rewrite Hemp //.
      * rewrite length_delete. { lia. }
        by apply lookup_lt_is_Some_2.
    - rewrite delete_take_drop take_ge in Hemp.
      * apply app_nil in Hemp as [-> _]. simpl. lia.
      * lia.
  Qed.

  Lemma schedule_exists {E R} (t : itree (threadpoolE +' E) R) tid tp :
    tp !! tid = Some t →
    interleaves tid tp (scheduler t (delete tid tp)).
  Proof.
    intros Hidx.
    remember (scheduler t (delete tid tp)) as t'.
    revert t tp tid Hidx t' Heqt'. pcofix CIH. intros t tp tid Hidx t' ->.
    pfold. exists t. split; first done.
    rewrite unfold_scheduler.
    destruct (observe t) as [r'|t'|A e k].
    - constructor.
    - constructor. right. apply (CIH t').
      apply lookup_lt_Some in Hidx.
      rewrite list_lookup_insert //.
      rewrite list_delete_insert //.
    - destruct e as [e|e]; first destruct e.
      * constructor. right. apply (CIH (k CurrentThread)).
        + simpl. apply lookup_lt_Some in Hidx.
          rewrite lookup_app_l; last rewrite insert_length //.
          rewrite list_lookup_insert; eauto.
        + rewrite delete_app_l; last rewrite insert_length // -lookup_lt_is_Some //.
          rewrite list_delete_insert //.
      * apply Yield with (new_current_tid := tid). right.
        apply (CIH (k ())).
        + simpl. apply lookup_lt_Some in Hidx.
          rewrite list_lookup_insert; eauto.
        + rewrite /= list_delete_insert //.
      * apply singleton_or_more in Hidx as [[-> ->]|[Hlen Hidx]].
        + constructor.
        + destruct (delete tid tp) as [|t' tp'] eqn:Heq.
          ++ apply list_delete_empty in Heq. lia.
          ++ apply KillThread with (new_current_tid := 0).
             right. apply CIH with (t := t'); rewrite Heq //.
      * constructor. intros a. right.
        apply CIH with (t := k a).
        + rewrite list_lookup_insert //. by apply lookup_lt_is_Some.
        + by rewrite list_delete_insert.
  Qed.
End scheduler.

Inductive ctrace (E : Type → Type) (R : Type) :=
  | CTRet (r : R)
  | CTVis {A : Type} (e : E A) (a : A) (tr' : ctrace E R)
  | CTVisEmpty {A : Type} (e : E A)
  | CTYield (new_tid : nat) (tr' : ctrace E R)
  | CTKillThread (new_tid : nat) (tr' : ctrace E R)
  | CTKillLastThread
  | CTFork (t : itree (threadpoolE +' E) R) (tr' : ctrace E R)
  | CTCut.

Arguments CTRet {_ _}.
Arguments CTVis {_ _}.
Arguments CTVisEmpty {_ _}.
Arguments CTYield {_ _}.
Arguments CTKillThread {_ _}.
Arguments CTKillLastThread {_ _}.
Arguments CTFork {_ _}.
Arguments CTCut {_ _}.

Lemma Forall2_singleton A R (x : A) (xs : list A) :
  Forall2 R [x] xs →
  ∃ x', xs !! 0 = Some x' ∧ R x x' ∧ xs = [x'].
Proof.
  intros Hforall. inversion Hforall. subst. inversion H3. subst. eexists. eauto.
Qed.

Section is_ctrace.
  Context {E : Type → Type} {R : Type}.

  Inductive is_ctrace_
    : ctrace E R
    → nat
    → itree' (threadpoolE +' E) R
    → list (itree (threadpoolE +' E) R)
    → Prop :=
  | is_CTRet tid tp r :
    is_ctrace_ (CTRet r) tid (RetF r) tp
  | is_CTVis tr' tid tp A (e : E A) a k :
    is_ctrace_ tr' tid (observe (k a)) (<[tid:=k a]>tp) →
    is_ctrace_ (CTVis A e a tr') tid (VisF (inr1 e) k) tp
  | is_CTVisEmpty tid tp A (f : A → Empty_set) (e : E A) k :
    is_ctrace_ (CTVisEmpty A e) tid (VisF (inr1 e) k) tp
  | is_CTYield tr' tid tp k t' tid' :
    <[tid := k ()]>tp !! tid' = Some t' →
    is_ctrace_ tr' tid' (observe t') (<[tid := k ()]>tp) →
    is_ctrace_ (CTYield tid' tr') tid (VisF (inl1 EYield) k) tp
  | is_CTKillThread tr' tid tp k t' tid' :
    (delete tid tp) !! tid' = Some t' →
    is_ctrace_ tr' tid' (observe t') (delete tid tp) →
    is_ctrace_ (CTKillThread tid' tr') tid (VisF (inl1 EKillThread) k) tp
  | is_CTKillLastThread k t :
    is_ctrace_ CTKillLastThread 0 (VisF (inl1 EKillThread) k) [t]
  | is_CTFork tr' tid tp k k_new' :
    k_new' ≈ k NewThread →
    is_ctrace_ tr' tid (observe (k CurrentThread)) (<[tid := k CurrentThread]>tp ++ [k NewThread]) →
    is_ctrace_ (CTFork k_new' tr') tid (VisF (inl1 EFork) k) tp
  | is_CTCut tid t tp :
    is_ctrace_ CTCut tid t tp
  | ctrace_skip_tau tr t' tid tp :
    is_ctrace_ tr tid (observe t') (<[tid := t']>tp) →
    is_ctrace_ tr tid (TauF t') tp.

  Definition is_ctrace
    : ctrace E R
    → nat
    → list (itree (threadpoolE +' E) R)
    → Prop :=
    λ tr tid tp, ∃ t, tp !! tid = Some t ∧ is_ctrace_ tr tid (observe t) tp.

  Lemma is_ctrace_CTCut tid tp :
    tid < length tp →
    is_ctrace CTCut tid tp.
  Admitted.

  Inductive similar
    : ctrace E R
    → ctrace E R
    → Prop :=
  | similar_CTRet r :
    similar (CTRet r) (CTRet r)
  | similar_CTVis A (e : E A) a tr1 tr2 :
    similar tr1 tr2 →
    similar (CTVis A e a tr1) (CTVis A e a tr2)
  | similar_CTVisEmpty A e :
    similar (CTVisEmpty A e) (CTVisEmpty A e)
  | similar_CTYield tid' tr1 tr2 :
    similar tr1 tr2 →
    similar (CTYield tid' tr1) (CTYield tid' tr2)
  | similar_CTKillThread tid' tr1 tr2 :
    similar tr1 tr2 →
    similar (CTKillThread tid' tr1) (CTKillThread tid' tr2)
  | similar_CTKillLastThread :
    similar CTKillLastThread CTKillLastThread
  | similar_CTFork t1 t2 tr1 tr2 :
    t1 ≈ t2 →
    similar tr1 tr2 →
    similar (CTFork t1 tr1) (CTFork t2 tr2)
  | similar_CTCut :
    similar CTCut CTCut.

  Instance similar_sym :
    Symmetric similar.
  Proof.
    intros tr1 tr2 Hsim. induction Hsim; constructor; eauto. by symmetry.
  Qed.
  Instance similar_refl :
    Reflexive similar.
  Proof.
    intros tr. induction tr; constructor; eauto. by symmetry.
  Qed.

  Lemma is_ctrace__eutt tr1 tr2 tid t1 t2 tp1 tp2 :
    is_ctrace_ tr1 tid (observe t1) tp1 →
    tp1 !! tid = Some t1 →
    tp2 !! tid = Some t2 →
    similar tr1 tr2 →
    Forall2 (eutt (=)) tp1 tp2 →
    t1 ≈ t2 →
    is_ctrace_ tr2 tid (observe t2) tp2.
  Proof.
    intros Htr.
    remember (observe t1) as ot1.
    remember (observe t2) as ot2.
    revert tr2 tp2 t1 t2 ot2 Heqot1 Heqot2.
    induction Htr as [tid tp1 r|tr' tid tp1 A e a k Htr IH|tid tp1 A f e k|tr' tid tp1 k t' tid' Hidx' Htr IH|tr' tid tp1 k t' tid' Hidx' Htr IH|k t'|tr' tid tp1 k k_new' Hsim' Htr IH|tid t' tp1 Htr|tr t' tid tp1 Htr IH]; intros tr2 tp2 t1 t2 ot2 Heqot1 Heqot2 Hidx1 Hidx2 Hsim Htp Heqit.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. rewrite -Heqot2 in Heqit.
      revert t1 t2 tp2 Htp Hidx1 Hidx2 Heqot0 Heqot1 Heqot2. induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH ]; try discriminate.
      * intros. injection Heqot1 as ->. destruct REL. inversion Hsim. constructor.
      * intros. constructor. apply IH with (t1 := t1) (t2 := t2'); eauto.
        + transitivity tp2; first done.
          replace tp2 with (<[tid := t2]>tp2); last rewrite list_insert_id //.
          rewrite list_insert_insert. f_equiv. simplify_obs. by apply eqit_Tau_l.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. rewrite -Heqot2 in Heqit.
      revert t1 t2 tp2 Htp Hidx1 Hidx2 Heqot0 Heqot1 Heqot2. induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH' ]; try discriminate.
      * pclearbot. intros. inversion Hsim. simplify_K. simplify_K. constructor. apply IH with (t1 := k1 a) (t2 := k2 a); try done.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
        + f_equiv; first apply REL. done.
        + apply REL.
      * intros. constructor. apply IH' with (t1 := t1) (t2 := t2'); eauto.
        + transitivity tp2; first done.
          replace tp2 with (<[tid := t2]>tp2); last rewrite list_insert_id //.
          rewrite list_insert_insert. f_equiv. simplify_obs. by apply eqit_Tau_l.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. rewrite -Heqot2 in Heqit.
      revert t1 t2 tp2 Htp Hidx1 Hidx2 Heqot0 Heqot1 Heqot2. induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH' ]; try discriminate.
      * pclearbot. intros. simplify_K. simplify_K. inversion Hsim. simplify_K. by constructor.
      * intros. constructor. apply IH' with (t1 := t1) (t2 := t2'); eauto.
        + transitivity tp2; first done.
          replace tp2 with (<[tid := t2]>tp2); last rewrite list_insert_id //.
          rewrite list_insert_insert. f_equiv. simplify_obs. by apply eqit_Tau_l.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. rewrite -Heqot2 in Heqit.
      revert t1 t2 tp2 Htp Hidx1 Hidx2 Heqot0 Heqot1 Heqot2. induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH' ]; try discriminate.
      * pclearbot. intros. simplify_K. simplify_K.
        assert (Forall2 (eutt eq) (<[tid:=k1 ()]>tp1) (<[tid:=k2 ()]>tp2)) as Htp'.
        { f_equiv; last done. apply REL. }
        apply Forall2_lookup_l with (i := tid') (x := t') in Htp' as [t'' [Hidx Heqit]].
        inversion Hsim. econstructor.
        + done.
        + apply IH with (t1 := t') (t2 := t''); try done. f_equiv; last done. apply REL.
        + done.
      * intros. constructor. apply IH' with (t1 := t1) (t2 := t2'); eauto.
        + transitivity tp2; first done.
          replace tp2 with (<[tid := t2]>tp2); last rewrite list_insert_id //.
          rewrite list_insert_insert. f_equiv. simplify_obs. by apply eqit_Tau_l.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. rewrite -Heqot2 in Heqit.
      revert t1 t2 tp2 Htp Hidx1 Hidx2 Heqot0 Heqot1 Heqot2. induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH' ]; try discriminate.
      * pclearbot. intros. simplify_K. simplify_K.
        assert (Forall2 (eutt eq) (delete tid tp1) (delete tid tp2)) as Htp'.
        { by f_equiv. }
        apply Forall2_lookup_l with (i := tid') (x := t') in Htp' as [t'' [Hidx Heqit]].
        inversion Hsim. econstructor.
        + done.
        + apply IH with (t1 := t') (t2 := t''); try done. f_equiv; last done.
        + done.
      * intros. constructor. apply IH' with (t1 := t1) (t2 := t2'); eauto.
        + transitivity tp2; first done.
          replace tp2 with (<[tid := t2]>tp2); last rewrite list_insert_id //.
          rewrite list_insert_insert. f_equiv. simplify_obs. by apply eqit_Tau_l.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. rewrite -Heqot2 in Heqit.
      revert t1 t2 tp2 Htp Hidx1 Hidx2 Heqot0 Heqot1 Heqot2. induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH ]; try discriminate.
      * intros. apply Forall2_singleton in Htp as (t2'&Hidx&Heqit'&->).
        inversion Hsim. simplify_K. simplify_K. constructor.
      * intros. constructor. apply IH with (t1 := t1) (t2 := t2'); eauto.
        + transitivity tp2; first done.
          replace tp2 with (<[0 := t2]>tp2); last rewrite list_insert_id //.
          rewrite list_insert_insert. f_equiv. simplify_obs. by apply eqit_Tau_l.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. rewrite -Heqot2 in Heqit.
      revert t1 t2 tp2 Htp Hidx1 Hidx2 Heqot0 Heqot1 Heqot2. induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH' ]; try discriminate.
      * pclearbot. intros. inversion Hsim. simplify_K. simplify_K. apply is_CTFork.
        { transitivity k_new'; first done.
          transitivity (k1 NewThread); first done.
          apply REL.
        }
        eapply IH; eauto.
        + rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
          apply list_lookup_insert. by apply lookup_lt_is_Some_1.
        + rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
          apply list_lookup_insert. by apply lookup_lt_is_Some_1.
        + f_equiv.
          ++ f_equiv; first apply REL. done.
          ++ constructor; eauto. apply REL.
        + apply REL.
      * intros. constructor. apply IH' with (t1 := t1) (t2 := t2'); eauto.
        + transitivity tp2; first done.
          replace tp2 with (<[tid := t2]>tp2); last by apply list_insert_id.
          rewrite list_insert_insert. f_equiv. simplify_obs. by apply eqit_Tau_l.
        + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - inversion Hsim. constructor.
    - apply IH with (t1 := t') (t2 := t2); eauto.
      + apply list_lookup_insert. by apply lookup_lt_is_Some_1.
      + replace tp2 with (<[tid := t2]>tp2); last by apply list_insert_id.
        f_equiv; last done. transitivity t1; last done. simplify_obs. by apply eqit_Tau_r.
      + transitivity t1; last done. simplify_obs. by apply eqit_Tau_r.
  Qed.

  Lemma is_ctrace_eutt' :
    Proper (similar ==> (pointwise_relation nat (Forall2 (eutt (=)) ==> (→))))
           is_ctrace.
  Proof.
    intros tr1 tr2 Hsim tid tp1 tp2 Heutt.
    intros [t [Hidx Htr]].
    assert (Hidx' := Hidx).
    apply Forall2_lookup_l with (P := eutt (=)) (k := tp2) in Hidx as [t' [Hidx Heutt']]; last done.
    eexists. split; first done. by eapply is_ctrace__eutt.
  Qed.
  Global Instance is_ctrace_eutt b1 b2 tr n :
    Proper (Forall2 (eqit (=) b1 b2) ==> (↔)) (is_ctrace tr n).
  Proof.
    intros tp1 tp2 Htp.
    apply Forall2_impl with (Q := eqit (=) true true) in Htp; last first.
    { intros t1 t2 Heqit. admit. }
    split.
    - intros Hctr. eapply is_ctrace_eutt'.
      * reflexivity.
      * apply Htp.
      * done.
    - intros Hctr. eapply is_ctrace_eutt'.
      * reflexivity.
      * symmetry. apply Htp.
      * done.
  Admitted.

  Lemma is_ctrace_insert tr tp n t t' :
    tp !! n = Some t →
    t ≈ t' →
    is_ctrace tr n (<[n := t']>tp) →
    is_ctrace tr n tp.
  Admitted.

  Lemma is_ctrace_yield tid tid' (tp : list (itree (threadpoolE +' E) R)) tr t :
    tp !! tid = Some (ITree.bind (trigger EYield) (λ _, t))%itree →
    is_ctrace tr tid' (<[tid := t]>tp) →
    is_ctrace (CTYield tid' tr) tid tp.
  Proof.
    intros Htp Htr.
    eapply is_ctrace_insert; first done; first rewrite bind_trigger //.
    eexists. split. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1. }
    econstructor.
  Admitted.

  Inductive is_postfix
    : ctrace E R
    → ctrace E R
    → Prop :=
  | is_postfix_same tr :
    is_postfix tr tr
  | is_postfix_CTVis tr tr' A e a :
    is_postfix tr tr' →
    is_postfix tr (CTVis A e a tr')
  | is_postfix_CTYield tr tr' new_tid :
    is_postfix tr tr' →
    is_postfix tr (CTYield new_tid tr')
  | is_postfix_CTKillThread tr tr' new_tid :
    is_postfix tr tr' →
    is_postfix tr (CTKillThread new_tid tr')
  | is_postfix_CTFork tr tr' t :
    is_postfix tr tr' →
    is_postfix tr (CTFork t tr').

  Global Instance is_postfix_trans :
    Transitive is_postfix.
  Admitted.
End is_ctrace.

Fixpoint sequencify {E R} (tr : ctrace E R) : trace E (R + last_thread_killed) :=
  match tr with
  | CTRet r => TRet (inl r)
  | CTVis A e a tr' => TVis A e a (sequencify tr')
  | CTVisEmpty A e => TVisEmpty A e
  | CTYield new_tid tr' => sequencify tr'
  | CTKillThread new_tid tr' => sequencify tr'
  | CTKillLastThread => TRet (inr LastThreadKilled)
  | CTFork t tr' => sequencify tr'
  | CTCut => TCut
  end.

Section extend_ctrace.
  Context {E : Type → Type} {R : Type}.

  Inductive extends_ctrace_
    : ctrace E R
    → nat
    → itree' (threadpoolE +' E) R
    → list (itree (threadpoolE +' E) R)
    → itree' E (R + last_thread_killed)
    → Prop :=
  | extends_CTRet tid tp r :
    extends_ctrace_ (CTRet r) tid (RetF r) tp (RetF (inl r))
  | extends_CTVis tr' tid tp A (e : E A) a k k_int :
    (∀ a, interleaves tid (<[tid:=k a]>tp) (k_int a)) →
    extends_ctrace_ tr' tid (observe (k a)) (<[tid:=k a]>tp) (observe (k_int a)) →
    extends_ctrace_ (CTVis A e a tr') tid (VisF (inr1 e) k) tp (VisF e k_int)
  | extends_CTVisEmpty tid tp A (f : A → Empty_set) (e : E A) k k_int :
    extends_ctrace_ (CTVisEmpty A e) tid (VisF (inr1 e) k) tp (VisF e k_int)
  | extends_Tau tr tid t' tp t'_int :
    extends_ctrace_ tr tid (observe t') (<[tid:=t']>tp) (observe t'_int) →
    extends_ctrace_ tr tid (TauF t') tp (TauF t'_int)
  | extends_CTYield tr' tid tp k t' tid' t'_int :
    <[tid := k ()]>tp !! tid' = Some t' →
    extends_ctrace_ tr' tid' (observe t') (<[tid := k ()]>tp) (observe t'_int) →
    extends_ctrace_ (CTYield tid' tr') tid (VisF (inl1 EYield) k) tp (TauF t'_int)
  | extends_CTKillThread tr' tid tp k t' tid' t'_int :
    (delete tid tp) !! tid' = Some t' →
    extends_ctrace_ tr' tid' (observe t') (delete tid tp) (observe t'_int) →
    extends_ctrace_ (CTKillThread tid' tr') tid (VisF (inl1 EKillThread) k) tp (TauF t'_int)
  | extends_CTKillLastThread k t :
    extends_ctrace_ CTKillLastThread 0 (VisF (inl1 EKillThread) k) [t] (RetF (inr LastThreadKilled))
  | extends_CTFork tr' tid tp k t_int k_new' :
    k_new' ≈ k NewThread →
    extends_ctrace_ tr' tid (observe (k CurrentThread)) (<[tid := k CurrentThread]>tp ++ [k NewThread]) (observe t_int) →
    extends_ctrace_ (CTFork k_new' tr') tid (VisF (inl1 EFork) k) tp (TauF t_int)
  | extends_CTCut tid t tp t_int :
    interleaves tid tp (go t_int) →
    extends_ctrace_ CTCut tid t tp t_int.

  Definition extends_ctrace
    : ctrace E R
    → nat
    → list (itree (threadpoolE +' E) R)
    → itree E (R + last_thread_killed)
    → Prop :=
    λ tr tid tp t_int, ∃ t, tp !! tid = Some t ∧ extends_ctrace_ tr tid (observe t) tp (observe t_int).

  Hint Resolve interleaves__mono : paco.
  Lemma extends_ctrace_is_interleaving tr tid tp t_int :
    extends_ctrace tr tid tp t_int →
    interleaves tid tp t_int.
  Proof.
    intros [t [Hidx Hext]].
    remember (observe t) as ot.
    remember (observe t_int) as ot_int.
    revert t_int t Hidx Heqot Heqot_int.
    induction Hext as [tid tp r|tr' tid tp A e a k k_int Hint Hext IH|tid tp A f e k k_int|tr' tid t' tp t'_int Hext IH|tr' tid tp k t' tid' t'_int Hidx' Hext IH|tr' tid tp k t' tid' t'_int Hidx' Hext IH|k t'|tr' tid tp k t'_int k_current' Hsim Hext IH|tid t' tp t'_int Hint]; intros t_int t Hidx Heqot Heqot_int.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      constructor.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      constructor. intros a'. left. apply Hint.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      constructor. intros a'. left. apply f in a' as a''. contradiction.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      constructor. left. apply IH with (t := t'); eauto. apply list_lookup_insert.
      by apply lookup_lt_is_Some_1.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      apply Yield with (new_current_tid := tid'). left. apply IH with (t := t'); eauto.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      apply KillThread with (new_current_tid := tid'). left. apply IH with (t := t'); eauto.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      constructor.
    - pfold. rewrite /interleaves_. exists t. split; first done. destruct Heqot, Heqot_int.
      constructor. left. apply IH with (t := k CurrentThread); eauto.
      simpl. rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
      apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - pfold. punfold Hint. rewrite /interleaves_. rewrite /interleaves_ in Hint. simpl in Hint.
      rewrite -Heqot_int //.
  Qed.

  Lemma exists_vis t A e a tid tp tr' k :
    tp !! tid = Some t →
    observe t = VisF (inr1 e) k →
    (∃ k_int, ∀ a', interleaves tid (<[tid:=k a']>tp) (k_int a') ∧ (a = a' → extends_ctrace_ tr' tid (observe (k a')) (<[tid:=k a']>tp) (observe (k_int a')))) →
    ∃ t, extends_ctrace (CTVis A e a tr') tid tp t.
  Proof.
    intros Hidx Hobs [k_int H].
    eexists (Vis e _).
    eexists. split; first done. rewrite Hobs. constructor.
    - intros a'. by destruct (H a') as [Hint _].
    - destruct (H a) as [_ Hext]. by apply Hext.
  Qed.

  Lemma ctrace_extension_exists tr tid tp :
    AnswerEqDecision E →
    is_ctrace tr tid tp →
    ∃ t_int, extends_ctrace tr tid tp t_int.
  Proof.
    intros Hanswer [t [Hidx Htr]].
    remember (observe t) as ot.
    revert t Hidx Heqot.
    induction Htr as [tid tp r|tr' tid tp A e a k Htr IH|tid tp A f e k|tr' tid tp k t' tid' Hidx' Htr IH|tr' tid tp k t' tid' Hidx' Htr IH|k t'|tr' tid tp k k_new' Hsim Htr IH|tid t' tp Htr|tr t' tid tp Htr IH]; intros t Hidx Heqot.
    - exists (Ret (inl r)). eexists. split; first done. destruct Heqot. constructor.
    - apply exists_vis with (t := t) (k := k); eauto.
      (* FIXME: Get rid of manual instantiation of [R]. *)
      apply choice with (R := (λ a' k_inta', interleaves tid (<[tid:=k a']>tp) (k_inta') ∧ (a = a' → extends_ctrace_ tr' tid (observe (k a')) (<[tid:=k a']>tp) (observe (k_inta'))))).
      intros a'. destruct (equal e a a') as [<-|Hneq].
      * unshelve epose (IH (k a) _ _) as Hext; eauto.
        (* FIXME: These two tactics are repeated a lot. Would make sense to automate. *)
        { apply list_lookup_insert. by apply lookup_lt_is_Some_1. }
        destruct Hext as [t_int Hext]. exists t_int. split.
        { by apply extends_ctrace_is_interleaving with (tr := tr'). }
        intros _. destruct Hext as [oka [Hidx' Hext]].
        rewrite list_lookup_insert in Hidx'; last by apply lookup_lt_is_Some_1.
        by injection Hidx' as <-.
      * exists (scheduler (k a') (delete tid tp)). split; last done.
        replace (delete tid tp) with (delete tid (<[tid:=k a']> tp)); last apply list_delete_insert.
        apply schedule_exists. rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1.
    - exists (Vis e (λ a, match f a with end)). eexists. split; first done. destruct Heqot.
      by constructor.
    - destruct (IH t' Hidx' eq_refl) as [t_int [t'' [Hidx'' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. by econstructor.
    - destruct (IH t' Hidx' eq_refl) as [t_int [t'' [Hidx'' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. by econstructor.
    - exists (Ret (inr LastThreadKilled)). eexists. split; first done.  destruct Heqot. constructor.
    - unshelve epose (IH (k CurrentThread) _ _) as Hext; eauto.
      { rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
        apply list_lookup_insert. by apply lookup_lt_is_Some_1. }
      destruct Hext as [t_int [t'' [Hidx' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. constructor; first done.
      rewrite lookup_app_l in Hidx'; last rewrite insert_length -lookup_lt_is_Some //.
      rewrite /= list_lookup_insert in Hidx'; last by apply lookup_lt_is_Some_1.
      by injection Hidx' as <-.
    - exists (scheduler t (delete tid tp)).
      eexists. split; first done. destruct Heqot. constructor.
      rewrite -itree_eta_. by apply schedule_exists.
    - unshelve epose (IH t' _ _) as Hext; eauto.
      { apply list_lookup_insert. by apply lookup_lt_is_Some_1. }
      destruct Hext as [t_int [t'' [Hidx' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. constructor.
      rewrite /= list_lookup_insert in Hidx'; last by apply lookup_lt_is_Some_1.
      by injection Hidx' as <-.
  Qed.

  Lemma extends_ctrace_is_trace tr tid tp t_int :
    extends_ctrace tr tid tp t_int →
    is_trace (sequencify tr) t_int.
  Proof.
    intros [t [Hidx Hext]].
    remember (observe t) as ot.
    remember (observe t_int) as ot_int.
    revert t_int t Hidx Heqot Heqot_int.
    induction Hext as [tid tp r|tr' tid tp A e a k k_int Hint Hext IH|tid tp A f e k k_int|tr' tid t' tp t'_int Hext IH|tr' tid tp k t' tid' t'_int Hidx' Hext IH|tr' tid tp k t' tid' t'_int Hidx' Hext IH|k t'|tr' tid tp k t'_int k_current' Hsim Hext IH|tid t' tp t'_int Hint]; intros t_int t Hidx Heqot Heqot_int.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor. apply IH with (t := k a); eauto.
      apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - simpl. rewrite /is_trace. destruct Heqot_int. by constructor.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor. apply IH with (t := t'); eauto.
      apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor. apply IH with (t := t'); eauto.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor. apply IH with (t := t'); eauto.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor.
      apply IH with (t := k CurrentThread); eauto.
      rewrite lookup_app_l; last rewrite insert_length -lookup_lt_is_Some //.
      apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor.
  Qed.

  Theorem interleaving_extending_trace (tr : ctrace E R) tid tp :
    AnswerEqDecision E →
    is_ctrace tr tid tp →
    ∃ t_int, interleaves tid tp t_int ∧ is_trace (sequencify tr) t_int.
  Proof.
    intros Hanswer Htr. apply ctrace_extension_exists in Htr as [t_int Hext]; last done.
    exists t_int. split.
    - by apply extends_ctrace_is_interleaving with (tr := tr).
    - by apply extends_ctrace_is_trace with (tid := tid) (tp := tp).
  Qed.
End extend_ctrace.
