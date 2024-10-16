From ITree Require Import ITree Eqit.
From Paco Require Import paco.
From Paco Require Import paco2.
From stdpp Require Import list.
From iris.itree.threadpool Require Import handler interleaving scheduler.
From iris.itree Require Import axioms itree.
From iris.itree Require Export trace.

(** A variant of [trace] tailored specifically for [threadpoolE] ("concurrent
trace").

Since [threadpoolE] is a very special type, [trace (threadpoolE +' E) R] is not
the appropriate notion of a "trace". One needs something more sophisticated
that can take into account that when executing an [itree (threadpoolE +' E) R],
one needs to sometimes execute multiple branches of certain [Vis] nodes. This
is the type for that. *)
Inductive ctrace (E : Type → Type) (R : Type) :=
  (** Yield control to a new thread [new_tid] and continue with the trace
  [tr']. *)
  | CTYield (new_tid : nat) (tr' : ctrace E R)
  (** Terminate the current thread and yield control to a new thread [new_tid]
  and continue with the trace [tr'] *)
  | CTKillThread (new_tid : nat) (tr' : ctrace E R)
  (** Terminate the current and last thread. *)
  | CTKillLastThread
  (** Fork a new thread [t] and continue in the current thread with trace
  [tr']. *)
  | CTFork (t : itree (threadpoolE +' E) R) (tr' : ctrace E R)
  (* Variants familiar from [trace E R]: *)
  | CTRet (r : R)
  | CTVis {A : Type} (e : E A) (a : A) (tr' : ctrace E R)
  | CTVisEmpty {A : Type} (e : E A)
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
  | ctrace_CTRet tid tp r :
    is_ctrace_ (CTRet r) tid (RetF r) tp
  | ctrace_CTVis tr' tid tp A (e : E A) a k :
    is_ctrace_ tr' tid (observe (k a)) (<[tid:=k a]>tp) →
    is_ctrace_ (CTVis A e a tr') tid (VisF (inr1 e) k) tp
  | ctrace_CTVisEmpty tid tp A (f : A → Empty_set) (e : E A) k :
    is_ctrace_ (CTVisEmpty A e) tid (VisF (inr1 e) k) tp
  | ctrace_CTYield tr' tid tp k t' tid' :
    <[tid := k ()]>tp !! tid' = Some t' →
    is_ctrace_ tr' tid' (observe t') (<[tid := k ()]>tp) →
    is_ctrace_ (CTYield tid' tr') tid (VisF (inl1 EYield) k) tp
  | ctrace_CTKillThread tr' tid tp k t' tid' :
    (delete tid tp) !! tid' = Some t' →
    is_ctrace_ tr' tid' (observe t') (delete tid tp) →
    is_ctrace_ (CTKillThread tid' tr') tid (VisF (inl1 EKillThread) k) tp
  | ctrace_CTKillLastThread k t :
    is_ctrace_ CTKillLastThread 0 (VisF (inl1 EKillThread) k) [t]
  | ctrace_CTFork tr' tid tp k k_new' :
    k_new' ≈ k NewThread →
    is_ctrace_ tr' tid (observe (k CurrentThread)) (<[tid := k CurrentThread]>tp ++ [k NewThread]) →
    is_ctrace_ (CTFork k_new' tr') tid (VisF (inl1 EFork) k) tp
  | ctrace_CTCut tid t tp :
    is_ctrace_ CTCut tid t tp
  (** [is_ctrace] is insensitive to [Tau]s. Because it is defined
  inductively, we eventually show insensitivity to [eutt]. *)
  | ctrace_Tau tr t' tid tp :
    is_ctrace_ tr tid (observe t') (<[tid := t']>tp) →
    is_ctrace_ tr tid (TauF t') tp.

  (** [tr] is a valid trace in the threadpool [tp] with current thread [tid]. *)
  Definition is_ctrace (tr : ctrace E R) (tid : nat) (tp : list (itree (threadpoolE +' E) R)) : Prop :=
    ∃ t, tp !! tid = Some t ∧ is_ctrace_ tr tid (observe t) tp.

  (** [CTCut] is always a valid trace (unless [tid] is out of bounds). *)
  Lemma is_ctrace_CTCut tid tp :
    tid < length tp →
    is_ctrace CTCut tid tp.
  Proof.
    intros [t Htp]%lookup_lt_is_Some_2.
    exists t. split; first done.
    constructor.
  Qed.

  (** [eutt] lifted to [ctrace]s. This is needed to set up the right induction
  to prove insensitivity of [is_ctrace] to [eutt]. *)
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
    induction Htr as [tid tp1 r|tr' tid tp1 A e a k Htr IH|tid tp1 A f e k|tr' tid tp1 k t' tid' Hidx' Htr IH|tr' tid tp1 k t' tid' Hidx' Htr IH|k t'|tr' tid tp1 k k_new' Hsim' Htr IH|tid t' tp1|tr t' tid tp1 Htr IH]; intros tr2 tp2 t1 t2 ot2 Heqot1 Heqot2 Hidx1 Hidx2 Hsim Htp Heqit.
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
      * pclearbot. intros. inversion Hsim. simplify_K. simplify_K. apply ctrace_CTFork.
        { transitivity k_new'; first done.
          transitivity (k1 NewThread); first done.
          apply REL.
        }
        eapply IH; eauto.
        + rewrite lookup_app_l; last rewrite length_insert -lookup_lt_is_Some //.
          apply list_lookup_insert. by apply lookup_lt_is_Some_1.
        + rewrite lookup_app_l; last rewrite length_insert -lookup_lt_is_Some //.
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
  (** [is_ctrace] is insensitive to [eutt] (and finer relations). *)
  Global Instance is_ctrace_eutt b1 b2 tr n :
    Proper (Forall2 (eqit (=) b1 b2) ==> (↔)) (is_ctrace tr n).
  Proof.
    intros tp1 tp2 Htp.
    apply Forall2_impl with (Q := eqit (=) true true) in Htp; last first.
    { intros t1 t2 Heqit. by apply eutt_weak in Heqit. }
    split.
    - intros Hctr. eapply is_ctrace_eutt'.
      * reflexivity.
      * apply Htp.
      * done.
    - intros Hctr. eapply is_ctrace_eutt'.
      * reflexivity.
      * symmetry. apply Htp.
      * done.
  Qed.

  (** Replace a thread in the threadpool with one that is equivalent up to
  [eutt]. *)
  Lemma is_ctrace_insert tr tp n t t' :
    tp !! n = Some t →
    t ≈ t' →
    is_ctrace tr n (<[n := t']>tp) →
    is_ctrace tr n tp.
  Proof.
    intros Htp <- Htr.
    replace tp with (<[n:=t]> tp); first done.
    rewrite list_insert_id //.
  Qed.

  (** Step over an [EYield]. *)
  Lemma is_ctrace_yield tid tid' (tp : list (itree (threadpoolE +' E) R)) tr t :
    tp !! tid = Some (ITree.bind yield (λ _, t))%itree →
    is_ctrace tr tid' (<[tid := t]>tp) →
    is_ctrace (CTYield tid' tr) tid tp.
  Proof.
    intros Htp (t'&Htp'&Htr).
    eapply is_ctrace_insert; first done; first rewrite bind_trigger //.
    eexists. split. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1. }
    econstructor; rewrite list_insert_insert //.
  Qed.

  (** Step over an event in [E]. *)
  Lemma is_ctrace_Vis {A} tid (tp : list (itree (threadpoolE +' E) R)) (e : E A) tr k (a : A) :
    tp !! tid = Some (ITree.bind (trigger e) k) →
    is_ctrace tr tid (<[tid := k a]>tp) →
    is_ctrace (CTVis A (subevent _ e) a tr) tid tp.
  Proof.
    intros Htp Htr. eapply is_ctrace_insert; first done; first done.
    rewrite bind_trigger.
    eexists. split. { rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1. }
    apply ctrace_CTVis.
    rewrite list_insert_insert.
    destruct Htr as (t'&Ht'&Htr).
    rewrite list_lookup_insert in Ht'; last by apply lookup_lt_is_Some_1.
    by injection Ht' as <-.
  Qed.

  Lemma is_ctrace_eutt_last tr tid tp t1 t2 :
    t1 ≈ t2 →
    is_ctrace tr tid (tp ++ [t1]) →
    is_ctrace tr tid (tp ++ [t2]).
  Proof.
    intros Heutt Htr.
    apply (is_ctrace_eutt true true _ _ (tp ++ [t1])).
    - f_equiv. by constructor.
    - done.
  Qed.

  Lemma is_ctrace_CTFork tid tp tr' k k_new' :
    tp !! tid = Some (Vis (inl1 EFork) k) →
    k_new' ≈ k NewThread →
    is_ctrace tr' tid (<[tid := k CurrentThread]>tp ++ [k_new']) →
    is_ctrace (CTFork k_new' tr') tid tp.
  Proof.
    intros Htp Heutt Htr.
    eapply is_ctrace_eutt_last with (t2 := k NewThread) in Htr; last done.
    econstructor. split; first done.
    destruct Htr as (t'&Ht'&Htr).
    constructor; first done.
    apply lookup_lt_Some in Htp.
    rewrite lookup_app_l in Ht'; last rewrite length_insert //.
    rewrite list_lookup_insert // in Ht'.
    injection Ht' as Heq. rewrite Heq. by rewrite Heq in Htr.
  Qed.
End is_ctrace.

(** Strip away all [threadpoolE] events to get a [trace]. *)
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

Section postfix.
  (** [is_postfix_ctrace tr tr'] says that [tr] is a postfix of [tr']. *)
  Inductive is_postfix_ctrace {E R}
    : ctrace E R
    → ctrace E R
    → Prop :=
  | is_postfix_ctrace_same tr :
    is_postfix_ctrace tr tr
  | is_postfix_ctrace_CTVis tr tr' A e a :
    is_postfix_ctrace tr tr' →
    is_postfix_ctrace tr (CTVis A e a tr')
  | is_postfix_ctrace_CTYield tr tr' new_tid :
    is_postfix_ctrace tr tr' →
    is_postfix_ctrace tr (CTYield new_tid tr')
  | is_postfix_ctrace_CTKillThread tr tr' new_tid :
    is_postfix_ctrace tr tr' →
    is_postfix_ctrace tr (CTKillThread new_tid tr')
  | is_postfix_ctrace_CTFork tr tr' t :
    is_postfix_ctrace tr tr' →
    is_postfix_ctrace tr (CTFork t tr').

  (** [sequencify] preserves postfixes. *)
  Lemma sequencify_is_postfix {E R} (tr tr' : ctrace E R) :
    is_postfix_ctrace tr tr' →
    is_postfix (sequencify tr) (sequencify tr').
  Proof.
    induction 1.
    - constructor.
    - simpl. by constructor.
    - done.
    - done.
    - done.
  Qed.

  Global Instance is_postfix_ctrace_trans {E R} : Transitive (is_postfix_ctrace (E := E) (R := R)).
  Proof.
    intros tr1 tr2 tr3 Htr12 Htr23.
    induction Htr23; first done.
    all: constructor; by apply IHHtr23.
  Qed.
End postfix.

Section interleaving.
  Context {E : Type → Type} {R : Type}.

  (** Our goal is now to given a [tr : ctrace E R] for a [itree (threadpoolE +' E) R]
  produce an interleaving [t' : itree E (R + last_thread_killed)] "extending" [tr],
  that is, such that [sequencify tr] is a trace in [t']. This is the theorem
  [threadpool_trace]. We call the class of theorems of this type "trace theory". *)

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

  (** This intermediate definition codifies [t_int] being an interleaving of
  [tp] with current thread [tid] (proven in [extends_ctrace_interleaving]), and
  this interleaving "extending"/"being compatible with" the trace [tr]
  (proven in [extends_ctrace_is_trace]). *)
  Definition extends_ctrace
    (tr : ctrace E R)
    (tid : nat)
    (tp : list (itree (threadpoolE +' E) R))
    (t_int : itree E (R + last_thread_killed)) : Prop :=
    ∃ t, tp !! tid = Some t ∧ extends_ctrace_ tr tid (observe t) tp (observe t_int).

  Hint Resolve interleaves__mono : paco.
  Lemma extends_ctrace_interleaving tr tid tp t_int :
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
      simpl. rewrite lookup_app_l; last rewrite length_insert -lookup_lt_is_Some //.
      apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - pfold. punfold Hint. rewrite /interleaves_. rewrite /interleaves_ in Hint. simpl in Hint.
      rewrite -Heqot_int //.
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
      rewrite lookup_app_l; last rewrite length_insert -lookup_lt_is_Some //.
      apply list_lookup_insert. by apply lookup_lt_is_Some_1.
    - simpl. rewrite /is_trace. destruct Heqot_int. constructor.
  Qed.

  (** Annoying intermediate statement used to get goal into the right form to
  apply the choice axiom. *)
  Lemma exists_Vis t A e a tid tp tr' k :
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

  Lemma extends_ctrace_exists tr tid tp :
    AnswerEqDecision E →
    is_ctrace tr tid tp →
    ∃ t_int, extends_ctrace tr tid tp t_int.
  Proof.
    intros Hanswer [t [Hidx Htr]].
    remember (observe t) as ot.
    revert t Hidx Heqot.
    induction Htr as [tid tp r|tr' tid tp A e a k Htr IH|tid tp A f e k|tr' tid tp k t' tid' Hidx' Htr IH|tr' tid tp k t' tid' Hidx' Htr IH|k t'|tr' tid tp k k_new' Hsim Htr IH|tid t' tp|tr t' tid tp Htr IH]; intros t Hidx Heqot.
    - exists (Ret (inl r)). eexists. split; first done. destruct Heqot. constructor.
    - apply exists_Vis with (t := t) (k := k); eauto.
      (* FIXME: Get rid of manual instantiation of [R]. *)
      apply AxChoice with (R := (λ a' k_inta', interleaves tid (<[tid:=k a']>tp) (k_inta') ∧ (a = a' → extends_ctrace_ tr' tid (observe (k a')) (<[tid:=k a']>tp) (observe (k_inta'))))).
      intros a'. destruct (equal e a a') as [<-|Hneq].
      * unshelve epose (IH (k a) _ _) as Hext; eauto.
        (* FIXME: These two tactics are repeated a lot. Would make sense to automate. *)
        { apply list_lookup_insert. by apply lookup_lt_is_Some_1. }
        destruct Hext as [t_int Hext]. exists t_int. split.
        { by apply extends_ctrace_interleaving with (tr := tr'). }
        intros _. destruct Hext as [oka [Hidx' Hext]].
        rewrite list_lookup_insert in Hidx'; last by apply lookup_lt_is_Some_1.
        by injection Hidx' as <-.
      * exists (scheduler tid ((<[tid:=k a']> tp))). split; last done.
        apply scheduler_interleaves. rewrite list_lookup_insert //. by apply lookup_lt_is_Some_1.
    - exists (Vis e (λ a, match f a with end)). eexists. split; first done. destruct Heqot.
      by constructor.
    - destruct (IH t' Hidx' eq_refl) as [t_int [t'' [Hidx'' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. by econstructor.
    - destruct (IH t' Hidx' eq_refl) as [t_int [t'' [Hidx'' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. by econstructor.
    - exists (Ret (inr LastThreadKilled)). eexists. split; first done.  destruct Heqot. constructor.
    - unshelve epose (IH (k CurrentThread) _ _) as Hext; eauto.
      { rewrite lookup_app_l; last rewrite length_insert -lookup_lt_is_Some //.
        apply list_lookup_insert. by apply lookup_lt_is_Some_1. }
      destruct Hext as [t_int [t'' [Hidx' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. constructor; first done.
      rewrite lookup_app_l in Hidx'; last rewrite length_insert -lookup_lt_is_Some //.
      rewrite /= list_lookup_insert in Hidx'; last by apply lookup_lt_is_Some_1.
      by injection Hidx' as <-.
    - exists (scheduler tid tp).
      eexists. split; first done. destruct Heqot. constructor.
      rewrite -itree_eta_. by apply scheduler_interleaves.
    - unshelve epose (IH t' _ _) as Hext; eauto.
      { apply list_lookup_insert. by apply lookup_lt_is_Some_1. }
      destruct Hext as [t_int [t'' [Hidx' Hext]]]. exists (Tau t_int).
      eexists. split; first done. destruct Heqot. constructor.
      rewrite /= list_lookup_insert in Hidx'; last by apply lookup_lt_is_Some_1.
      by injection Hidx' as <-.
  Qed.

  (** Construct an interleaving from a [ctrace]. *)
  Theorem threadpool_trace `{AnswerEqDecision E} (tr : ctrace E R) tid tp :
    is_ctrace tr tid tp →
    ∃ t_int, interleaves tid tp t_int ∧ is_trace (sequencify tr) t_int.
  Proof.
    intros Htr. apply extends_ctrace_exists in Htr as [t_int Hext]; last done.
    exists t_int. split.
    - by apply extends_ctrace_interleaving with (tr := tr).
    - by apply extends_ctrace_is_trace with (tid := tid) (tp := tp).
  Qed.
End interleaving.

Lemma tac_normalize_ctrace_insert {E R} p (t t' : itree (threadpoolE +' E) R) tid tr tid' ts :
  NormalizeITree p t t' →
  is_ctrace tr tid (<[tid':=t']>ts) →
  is_ctrace tr tid (<[tid':=t]>ts).
Proof. by move => [->]. Qed.

Ltac is_ctrace_norm :=
  lazymatch goal with
  | |- is_ctrace _ _ (<[_:=_]>_) =>
      notypeclasses refine (tac_normalize_ctrace_insert _ _ _ _ _ _ _ _ _);
        [solve_normalize_itree..|]
  end.
Tactic Notation "is_ctrace_norm/=" :=
  repeat (simpl; is_ctrace_norm).
