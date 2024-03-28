From iris.itree Require Import axioms.
From iris.itree.threadpool Require Import handler interleaving.
From ITree Require Import ITree Eqit.
From Paco Require Import paco.
From Paco Require Import paco2.
From stdpp Require Import list.

Section scheduler.
  Definition scheduler {E R} : itree (threadpoolE +' E) R → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) :=
    cofix _scheduler t tp :=
        match observe t with
        | RetF r  => Ret (inl r)
        | TauF t' => Tau (_scheduler t' tp)
        | @VisF _ _ _ A (inl1 e) k =>
          (match e with
          | EFork => λ k, Tau (_scheduler (k CurrentThread) (k NewThread :: tp))
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
        | EFork => λ k, Tau (scheduler (k CurrentThread) (k NewThread :: tp))
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
          rewrite list_lookup_insert; eauto.
        + rewrite /= list_delete_insert //.
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

CoInductive ctrace (E : Type → Type) (R : Type) :=
  | CTRet (r : R)
  | CTVis (A : Type) (e : E A) (a : A) (k : ctrace E R)
  | CTTau (k : ctrace E R)
  | CTYield (new_tid : nat) (k : ctrace E R)
  | CTKillThread (new_tid : nat) (k : ctrace E R)
  | CTKillLastThread
  | CTFork (t : itree (threadpoolE +' E) R) (k : ctrace E R)
  | CTCut.

Arguments CTRet {_ _}.
Arguments CTVis {_ _}.
Arguments CTTau {_ _}.
Arguments CTYield {_ _}.
Arguments CTKillThread {_ _}.
Arguments CTKillLastThread {_ _}.
Arguments CTFork {_ _}.
Arguments CTCut {_ _}.

CoInductive trace (E : Type → Type) (R : Type) :=
  | TRet (r : R)
  | TVis (A : Type) (e : E A) (a : A) (k : trace E R)
  | TTau (k : trace E R)
  | TCut.

Class AnswerEqDecision (E : Type → Type) :=
  is_AnswerEqDecision A : E A → EqDecision A.
Print RelDecision.
Print Decision.

Program Definition equal `{AnswerEqDecision E} {A : Type} (e : E A) (a a' : A) : {a = a'} + {a ≠ a'} :=
  @decide (a = a') _.
Next Obligation.
  intros E Hdec A e a a'. by apply is_AnswerEqDecision.
Qed.

Section extend_ctrace.
  Context {E : Type → Type} {R : Type} `{AnswerEqDecision E}.

  Definition extend_ctrace_to_interleaving_ : ctrace E R → nat → itree (threadpoolE +' E) R → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) :=
    cofix _extend_ctrace_to_interleaving tr tid t tp :=
        match tr with
        | CTRet r => Ret (inl r)
        | CTVis A e a tr' => Vis e (λ a', if equal e a a' then _extend_ctrace_to_interleaving tr' tid t tp else scheduler t (delete tid tp))
        | CTTau tr' => Tau (_extend_ctrace_to_interleaving tr' tid t tp)
        | CTYield new_tid tr' =>
            match tp !! new_tid with
            | Some t' => Tau (_extend_ctrace_to_interleaving tr' new_tid t' tp)
            (* Placeholder: should never happen. *)
            | None => ITree.spin
            end
        | _ => Ret (inr LastThreadKilled)
        end.

        | TauF t' => Tau (_scheduler t' tp)
        | @VisF _ _ _ A (inl1 e) k =>
          (match e with
          | EFork => λ k, Tau (_scheduler (k CurrentThread) (k NewThread :: tp))
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
        | EFork => λ k, Tau (scheduler (k CurrentThread) (k NewThread :: tp))
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

extend_ctrace_to_interleaving :: ctrace → ITree (threadpoolE +' E) R → ITree E R
is_ctrace :: ctrace → ITree (threadpoolE +' E) R → Prop
is_trace :: trace → ITree E R → Prop
tracify :: ctrace → trace

Lemma :
  is_ctrace ctr t →
  interleaving t (extend_ctrace_to_interleaving ctr t).
Lemma :
  is_ctrace ctr t →
  is_trace (tracify ctr) (extend_ctrace_to_interleaving ctr t).


Section traced_interleaving.
  Context {E : Type → Type} {R : Type}.

  Variant traced_interleavesF
    (traced_interleaves : trace E R → nat → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) → Prop)
    : trace E R
    → nat
    → itree' (threadpoolE +' E) R
    → list (itree (threadpoolE +' E) R)
    → itree' E (R + last_thread_killed)
    → Prop :=
  | Return current_tid tp r :
    traced_interleavesF interleaves (TRet r) current_tid (RetF r) tp (RetF (inl r))
  | Step trace' current_tid current' tp interleaving' :
    traced_interleaves current_tid trace' (<[current_tid:=current']>tp) interleaving' →
    traced_interleavesF interleaves (TTau trace') current_tid (TauF current') tp (TauF interleaving')
  | Emit trace' current_tid tp A (e : E A) a k k' :
    (∀ a, interleaves current_tid (<[current_tid:=k a]>tp) (k' a)) →
    traced_interleavesF interleaves trace' current_tid (<[current_tid:=k a]>tp) (k' a) →
    traced_interleavesF interleaves (TVis A e a trace') current_tid (VisF (inr1 e) k) tp (VisF e k')
  | KillThread trace' current_tid tp k new_current_tid interleaving' :
    traced_interleaves trace' new_current_tid (delete current_tid tp) interleaving' →
    traced_interleavesF interleaves (TKillThread new_current_tid trace') current_tid (VisF (inl1 EKillThread) k) tp (TauF interleaving')
  | KillLastThread k t :
    traced_interleavesF interleaves TKillLastThread 0 (VisF (inl1 EKillThread) k) [t] (RetF (inr LastThreadKilled))
  | Yield trace' current_tid tp k new_current_tid interleaving' :
    traced_interleaves trace' new_current_tid (<[current_tid := k ()]>tp) interleaving' →
    traced_interleavesF interleaves (TYield new_current_tid trace') current_tid (VisF (inl1 EYield) k) tp (TauF interleaving')
  | Fork trace' current_tid tp k interleaving' :
    traced_interleaves (S current_tid) (k NewThread :: <[current_tid := k CurrentThread]>tp) interleaving' →
    traced_interleavesF interleaves (TFork (k CurrentThread) trace') current_tid (VisF (inl1 EFork) k) tp (TauF interleaving').
  (* TODO: Somehow deal with the case where the main thread emits
  [EKillThread]. (This case is never exhibited for typical [itree]s, because
  [EKillThread] is generally only to be used to avoid forked threads from
  returning.) For example, return an [option]. *)
  Hint Constructors interleavesF : iris_itree.
  (** The recuirsion template for the interleaving relation. *)
  Definition interleaves_
    (interleaves : nat → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) → Prop)
    : nat
    → list (itree (threadpoolE +' E) R)
    → itree E (R + last_thread_killed)
    → Prop :=
    λ tid tp interleaving, ∃ t, tp !! tid = Some t ∧ interleavesF interleaves tid (observe t) tp (observe interleaving).

  Lemma interleavesF_mono interleaves interleaves' tid t tp interleaving :
    interleaves <3= interleaves' →
    interleavesF interleaves tid t tp interleaving →
    interleavesF interleaves' tid t tp interleaving.
  Proof.
    intros Hleq HinterleavesF. destruct HinterleavesF; eauto with iris_itree.
  Qed.
  Lemma interleaves__mono :
    monotone3 interleaves_.
  Proof.
    rewrite /monotone3 /interleaves_. intros tid tp t r r' [t' [Hidx Hinter]] Hrel.
    eexists. split; first done. by eapply interleavesF_mono; last done.
  Qed.
  Hint Resolve interleaves__mono : paco.

  (** The interleaving relation. (See comments above.) *)
  Definition interleaves : nat → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) → Prop :=
    paco3 interleaves_ bot3.

  Lemma interleaves_lookup tid tp interleaving :
    interleaves tid tp interleaving →
    ∃ t, tp !! tid = Some t.
  Proof.
    intros Hinter. punfold Hinter. destruct Hinter as [t' [Hidx' Hinter]]. eauto.
  Qed.
