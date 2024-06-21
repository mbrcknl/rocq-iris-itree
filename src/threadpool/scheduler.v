From ITree Require Import ITree Eqit.
From Paco Require Import paco.
From Paco Require Import paco2.
From iris.itree Require Import axioms itree.
From iris.itree.threadpool Require Import handler interleaving.

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

Section scheduler.
  Context {E : Type → Type} {R : Type}.

  Definition scheduler : nat → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) :=
    cofix _scheduler tid tp :=
      (* Not using "!!" notation here as that leads to a Coq anomaly. *)
      match list_lookup tid tp with
      | Some t =>
        match observe t with
        | RetF r  => Ret (inl r)
        | TauF t' => Tau (_scheduler tid (<[tid := t']>tp))
        | @VisF _ _ _ A (inl1 e) k =>
          (match e in threadpoolE A return (A → _) → _ with
          | EFork => λ k, Tau (_scheduler tid (<[tid := k CurrentThread]>tp ++ [k NewThread]))
          | EYield => λ k, Tau (_scheduler (match tid with S n => n | O => length tp - 1 end) (<[tid := k ()]>tp))
          | EKillThread => λ k,
              match tp with
              | _::_::_ => Tau (_scheduler (match tid with S n => n | O => length tp - 2 end) (delete tid tp))
              | _ => Ret (inr LastThreadKilled)
              end
          end) k
        | VisF (inr1 e) k => Vis e (λ a, _scheduler tid (<[tid := k a]>tp))
        end
      | None => (* placeholder: *) Ret (inr LastThreadKilled)
      end.
  Notation scheduler_ tid tp :=
    match list_lookup tid tp with
    | Some t =>
      match observe t with
      | RetF r  => Ret (inl r)
      | TauF t' => Tau (scheduler tid (<[tid := t']>tp))
      | @VisF _ _ _ A (inl1 e) k =>
        (match e in threadpoolE A return (A → _) → _ with
        | EFork => λ k, Tau (scheduler tid (<[tid := k CurrentThread]>tp ++ [k NewThread]))
        | EYield => λ k, Tau (scheduler (match tid with S n => n | O => length tp - 1 end) (<[tid := k ()]>tp))
        | EKillThread => λ k,
            match tp with
            | _::_::_ => Tau (scheduler (match tid with S n => n | O => length tp - 2 end) (delete tid tp))
            | _ => Ret (inr LastThreadKilled)
            end
        end) k
      | VisF (inr1 e) k => Vis e (λ a, scheduler tid (<[tid := k a]>tp))
      end
    | None => (* placeholder: *) Ret (inr LastThreadKilled)
    end.

  Lemma unfold_scheduler tid tp :
    scheduler tid tp = scheduler_ tid tp.
  Proof.
    apply bisimulation_is_eq. apply observing_sub_eqit; constructor; reflexivity.
  Qed.

  Lemma scheduler_interleaves tid tp :
    is_Some (tp !! tid) →
    interleaves tid tp (scheduler tid tp).
  Proof.
    intros Hidx.
    remember (scheduler tid tp) as t.
    revert tp tid Hidx t Heqt. pcofix CIH. intros tp tid Hidx t ->.
    pfold. destruct Hidx as [t' Hidx]. exists t'. split; first done.
    rewrite unfold_scheduler.
    rewrite /lookup in Hidx. rewrite Hidx.
    destruct (observe t') as [r'|t''|A e k].
    - constructor.
    - constructor. right. apply CIH; eauto.
      apply lookup_lt_Some in Hidx.
      rewrite list_lookup_insert //.
    - destruct e as [e|e]; first destruct e.
      * constructor. right. apply CIH; eauto.
        simpl. apply lookup_lt_Some in Hidx.
        rewrite lookup_app_l; last rewrite insert_length //.
        rewrite list_lookup_insert; eauto.
      * apply Yield with (new_current_tid :=
          match tid with
          | 0 => length tp - 1
          | S n => n
          end).
        right. apply CIH; last done.
        simpl. apply lookup_lt_Some in Hidx.
        destruct tid; apply lookup_lt_is_Some_2; rewrite insert_length; lia.
      * apply singleton_or_more in Hidx as [[-> ->]|[Hlen Hidx]].
        + constructor.
        + destruct tp as [|t1 [|t2 tp']] eqn:Heq.
          ++ discriminate.
          ++ simpl in Hlen. lia.
          ++ destruct tid.
             +++ simpl. apply KillThread with (new_current_tid := length (t1 :: t2 :: tp') - 2).
                 right. apply CIH; last done. apply lookup_lt_is_Some_2. simpl. lia.
             +++ simpl. apply KillThread with (new_current_tid := tid).
                 right. simpl. apply CIH; last done. apply lookup_lt_is_Some_2.
                 rewrite /= length_delete // /=. simpl in Hidx. 
                 apply mk_is_Some in Hidx. apply lookup_lt_is_Some_1 in Hidx.
                 simpl in Hidx. lia.
      * constructor. intros a. right.
        apply CIH.
        + rewrite list_lookup_insert //. by apply lookup_lt_is_Some.
        + done.
  Qed.

  Definition threadpool_ifn (t : itree (threadpoolE +' E) R) : itree E (R + last_thread_killed) :=
    scheduler 0 [t].

  Lemma threadpool_ifn_irel t :
    threadpool_irel t (threadpool_ifn t).
  Proof. by apply scheduler_interleaves. Qed.
End scheduler.
