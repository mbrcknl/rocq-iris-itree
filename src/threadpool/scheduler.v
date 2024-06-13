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

  Definition scheduler : itree (threadpoolE +' E) R → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) :=
    cofix _scheduler t tp :=
        match observe t with
        | RetF r  => Ret (inl r)
        | TauF t' => Tau (_scheduler t' tp)
        | @VisF _ _ _ A (inl1 e) k =>
          (match e in threadpoolE A return (A → itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) with
          | EFork => λ k, Tau (_scheduler (k CurrentThread) (tp ++ [k NewThread]))
          | EYield => λ k, Tau (_scheduler (k ()) tp)
          | EKillThread => λ k,
              match tp with
              | [] => Ret (inr LastThreadKilled)
              | t' :: tp' => Tau (_scheduler t' tp')
              end
          end) k
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

  Definition scheduler' : nat → list (itree (threadpoolE +' E) R) → itree E (R + last_thread_killed) :=
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
              | [] => Ret (inr LastThreadKilled)
              | _ => Tau (_scheduler (match tid with S n => n | O => length tp - 1 end) (delete tid tp))
              end
          end) k
        | VisF (inr1 e) k => Vis e (λ a, _scheduler tid (<[tid := k a]>tp))
        end
      | None => (* placeholder: *) Ret (inr LastThreadKilled)
      end.
  Notation scheduler_' t tp plan :=
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

  Lemma unfold_scheduler (t : itree (threadpoolE +' E) R) tp :
    scheduler t tp = scheduler_ t tp.
  Proof.
    apply bisimulation_is_eq. apply observing_sub_eqit; constructor; reflexivity.
  Qed.

  Lemma schedule_exists (t : itree (threadpoolE +' E) R) tid tp :
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
