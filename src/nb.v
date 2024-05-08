From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.bi Require Import fixpoint.
From iris.bi Require Import derived_laws.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import ITree.
From ITree Require Import Eqit.

(** An event type for No Behavior (NB). *)
Variant nbE : Type → Type :=
  (** Event for exhibiting No Behavior (crash safely/discard execution). *)
  | ENb : nbE void.

(** Exhibit Undefined Behavior (crash unsafely). *)
Definition nb {R : Type} `{nbE -< E} : itree E R :=
  vis ENb (λ (a : Empty_set), match a with end).

Section handler.
  Context {Σ : gFunctors}.

  Program Definition nbH : iHandler Σ nbE :=
    IHandler (λ _ _ _ _, True%I) _.
  Next Obligation.
    eauto.
  Qed.
  Global Instance nbH_Sequential :
    Sequential nbH.
  Proof.
    by iIntros (A e Φ s) "HH".
  Qed.
End handler.

(** "Sandbox" an [itree] with NB events by replacing NB with returning [None]. *)
Definition sandbox_nb {R E} (t : itree (nbE +' E) R) : itree E (option R) :=
  ITree.iter (λ (t : itree (nbE +' E) (option R)),
    match observe t with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | VisF (inl1 ENb) k => Ret (inr None)
    | VisF (inr1 e) k => ITree.map (λ x, inl (k x)) (trigger e)
    end) (ITree.map Some t).

Lemma sandbox_nb_ret {E R} (r : R) :
  sandbox_nb (Ret r) ≅ (Ret (Some r) : itree E (option R)).
Proof.
  rewrite /sandbox_nb.
  pose (Heq := map_ret (E:=nbE +' E) Some r).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_nb_tau {E R} (t : itree (nbE +' E) R) :
  sandbox_nb (Tau t) ≅ Tau (sandbox_nb t).
Proof.
  rewrite /sandbox_nb.
  pose (Heq := map_tau (E:=nbE +' E) (Some : R -> option R) t).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_nb_nb {E R} (k : ∅ → itree (nbE +' E) R) :
  sandbox_nb (Vis (inl1 ENb) k) ≅ Ret None.
Proof.
  rewrite /sandbox_nb.
  pose (Heq := map_vis (E:=nbE +' E) (Some : R -> option R) (inl1 ENb) k).
  apply bisimulation_is_eq in Heq.
  rewrite Heq unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_nb_vis {E R A} (e : E A) (k : A → itree (nbE +' E) R) :
  sandbox_nb (Vis (inr1 e) k) ≅ Vis e (λ a, Tau (sandbox_nb (k a))).
Proof.
  rewrite /sandbox_nb.
  pose (Heq := map_vis (E:=nbE +' E) (Some : R -> option R) (inr1 e) k).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter /= bind_bind bind_vis. f_equiv. f_equiv. intros a.
  rewrite !bind_ret_l //.
Qed.

Section nb_adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS_gen hlc Σ} {H : iHandler Σ E}.
  (** This sequentiality assumption is necessary because [sandbox_nb]
  introduces [Ret] (with non [False] post-conditions) even in branches not
  corresponding to the main thread. *)
  Context `{!Sequential H}.

  Theorem nb_adequacy (t : itree (nbE +' E) R) Φ :
    WPi t @ nbH ⊕ H; ∅ {{ Φ }} -∗
    WPi sandbox_nb t @ H; ∅ {{ r,
      match r with
      | Some r => Φ r
      | None => True
      end
    }}.
  Proof.
    iRevert (t Φ). iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". by iEval (rewrite sandbox_nb_ret -wpi_ret').
    - iIntros "!>" (Φ t) "Hwp". rewrite sandbox_nb_tau -wpi_tau. by iApply wpi_update.
    - iIntros "!>" (Φ A [[]|e] k) "HH".
      * simpl. rewrite sandbox_nb_nb. by iApply wpi_ret'.
      * simpl. rewrite sandbox_nb_vis. iApply wpi_vis.
        iDestruct (is_seq with "HH") as "HH".
        iApply ihandler_mono; last done.
        + iIntros (a) "Hwp". rewrite wpi_tau. by iApply wpi_update_post.
        + by iIntros "!>" (a) "Hwp".
  Qed.
End nb_adequacy.
