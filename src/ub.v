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

(** An event type for Undefined Behavior. *)
Variant ubE : Type → Type :=
  (** Event for exhibiting Undefined Behavior (crash unsafely). *)
  | EUb : ubE void.

(** Exhibit Undefined Behavior (crash unsafely). *)
Definition ub {R : Type} `{ubE -< E} : itree E R :=
  vis EUb (λ (a : Empty_set), match a with end).

Section handler.
  Context {Σ : gFunctors}.

  Program Definition ubH : iHandler Σ ubE :=
    IHandler (λ _ _ _ _, False%I) _.
  Next Obligation.
    eauto.
  Qed.
  Global Instance ubH_Sequential :
    Sequential ubH.
  Proof.
    by iIntros (A e Φ s) "HH".
  Qed.
End handler.

(** "Sandbox" an [itree] with UB events by replacing UB with returning [None]
("crashing safely"). *)
Definition sandbox {R E} (t : itree (ubE +' E) R) : itree E (option R) :=
  ITree.iter (λ (t : itree (ubE +' E) (option R)),
    match observe t with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | VisF (inl1 EUb) k => Ret (inr None)
    | VisF (inr1 e) k => ITree.map (λ x, inl (k x)) (trigger e)
    end) (ITree.map Some t).

Lemma sandbox_ret {E R} (r : R) :
  sandbox (Ret r) ≅ (Ret (Some r) : itree E (option R)).
Proof.
  rewrite /sandbox.
  pose (Heq := map_ret (E:=ubE +' E) Some r).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_tau {E R} (t : itree (ubE +' E) R) :
  sandbox (Tau t) ≅ Tau (sandbox t).
Proof.
  rewrite /sandbox.
  pose (Heq := map_tau (E:=ubE +' E) (Some : R -> option R) t).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_ub {E R} (k : ∅ → itree (ubE +' E) R) :
  sandbox (Vis (inl1 EUb) k) ≅ Ret None.
Proof.
  rewrite /sandbox.
  pose (Heq := map_vis (E:=ubE +' E) (Some : R -> option R) (inl1 EUb) k).
  apply bisimulation_is_eq in Heq.
  rewrite Heq unfold_iter bind_ret_l //.
Qed.

Lemma sandbox_vis {E R A} (e : E A) (k : A → itree (ubE +' E) R) :
  sandbox (Vis (inr1 e) k) ≅ Vis e (λ a, Tau (sandbox (k a))).
Proof.
  rewrite /sandbox.
  pose (Heq := map_vis (E:=ubE +' E) (Some : R -> option R) (inr1 e) k).
  apply bisimulation_is_eq in Heq as ->.
  rewrite unfold_iter /= bind_bind bind_vis. f_equiv. f_equiv. intros a.
  rewrite !bind_ret_l //.
Qed.

Section ub_adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS_gen hlc Σ} {H : iHandler Σ E}.

  (** Intermediate statement of UB adequacy for empty masks. See below for
  general statement. *)
  Theorem ub_adequacy' (t : itree (ubE +' E) R) Φ :
    WPi t @ ubH ⊕ H; ∅ {{ Φ }} -∗
    WPi sandbox t @ H; ∅ {{ r,
      match r with
      | Some r => Φ r
      | None => False
      end
    }}.
  Proof.
    iRevert (t Φ). iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". by iEval (rewrite sandbox_ret -wpi_ret').
    - iIntros "!>" (Φ t) "Hwp". rewrite sandbox_tau -wpi_tau. by iApply wpi_update.
    - iIntros "!>" (Φ A [[]|e] k) "HH".
      * simpl. rewrite sandbox_ub. by iApply wpi_ret'.
      * simpl. rewrite sandbox_vis. iApply wpi_vis.
        iApply ihandler_mono; last done.
        + iIntros (a) "Hwp". rewrite wpi_tau. by iApply wpi_update_post.
        + iIntros "!>" (a) "Hwp". rewrite -wpi_tau. iApply wpi_clear_mask.
          iMod "Hwp". iModIntro. iApply wpi_wand; last done.
          iIntros (r). destruct r; by iIntros "Hfalse".
  Qed.

  (** Adequacy theorem for UB. *)
  Theorem ub_adequacy (t : itree (ubE +' E) R) M Φ :
    WPi t @ ubH ⊕ H; M {{ Φ }} -∗
    WPi sandbox t @ H; M {{ r,
      match r with
      | Some r => Φ r
      | None => False
      end
    }}.
  Proof.
    iIntros "Hwp".
    rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iPoseProof ub_adequacy' as "Had". iSpecialize ("Had" with "Hwp").
    iApply wpi_wand; last done. iIntros (r). destruct r.
    - eauto.
    - by iIntros "Hfalse".
  Qed.
End ub_adequacy.

Definition assert {E} `{ubE -< E} (P : Prop) `{Decision P} : itree E () :=
  if decide P then
    Ret ()
  else ub.

Section wp_ub.
  Context {E : Type → Type} `{H : iHandler Σ E} `{ubE -< E} `{inH Σ ubE E ubH H}.
  Context `{!invGS_gen hlc Σ}.

  Lemma wpi_assert M P `{Decision P} Φ :
    P →
    Φ () -∗
    WPi assert P @ H; M {{ Φ }}.
  Proof.
    iIntros (HP). rewrite /assert. destruct (decide P).
    - iApply wpi_ret.
    - contradiction.
  Qed.
End wp_ub.
