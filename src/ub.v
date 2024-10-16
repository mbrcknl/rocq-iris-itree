From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree Require Import trace.
From iris.itree Require Import exec.
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

Global Instance AnswerEqDecision_ubE :
  AnswerEqDecision ubE.
Proof. intros A [] []. Qed.

(** Exhibit Undefined Behavior (crash unsafely). *)
Definition ub {R : Type} `{ubE -< E} : itree E R :=
  vis EUb (λ (a : Empty_set), match a with end).

Lemma ub_to_translate {E1 E2 R} (HE1 : ubE -< E1) (HE2 : ubE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (ub (R:=R)) Hin ub.
Proof. move => ?. rewrite /ub. by apply vis_to_translate. Qed.
Global Hint Resolve ub_to_translate : itree_auto.

(** Unwrap [Some v] to [v] or emit [EUb]. *)
Definition some_or_ub {E R} `{!ubE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => ub end)%itree.
Notation "x ?" := (some_or_ub x) (at level 10, format "x ?") : itree_scope.

Lemma some_or_ub_to_translate {E1 E2 R} (o : option R) (HE1 : ubE -< E1) (HE2 : ubE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (o?) Hin (o?).
Proof. move => ?. by destruct o => /=; [apply Ret_to_translate|apply ub_to_translate]. Qed.
Global Hint Resolve some_or_ub_to_translate : itree_auto.

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

Section ifn.
  (** Return type for executions that crashed due to UB. *)
  Variant ub_crash := UbCrash.

  (** Interpretation function for [ubE]. It effectively replaces [EUb] events
  with [Ret (inr UbCrash)]. *)
  Definition ub_ifn {R E} (t : itree (ubE +' E) R) : itree E (R + ub_crash) :=
    ITree.iter (λ (t : itree (ubE +' E) (R + ub_crash)),
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF (inl1 EUb) k => Ret (inr (inr UbCrash))
      | VisF (inr1 e) k => ITree.map (λ x, inl (k x)) (trigger e)
      end) (ITree.map inl t).

  (** Interpretation relation for [ubE] obtained from turning [ub_ifn] into a
  relation. *)
  Definition ub_irel {R E} (t : itree (ubE +' E) R) (t' : itree E (R + ub_crash)) : Prop :=
    t' = ub_ifn t.

  Lemma ub_ifn_irel {R E} (t : itree (ubE +' E) R) :
    ub_irel t (ub_ifn t).
  Proof. reflexivity. Qed.

  Lemma ub_ifn_ret {E R} (r : R) :
    ub_ifn (Ret r) ≅ (Ret (inl r) : itree E (R + ub_crash)).
  Proof.
    rewrite /ub_ifn.
    pose (Heq := map_ret (E:=ubE +' E) (inl (B := ub_crash)) r).
    apply bisimulation_is_eq in Heq as ->.
    rewrite unfold_iter bind_ret_l //.
  Qed.

  Lemma ub_ifn_tau {E R} (t : itree (ubE +' E) R) :
    ub_ifn (Tau t) ≅ Tau (ub_ifn t).
  Proof.
    rewrite /ub_ifn.
    pose (Heq := map_tau (E:=ubE +' E) (inl (B := ub_crash)) t).
    apply bisimulation_is_eq in Heq as ->.
    rewrite unfold_iter bind_ret_l //.
  Qed.

  Lemma ub_ifn_ub {E R} (k : ∅ → itree (ubE +' E) R) :
    ub_ifn (Vis (inl1 EUb) k) ≅ Ret (inr UbCrash).
  Proof.
    rewrite /ub_ifn.
    pose (Heq := map_vis (E:=ubE +' E) (inl (B := ub_crash)) (inl1 EUb) k).
    apply bisimulation_is_eq in Heq.
    rewrite Heq unfold_iter bind_ret_l //.
  Qed.

  Lemma ub_ifn_vis {E R A} (e : E A) (k : A → itree (ubE +' E) R) :
    ub_ifn (Vis (inr1 e) k) ≅ Vis e (λ a, Tau (ub_ifn (k a))).
  Proof.
    rewrite /ub_ifn.
    pose (Heq := map_vis (E:=ubE +' E) (inl (B := ub_crash)) (inr1 e) k).
    apply bisimulation_is_eq in Heq as ->.
    rewrite unfold_iter /= bind_bind bind_vis. f_equiv. f_equiv. intros a.
    rewrite !bind_ret_l //.
  Qed.
End ifn.

Section adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS_gen hlc Σ} {H : iHandler Σ E}.

  (** Intermediate statement of UB adequacy for empty masks. See below for
  general statement. *)
  Theorem ub_adequacy_empty (t : itree (ubE +' E) R) Φ :
    WPi t @ ubH ⊕ H; ∅ {{ Φ }} -∗
    WPi ub_ifn t @ H; ∅ {{ r,
      match r with
      | inl r => Φ r
      | inr UbCrash => False
      end
    }}.
  Proof.
    iRevert (t Φ). iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". by iEval (rewrite ub_ifn_ret -wpi_ret').
    - iIntros "!>" (Φ t) "Hwp". rewrite ub_ifn_tau -wpi_tau. by iApply wpi_update.
    - iIntros "!>" (Φ A [[]|e] k) "HH".
      * simpl. rewrite ub_ifn_ub. by iApply wpi_ret'.
      * simpl. rewrite ub_ifn_vis. iApply wpi_vis.
        iApply ihandler_mono; last done.
        + iIntros (a) "Hwp". rewrite wpi_tau. by iApply wpi_update_post.
        + iIntros "!>" (a) "Hwp". rewrite -wpi_tau. iApply wpi_clear_mask.
          iMod "Hwp". iModIntro. iApply wpi_wand; last done.
          iIntros (r). destruct r as [r|[]]; by iIntros "Hfalse".
  Qed.

  (** Adequacy theorem for [ubH]. *)
  Theorem ub_adequacy (t : itree (ubE +' E) R) (t' : itree E (R + ub_crash)) M Φ :
    ub_irel t t' →
    WPi t @ ubH ⊕ H; M {{ Φ }} -∗
    WPi t' @ H; M {{ r,
      match r with
      | inl r => Φ r
      | inr UbCrash => False
      end
    }}.
  Proof.
    iIntros (->) "Hwp".
    rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iPoseProof ub_adequacy_empty as "Had". iSpecialize ("Had" with "Hwp").
    iApply wpi_wand; last done. iIntros (r). destruct r as [r|[]].
    - eauto.
    - by iIntros "Hfalse".
  Qed.
End adequacy.

(** Assert a decidable property [P] and crash with [EUb] if it fails. *)
Definition assert {E} `{ubE -< E} (P : Prop) `{Decision P} : itree E () :=
  if decide P then
    Ret ()
  else ub.

Lemma assert_to_translate {E1 E2} (HE1: ubE -< E1) (HE2: ubE -< E2) P `{!Decision P} (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (assert P) Hin (assert P).
Proof. move => ?. rewrite /assert. by case_decide; [apply Ret_to_translate|apply ub_to_translate]. Qed.
Global Hint Resolve assert_to_translate : itree_auto.

Lemma assert_True {E} `{ubE -< E} (P : Prop) `{Decision P} :
  P → assert (E := E) P ≈ Ret ().
Proof. intros HP. rewrite /assert decide_True //. Qed.

Lemma assert_False {E} `{ubE -< E} (P : Prop) `{Decision P} :
  ¬ P → assert (E := E) P ≈ ub.
Proof. intros HP. rewrite /assert decide_False //. Qed.

Section wp.
  Context {E : Type → Type} `{H : iHandler Σ E} `{ubE -< E} `{inH Σ ubE E ubH H}.
  Context `{!invGS_gen hlc Σ}.

  Lemma wpi_ub {R} M Φ :
    WPi ub (R := R) @ H; M {{ Φ }} -∗
    |={M}=> False.
  Proof.
    iIntros "Hwp". rewrite -wpi_vis' -(is_inH (H1 := ubH)) /=. by iMod "Hwp".
  Qed.

  Lemma wpi_assert M P `{Decision P} Φ :
    P →
    Φ () -∗
    WPi assert P @ H; M {{ Φ }}.
  Proof.
    iIntros (HP). rewrite /assert. destruct (decide P).
    - iApply wpi_ret.
    - contradiction.
  Qed.
End wp.

Section ub_trace.
  Context {R : Type} {E : Type → Type}.

  (** Interpret away [ubE] from a trace, instead returning [inr UbCrash] if
  [EUb] is encountered. *)
  Fixpoint interp_tr_ub (tr : trace (ubE +' E) R) : trace E (R + ub_crash) :=
    match tr with
    | TRet r => TRet (inl r)
    | TVis A (inr1 e) a k => TVis A e a (interp_tr_ub k)
    | TVisEmpty A (inl1 EUb) => TRet (inr UbCrash)
    | TVisEmpty A (inr1 e) => TVisEmpty A e
    | _ => TCut
    end.

  (** [ub_ifn] preserves traces. *)
  Lemma ub_ifn_trace (tr : trace (ubE +' E) R) t :
    is_trace tr t →
    is_trace (interp_tr_ub tr) (ub_ifn t).
  Proof.
    intros Htr. rewrite /is_trace in Htr.
    remember (observe t) as ot. revert t Heqot.
    induction Htr; intros t_ Heqot; simplify_obs.
    - constructor.
    - destruct e as [e|e]; first destruct e as [].
      * constructor.
      * simpl. rewrite ub_ifn_vis. constructor. constructor. by apply IHHtr.
    - destruct e as [e|e].
      * destruct e. constructor.
      * rewrite ub_ifn_vis. by constructor.
    - constructor.
    - rewrite ub_ifn_tau. constructor. by apply IHHtr.
  Qed.

  (** A version of [ub_ifn_trace] that looks more like other lemmata such as
  [demonic_trace]. *)
  Lemma ub_trace (tr : trace (ubE +' E) R) t :
    is_trace tr t →
    ∃ t', ub_irel t t' ∧ is_trace (interp_tr_ub tr) t'.
  Proof. intros Htr%ub_ifn_trace. exists (ub_ifn t). by split. Qed.
End ub_trace.

(** Definitions for exec *)
Program Definition ubEH : seHandler ubE :=
  SEHandler unit (λ A e s C, True) _.
Next Obligation. done. Qed.

Global Program Instance ubEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    seHandlerAdequate ubH ubEH := {| sehandler_inv s := True%I |}.
Next Obligation. move => ??????????. by iIntros (?). Qed.


Lemma exec_some_or_ub E R (EH : eHandler E E R) `{!ubE -< E} f1 f2 `{!inEH ubEH EH f1 f2} (o : option R) s C:
  (∀ x, o = Some x → C (Ret x) s) →
  exec EH (o?) s C.
Proof. move => ?. destruct o => /=; [apply exec_stop; naive_solver|]. by apply: exec_vis. Qed.

Lemma exec_assert E (EH : eHandler E E unit) `{!ubE -< E} f1 f2 `{!inEH ubEH EH f1 f2} P `{!Decision P} s C:
  (P → C (Ret tt) s) →
  exec EH (assert P) s C.
Proof. move => ?. rewrite /assert. case_decide; [apply exec_stop; naive_solver|]. by apply: exec_vis. Qed.
