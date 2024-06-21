From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree Require Import trace.
From iris.bi Require Import fixpoint.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import ITree.
From ITree Require Import Basics.Monad.
From ITree Require Import Eqit.

Variant demonicE : Type → Type :=
  | EDemonic (A : Type) `{EqDecision A} `{Inhabited A} : demonicE A.

Global Instance demonicE_AnswerEqDecision :
  AnswerEqDecision demonicE.
Proof.
  intros A e. by destruct e.
Qed.

Section handler.
  Context {Σ : gFunctors}.

  Program Definition demonicH : iHandler Σ demonicE :=
    IHandler (λ A e,
      match e with
      | EDemonic A => λ Φ _, (∀ s, Φ s)
      end
    )%I _.
  Next Obligation.
    iIntros (? e ????) "HΦwand Hswand". destruct e. iIntros "HΦ" (a). by iApply "HΦwand".
  Qed.
  Global Instance demonicH_Sequential :
    Sequential demonicH.
  Proof.
    iIntros (A e Φ s) "HH". by destruct e.
  Qed.
End handler.

Section wp_demonic.
  Context {E : Type → Type} `{H : iHandler Σ E} `{demonicE -< E} `{inH Σ demonicE E demonicH H}.
  Context `{!invGS_gen hlc Σ}.

  Lemma wpi_demonic {R A} `{EqDecision A} `{Inhabited A} k M (Φ : R → iProp Σ) :
    (∀ a, WPi k a @ H; M {{ Φ }}) -∗
    WPi (vis (EDemonic A) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /demonicH. iIntros (a).
    iEval (rewrite -wpi_update). iMod "Hfupd". rewrite wpi_clear_mask //.
  Qed.

  Lemma wpi_demonic_trigger {A} `{EqDecision A} `{Inhabited A} M (Φ : A → iProp Σ) :
    (∀ a,  Φ a) -∗
    WPi (trigger (EDemonic A)) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_demonic. iIntros (?). iApply wpi_ret. iApply "Hwp".
  Qed.
End wp_demonic.

Section demonic_adequacy.
  Context {E : Type → Type} `{H : iHandler Σ E} {R : Type} `{!invGS_gen hlc Σ}.

  Variant demonic_irelF
    (demonic_irel : itree (demonicE +' E) R → itree E R → Prop)
    : itree' (demonicE +' E) R → itree' E R → Prop :=
  | DInstantiate A `{EqDecision A} `{Inhabited A} (a : A) k t :
    demonic_irel (k a) t →
    demonic_irelF demonic_irel (VisF (inl1 (EDemonic A)) k) (TauF t)
  | DReturns r :
    demonic_irelF demonic_irel (RetF r) (RetF r)
  | DSteps t_next t_next' :
    demonic_irel t_next t_next' →
    demonic_irelF demonic_irel (TauF t_next) (TauF t_next')
  | DEmits A (e : E A) k k' :
    (∀ a, demonic_irel (k a) (k' a)) →
    demonic_irelF demonic_irel (VisF (inr1 e) k) (VisF e k').
  Hint Constructors demonic_irelF : iris_itree.
  Definition demonic_irel_
    (demonic_irel : itree (demonicE +' E) R → itree E R → Prop)
    : itree (demonicE +' E) R → itree E R → Prop :=
    λ t t', demonic_irelF demonic_irel (observe t) (observe t').

  Lemma demonic_irelF_mono demonic_irel demonic_irel' t t' :
    demonic_irel <2= demonic_irel' →
    demonic_irelF demonic_irel t t' →
    demonic_irelF demonic_irel' t t'.
  Proof.
    intros Hleq HinterleavesF. destruct HinterleavesF; eauto with iris_itree.
  Qed.
  Lemma demonic_irel__mono :
    monotone2 demonic_irel_.
  Proof.
    rewrite /monotone3 /demonic_irel_. intros ??????. by eapply demonic_irelF_mono.
  Qed.
  Hint Resolve demonic_irel__mono : paco.

  Definition demonic_irel : itree (demonicE +' E) R → itree E R → Prop :=
    paco2 demonic_irel_ bot2.

  Lemma demonic_irel_unfold (t : itree (demonicE +' E) R) t' :
    demonic_irel t t' ↔
    demonic_irelF
      (upaco2 (λ demonic_irel t t', demonic_irelF demonic_irel (observe t) (observe t')) bot2) (observe t) (observe t').
  Proof.
    split.
    - intros Hinst. rewrite /demonic_irel in Hinst. punfold Hinst.
    - intros Hinst. pfold. rewrite /demonic_irel_ //.
  Qed.

  Global Instance demonic_irel_proper_unilateral :
    Proper (eqit (=) false false ==> eqit (=) false false ==> impl) demonic_irel.
  Proof.
    pcofix CIH.
    intros t1 t2 Ht t1' t2' Ht' Hinst.
    pfold. rewrite /demonic_irel_.
    punfold Ht. punfold Ht'. punfold Hinst. rewrite /demonic_irel_ in Hinst.
    destruct Ht, Ht'; try discriminate; try inversion Hinst.
    - simplify_eq. inversion Hinst. constructor.
    - constructor. pclearbot. simplify_eq. right. eapply CIH.
      * apply REL.
      * done.
      * done.
    - simplify_K. pclearbot. eapply DInstantiate. right. eapply CIH.
      + apply REL.
      + done.
      + done.
    - simplify_K. pclearbot. inversion Hinst. simplify_K. constructor. right.
      pclearbot. eapply CIH; last apply H2.
      * apply REL.
      * apply REL0.
  Qed.
  Global Instance demonic_irel_proper :
    Proper ((eqit (=) false false) ==> (eqit (=) false false) ==> (↔)) demonic_irel.
  Proof.
    intros t1 t2 Ht t1' t2' Ht'.
    split; rewrite Ht Ht' //.
  Qed.

  Theorem demonicH_adequate' (t : itree (demonicE +' E) R) (t' : itree E R) Φ :
    demonic_irel t t' →
    WPi t @ demonicH ⊕ H; ∅ {{ Φ }} -∗
    WPi t' @ H; ∅ {{ Φ }}.
  Proof.
    iIntros (Hinstant) "Hwp".
    (* TODO: A lot of these explicitly spelled out [G]'s can be replaced by
    appropriate [iRevert]s. See [threadpool.v]. *)
    pose (G := λ (t : leibnizO (itree (demonicE +' E) R)) (Φ : leibnizO R -d> iPropO Σ), (∀ t', ⌜demonic_irel t t'⌝ → WPi t' @ H; ∅ {{ Φ }})%I).
    iApply (wpi_iter' (H := demonicH ⊕ H) G with "[] [] [] Hwp [//]"); first solve_proper; clear.
    - iModIntro. iIntros (Φ r) "HΦ". iIntros (t Hinst). punfold Hinst. inversion Hinst.
      simplify_obs. rewrite -wpi_ret' //.
    - iModIntro. iIntros (Φ t) "HG". iIntros (t' Hinst). rewrite -wpi_update. iMod "HG".
      punfold Hinst. inversion Hinst. pclearbot.
      simplify_obs. rewrite -wpi_tau. by iApply "HG".
    - iModIntro. iIntros (Φ' A e k) "HH". rewrite /G /=. iIntros (t'' Hinst).
      punfold Hinst. inversion Hinst. simplify_K. simplify_obs.
      * iApply wpi_update. iMod "HH". iModIntro. rewrite -wpi_tau. pclearbot. iApply "HH".
        iPureIntro. apply H2.
      * simplify_K. simplify_obs. rewrite -wpi_vis'.
        iApply ihandler_mono; last done.
        + iIntros (a) "Hwp". iApply wpi_update_post. pclearbot. iApply "Hwp". iPureIntro. apply H1.
        + iModIntro. iIntros (t) "Hwp". iApply wpi_clear_mask_false. iMod "Hwp". iModIntro.
          pclearbot. iApply "Hwp". iPureIntro. apply H1.
  Qed.

  Theorem demonicH_adequate (t : itree (demonicE +' E) R) (t' : itree E R) M Φ :
    demonic_irel t t' →
    WPi t @ demonicH ⊕ H; M {{ Φ }} -∗
    WPi t' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hinstant) "Hwp". rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iApply demonicH_adequate'.
    - pclearbot. apply Hinstant.
    - done.
  Qed.
End demonic_adequacy.

Section demonic_ifn.
  Context {E : Type → Type} {R : Type} `{AnswerEqDecision E}.

  Definition demonic_ifn : itree (demonicE +' E) R → itree E R :=
    cofix _demonic_ifn t :=
        match observe t with
        | RetF r  => Ret r
        | TauF t' => Tau (_demonic_ifn t')
        | @VisF _ _ _ A (inl1 e) k =>
          (match e with
          | EDemonic _ => λ k, Tau (_demonic_ifn (k inhabitant))
          end : (A → _) → _) k
        | VisF (inr1 e) k => Vis e (λ a, _demonic_ifn (k a))
        end.
  Notation demonic_ifn_ t :=
      match observe t with
      | RetF r  => Ret r
      | TauF t' => Tau (demonic_ifn t')
      | @VisF _ _ _ A (inl1 e) k =>
        (match e with
        | EDemonic _ => λ k, Tau (demonic_ifn (k inhabitant))
        end : (A → _) → _) k
      | VisF (inr1 e) k => Vis e (λ a, demonic_ifn (k a))
      end.

  Lemma unfold_demonic_ifn t :
    demonic_ifn t = demonic_ifn_ t.
  Proof.
    apply bisimulation_is_eq. apply observing_sub_eqit; constructor; reflexivity.
  Qed.

  Lemma demonic_ifn_irel t :
    demonic_irel t (demonic_ifn t).
  Proof.
    remember (demonic_ifn t) as t'.
    revert t t' Heqt'. pcofix CIH. pfold. intros t t' ->.
    rewrite unfold_demonic_ifn /demonic_irel_.
    destruct (observe t) as [r'|t'|A e k].
    - constructor.
    - constructor. right. by apply (CIH t').
    - destruct e as [e|e]; first destruct e.
      * econstructor. right. by apply (CIH (k inhabitant)).
      * constructor. right. by apply (CIH (k a)).
  Qed.
End demonic_ifn.

Section demonic_state.
  Context {E : Type → Type} {R : Type} `{AnswerEqDecision E}.

  Lemma unfold_demonic_irel_under tr (t : itree (demonicE +' E) R) :
    (∃ t', demonic_irelF
      (upaco2 (λ demonic_irel t t', demonic_irelF demonic_irel (observe t) (observe t')) bot2) (observe t) (observe t') ∧ is_trace (interp_tr tr) t') →
    ∃ t' : itree E R, demonic_irel t t' ∧ is_trace (interp_tr (E := demonicE) tr) t'.
  Proof.
    intros [t' [Hpaco Htr]].
    exists t'. split.
    - by pfold.
    - done.
  Qed.

  Lemma demonic_trace `{AnswerEqDecision E} tr (t : itree (demonicE +' E) R) :
    is_trace tr t →
    ∃ t', demonic_irel t t' ∧ is_trace (interp_tr tr) t'.
  Proof.
    intros Htr. apply unfold_demonic_irel_under. induction Htr as [r|tr' A e a k Htr [t' [Hinst Htr']]| |ot' | tr' t'' Htr [t' [Hinst Htr']]].
    - exists (Ret r). split; constructor.
    - destruct e as [e|e]; first destruct e.
      * exists (Tau t'). split.
        + apply DInstantiate with (a := a). left. by pfold.
        + simpl. constructor. done.
      * specialize (H A e).
        exists (Vis e (λ a', if decide (a = a') then t' else demonic_ifn (k a'))).
        split.
        + constructor. intros a'. left.
          destruct (decide _).
          ++ subst. by pfold.
          ++ apply demonic_ifn_irel.
        + apply is_trace_Vis. destruct (decide _); first done. contradiction.
    - destruct e as [e|e]. { destruct e as [A Heq Hinh]. destruct Hinh. contradiction. }
      exists (Vis e (λ a, match f a with end)).
      split.
      * constructor. intros a. destruct (f a) as [].
      * by constructor.
    - destruct (unobserve ot') as [t' ->].
      exists (demonic_ifn t').
      * split.
        + rewrite -demonic_irel_unfold.
          apply demonic_ifn_irel.
        + constructor.
    - exists (Tau t').
      * split.
        + constructor. left. by pfold.
        + by constructor.
  Qed.
End demonic_state.
