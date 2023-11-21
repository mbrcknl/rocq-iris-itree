From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.bi Require Import fixpoint.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import ITree.
From ITree Require Import Basics.Monad.
From ITree Require Import Eqit.

(* TODO: Use syntactic sugar such as stdpp's Equiv (≡) and (>>=). *)

Variant demonicE : Type → Type :=
  | EDemonic (A : Type) : demonicE A.
Variant angelicE : Type → Type :=
  | EAngelic (A : Type) : angelicE A.

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
    iIntros (A e Φ s s') "HH". by destruct e.
  Qed.

  Program Definition angelicH : iHandler Σ angelicE :=
    IHandler (λ A e,
      match e with
      | EAngelic A => λ Φ _, (∃ s, Φ s)
      end
    )%I _.
  Next Obligation.
    iIntros (? e ????) "HΦwand Hswand". destruct e. iIntros "[%a HΦ]". iExists a.
    by iApply "HΦwand".
  Qed.
  Global Instance angelicH_Sequential :
    Sequential angelicH.
  Proof.
    iIntros (A e Φ s s') "HH". by destruct e.
  Qed.
End handler.

Section wp_angelic.
  Context {E : Type → Type} `{H : iHandler Σ E} `{angelicE -< E} `{inH Σ angelicE E angelicH H}.
  Context `{!invGS_gen hlc Σ}.

  Lemma wpi_angelic {R A} k M (Φ : R → iProp Σ) :
    (∃ a, WPi k a @ H; M {{ Φ }}) -∗
    WPi (vis (EAngelic A) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "[%a Hwp]". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /angelicH. iExists a.
    iEval (rewrite -wpi_update). iMod "Hfupd". rewrite wpi_clear_mask //.
  Qed.
End wp_angelic.

Section wp_demonic.
  Context {E : Type → Type} `{H : iHandler Σ E} `{demonicE -< E} `{inH Σ demonicE E demonicH H}.
  Context `{!invGS_gen hlc Σ}.

  Lemma wpi_demonic {R A} k M (Φ : R → iProp Σ) :
    (∀ a, WPi k a @ H; M {{ Φ }}) -∗
    WPi (vis (EDemonic A) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /demonicH. iIntros (a).
    iEval (rewrite -wpi_update). iMod "Hfupd". rewrite wpi_clear_mask //.
  Qed.
End wp_demonic.

Section demonic_adequacy.
  Context {E : Type → Type} `{H : iHandler Σ E} {R : Type} `{!invGS_gen hlc Σ}.

  Variant demonic_instantiatesF
    (demonic_instantiates : itree (demonicE +' E) R → itree E R → Prop)
    : itree' (demonicE +' E) R → itree' E R → Prop :=
  | DInstantiate A (a : A) k t :
    demonic_instantiates (k a) t →
    demonic_instantiatesF demonic_instantiates (VisF (inl1 (EDemonic A)) k) (TauF t)
  | DReturns r :
    demonic_instantiatesF demonic_instantiates (RetF r) (RetF r)
  | DSteps t_next t_next' :
    demonic_instantiates t_next t_next' →
    demonic_instantiatesF demonic_instantiates (TauF t_next) (TauF t_next')
  | DEmits A (e : E A) k k' :
    (∀ a, demonic_instantiates (k a) (k' a)) →
    demonic_instantiatesF demonic_instantiates (VisF (inr1 e) k) (VisF e k').
  Hint Constructors demonic_instantiatesF : iris_itree.
  Definition demonic_instantiates_
    (demonic_instantiates : itree (demonicE +' E) R → itree E R → Prop)
    : itree (demonicE +' E) R → itree E R → Prop :=
    λ t t', demonic_instantiatesF demonic_instantiates (observe t) (observe t').

  Lemma demonic_instantiatesF_mono demonic_instantiates demonic_instantiates' t t' :
    demonic_instantiates <2= demonic_instantiates' →
    demonic_instantiatesF demonic_instantiates t t' →
    demonic_instantiatesF demonic_instantiates' t t'.
  Proof.
    intros Hleq HinterleavesF. destruct HinterleavesF; eauto with iris_itree.
  Qed.
  Lemma demonic_instantiates__mono :
    monotone2 demonic_instantiates_.
  Proof.
    rewrite /monotone3 /demonic_instantiates_. intros ??????. by eapply demonic_instantiatesF_mono.
  Qed.
  Hint Resolve demonic_instantiates__mono : paco.

  Definition demonic_instantiates : itree (demonicE +' E) R → itree E R → Prop :=
    paco2 demonic_instantiates_ bot2.

  Global Instance instantiates_proper_unilateral :
    Proper (eqit (=) false false ==> eqit (=) false false ==> impl) demonic_instantiates.
  Proof.
    pcofix CIH.
    intros t1 t2 Ht t1' t2' Ht' Hinst.
    pfold. rewrite /demonic_instantiates_.
    punfold Ht. punfold Ht'. punfold Hinst. rewrite /demonic_instantiates_ in Hinst.
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
  Global Instance instantiates_proper :
    Proper ((eqit (=) false false) ==> (eqit (=) false false) ==> (↔)) demonic_instantiates.
  Proof.
    intros t1 t2 Ht t1' t2' Ht'.
    split; rewrite Ht Ht' //.
  Qed.

  Theorem demonicH_adequate' (t : itree (demonicE +' E) R) (t' : itree E R) Φ :
    demonic_instantiates t t' →
    WPi t @ demonicH ⊕ H; ∅ {{ Φ }} -∗
    WPi t' @ H; ∅ {{ Φ }}.
  Proof.
    iIntros (Hinstant) "Hwp".
    unshelve epose
      (G := λne (t : leibnizO (itree (demonicE +' E) R)) (Φ : leibnizO R -d> iPropO Σ), (∀ t', ⌜demonic_instantiates t t'⌝ → WPi t' @ H; ∅ {{ Φ }})%I);
      try apply _; try solve_proper.
    iApply (wpi_iter' (H := demonicH ⊕ H) G with "[] [] [] Hwp [//]"); clear.
    - intros n t1 t2 Ht Φ1 Φ2 HΦ. by repeat f_equiv.
    - iModIntro. iIntros (Φ r) "HΦ". iIntros (t Hinst). punfold Hinst. inversion Hinst.
      simplify_obs. rewrite -wpi_ret' //.
    - iModIntro. iIntros (Φ t) "HG". iIntros (t' Hinst). rewrite -wpi_update. iMod "HG".
      punfold Hinst. inversion Hinst. pclearbot.
      simplify_obs. rewrite -wpi_tau. by iApply "HG".
    - iModIntro. iIntros (Φ' A e k) "HH". rewrite /G /=. iIntros (t'' Hinst).
      punfold Hinst. inversion Hinst. simplify_K. simplify_obs.
      * iApply wpi_update. iMod "HH". iModIntro. rewrite -wpi_tau. pclearbot. iApply "HH".
        iPureIntro. apply H1.
      * simplify_K. simplify_obs. rewrite -wpi_vis'.
        iApply ihandler_mono; last done.
        + iIntros (a) "Hwp". iApply wpi_update_post. pclearbot. iApply "Hwp". iPureIntro. apply H1.
        + iModIntro. iIntros (t) "Hwp". iApply wpi_clear_mask_false. iMod "Hwp". iModIntro.
          pclearbot. iApply "Hwp". iPureIntro. apply H1.
  Qed.

  Theorem demonicH_adequate (t : itree (demonicE +' E) R) (t' : itree E R) M Φ :
    demonic_instantiates t t' →
    WPi t @ demonicH ⊕ H; M {{ Φ }} -∗
    WPi t' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hinstant) "Hwp". rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iApply demonicH_adequate'.
    - pclearbot. apply Hinstant.
    - done.
  Qed.
End demonic_adequacy.

(*
Lemma fupd_soundness `{!invGpreS Σ} E1 E2 (P : iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS_gen hlc Σ}, ⊢ |={E1,E2}=> P) → ⊢ P.
Proof.
  intros Hfupd. apply fupd_soundness_no_lc with (E1 := E1) (E2 := E2) (m := 0).
  - done.
  - iIntros (Hinv) "Hcred". iApply Hfupd.
Qed.

(* TODO: Move above demonic_adequacy to signify correct order of application. *)
Section demonic_angelic_adequacy.
  Context {R : Type}.

  Variant angel_winsF
    (angel_wins : itree (angelicE +' demonicE) R → (R → Prop) → Prop)
    : itree' (angelicE +' demonicE) R → (R → Prop) → Prop :=
  | Returns (Q : R → Prop) r :
    Q r →
    angel_winsF angel_wins (RetF r) Q
  | AngelicChoice Q A k a :
    angel_wins (k a) Q →
    angel_winsF angel_wins (VisF (inl1 (EAngelic A)) k) Q
  | DemonicChoice Q A k :
    (∀ a, angel_wins (k a) Q) →
    angel_winsF angel_wins (VisF (inr1 (EDemonic A)) k) Q
  | Steps Q t :
    angel_wins t Q →
    angel_winsF angel_wins (TauF t) Q.
  Hint Constructors angel_winsF : iris_itree.
  Definition angel_wins_
    (angel_wins : itree (angelicE +' demonicE) R → (R → Prop) → Prop)
    : itree (angelicE +' demonicE) R → (R → Prop) → Prop :=
    λ t Q, angel_winsF angel_wins (observe t) Q.

  Lemma angel_winsF_mono angel_wins angel_wins' t t' :
    angel_wins <2= angel_wins' →
    angel_winsF angel_wins  t t' →
    angel_winsF angel_wins' t t'.
  Proof.
    intros Hleq HinterleavesF. destruct HinterleavesF; eauto with iris_itree.
  Qed.
  Lemma angel_wins__mono :
    monotone2 angel_wins_.
  Proof.
    rewrite /monotone3 /demonic_instantiates_. intros ??????. by eapply angel_winsF_mono.
  Qed.
  Hint Resolve demonic_instantiates__mono : paco.

  Definition angel_wins : itree (angelicE +' demonicE) R → (R → Prop) → Prop :=
    paco2 angel_wins_ bot2.

  Theorem demonicH_angelicH_adequate' `{!invGpreS Σ} (t : itree (angelicE +' demonicE) R) (Q : R → Prop) :
    (∀ `{Hinv : invGS_gen hlc Σ}, sat WPi t @ angelicH ⊕ demonicH; ⊤ {{ v, ⌜ Q v ⌝ }}) →
    angel_wins t Q.
  Proof.
    generalize t. pcofix CIH. clear t. intros t Hwp. pfold. rewrite /angel_wins_.
    destruct (observe t) eqn:Heq.
    - constructor. symmetry in Heq. apply ret_observe_eqit in Heq.
      setoid_rewrite <- Heq in Hwp. setoid_rewrite <- wpi_ret' in Hwp.
      apply fupd_soundness in Hwp. apply pure_soundness in Hwp.
      * done.
      * apply _.
    - constructor. symmetry in Heq. apply tau_observe_eqit in Heq.
      setoid_rewrite <- Heq in Hwp. setoid_rewrite <- wpi_tau' in Hwp.
      apply fupd_soundness in Hwp. apply pure_soundness in Hwp.
      * done.
      * apply _.
End angelic_adequacy.
*)
