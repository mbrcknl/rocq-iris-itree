From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import axioms.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.bi Require Import fixpoint.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import ITree.
From ITree Require Import Basics.Monad.

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
  Context `{!invGS_gen HasNoLc Σ}.

  Lemma wpi_angelic {R A} k M (Φ : R → iProp Σ) :
    (∃ a, ▷ WPi k a @ H; M {{ Φ }}) -∗
    WPi (vis (EAngelic A) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "[%a Hwp]". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /angelicH. iExists a. iNext.
    iEval (rewrite -wpi_update). iMod "Hfupd". rewrite wpi_clear_mask //.
  Qed.
End wp_angelic.

Section wp_demonic.
  Context {E : Type → Type} `{H : iHandler Σ E} `{demonicE -< E} `{inH Σ demonicE E demonicH H}.
  Context `{!invGS_gen HasNoLc Σ}.

  Lemma wpi_demonic {R A} k M (Φ : R → iProp Σ) :
    (∀ a, ▷ WPi k a @ H; M {{ Φ }}) -∗
    WPi (vis (EDemonic A) k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /demonicH. iIntros (a). iNext.
    iEval (rewrite -wpi_update). iMod "Hfupd". rewrite wpi_clear_mask //.
  Qed.
End wp_demonic.

Section demonic_adequacy.
  Context {E : Type → Type} `{H : iHandler Σ E} {R : Type} `{!invGS_gen HasNoLc Σ}.

  Variant demonic_instantiatesF
    (demonic_instantiates : itree (demonicE +' E) R → itree E R → Prop)
    : itree' (demonicE +' E) R → itree' E R → Prop :=
  | DInstantiate A (a : A) k k' :
    (∀ a, demonic_instantiates (k a) (k' a)) →
    demonic_instantiatesF demonic_instantiates (VisF (inl1 (EDemonic A)) k) (TauF (k' a))
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

  Theorem demonicH_adequate' (t : itree (demonicE +' E) R) (t' : itree E R) Φ :
    demonic_instantiates t t' →
    WPi t @ demonicH ⊕ H; ∅ {{ Φ }} -∗
    WPi t' @ H; ∅ {{ Φ }}.
  Proof.
    iIntros (Hinstant) "Hwp". iLöb as "IH" forall (t t' Hinstant Φ).
    punfold Hinstant. inversion Hinstant as
      [A a k k' Hinstant' Ht Ht'
      |r Ht Ht'
      |t_next t_next' Hinstant' Ht Ht'
      |A e k k' Hinstant' Ht Ht'].
    - apply vis_observe_eqit in Ht as <-. apply tau_observe_eqit in Ht' as <-.
      rewrite -wpi_vis' -wpi_tau' wpi_update_post. iMod "Hwp". iModIntro. simpl. iNext. iApply "IH".
      * pclearbot. iPureIntro. apply Hinstant'.
      * rewrite  -wpi_update_post. iApply "Hwp".
    - apply ret_observe_eqit in Ht as <-. apply ret_observe_eqit in Ht' as <-. rewrite -!wpi_ret' //.
    - apply tau_observe_eqit in Ht as <-. apply tau_observe_eqit in Ht' as <-. rewrite -!wpi_tau'.
      iMod "Hwp". iModIntro. iNext. iApply "IH".
      * pclearbot. iPureIntro. apply Hinstant'.
      * done.
    - apply vis_observe_eqit in Ht as <-. apply vis_observe_eqit in Ht' as <-.
      rewrite -!wpi_vis'. iMod "Hwp". iModIntro. iApply ihandler_mono; last done.
      * iIntros (a) "Hwp". iNext. rewrite !wpi_update_post. iApply "IH".
        + pclearbot. iPureIntro. apply Hinstant'.
        + done.
      * iModIntro. iIntros (a) "Hwp". iNext.
        rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask). iApply "IH".
        + pclearbot. iPureIntro. apply Hinstant'.
        + done.
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

(* TODO: Move above demonic_adequacy to signify correct order of application. *)
Section angelic_adequacy.
  Context {E : Type → Type} `{H : iHandler Σ E} {R : Type} `{!invGS_gen HasNoLc Σ}.

  Variant angelic_instantiatesF
    (angelic_instantiates : itree (angelicE +' E) R → itree E R → Prop)
    : itree' (angelicE +' E) R → itree' E R → Prop :=
  | AInstantiate A (a : A) k k' :
    (∀ a, angelic_instantiates (k a) (k' a)) →
    angelic_instantiatesF angelic_instantiates (VisF (inl1 (EAngelic A)) k) (TauF (k' a))
  | AReturns r :
    angelic_instantiatesF angelic_instantiates (RetF r) (RetF r)
  | ASteps t_next t_next' :
    angelic_instantiates t_next t_next' →
    angelic_instantiatesF angelic_instantiates (TauF t_next) (TauF t_next')
  | AEmits A (e : E A) k k' :
    (∀ a, angelic_instantiates (k a) (k' a)) →
    angelic_instantiatesF angelic_instantiates (VisF (inr1 e) k) (VisF e k').
  Hint Constructors angelic_instantiatesF : iris_itree.
  Definition angelic_instantiates_
    (angelic_instantiates : itree (angelicE +' E) R → itree E R → Prop)
    : itree (angelicE +' E) R → itree E R → Prop :=
    λ t t', angelic_instantiatesF angelic_instantiates (observe t) (observe t').

  Lemma angelic_instantiatesF_mono angelic_instantiates angelic_instantiates' t t' :
    angelic_instantiates <2= angelic_instantiates' →
    angelic_instantiatesF angelic_instantiates t t' →
    angelic_instantiatesF angelic_instantiates' t t'.
  Proof.
    intros Hleq HinterleavesF. destruct HinterleavesF; eauto with iris_itree.
  Qed.
  Lemma angelic_instantiates__mono :
    monotone2 angelic_instantiates_.
  Proof.
    rewrite /monotone3 /angelic_instantiates_. intros ??????. by eapply angelic_instantiatesF_mono.
  Qed.
  Hint Resolve angelic_instantiates__mono : paco.

  Definition angelic_instantiates : itree (angelicE +' E) R → itree E R → Prop :=
    paco2 angelic_instantiates_ bot2.

  Theorem angelicH_adequate' (t : itree (angelicE +' E) R) Φ :
    WPi t @ angelicH ⊕ H; ∅ {{ Φ }} -∗
    (∃ t', ⌜angelic_instantiates t t'⌝ ∧ WPi t' @ H; ∅ {{ Φ }}).
  Proof.
    iIntros "Hwp". iLöb as "IH" forall (t Φ).
    destruct (observe t) as [r|A e k|t'] eqn:Hobserve.
    - iExists (Ret r). iSplit.
      * iPureIntro. pfold. rewrite /angelic_instantiates_ Hobserve. simpl. constructor.
      * symmetry in Hobserve. apply ret_observe_eqit in Hobserve as <-. rewrite -!wpi_ret' //.
    - symmetry in Hobserve. apply tau_observe_eqit in Hobserve as Heqit. rewrite <- Heqit.
      rewrite -!wpi_tau'. iMod "Hwp". iModIntro. iNext. iDestruct ("IH" with "Hwp") as "[%t' [%Hinstant Hwp]]". iApply "Hwp".

      iExists (Tau _). iSplit.
      * shelve.
      * symmetry in Hobserve. apply tau_observe_eqit in Hobserve as <-.
        rewrite -!wpi_tau'. iMod "Hwp". iModIntro. iNext. iDestruct ("IH" with "Hwp") as "[%t' [%Hinstant Hwp]]". iApply "Hwp".
        iApply wpi_tau. iNext. 
        iPureIntro. pfold. rewrite /angelic_instantiates_ Hobserve. simpl. constructor.
    inversion (observe t) as [A].
    punfold Hinstant. inversion Hinstant as [A a k k' Hinstant' Ht Ht'|A e k k' Hinstant' Ht Ht'].
    - apply vis_observe_eqit in Ht as <-. apply tau_observe_eqit in Ht' as <-.
      rewrite -wpi_vis' -wpi_tau' wpi_update_post. iMod "Hwp". iModIntro. simpl. iNext. iApply "IH".
      * pclearbot. iPureIntro. apply Hinstant'.
      * rewrite  -wpi_update_post. iDestruct "Hwp" as "[%a Hwp]". iApply "Hwp".
    - apply vis_observe_eqit in Ht as <-. apply vis_observe_eqit in Ht' as <-.
      rewrite -!wpi_vis'. iMod "Hwp". iModIntro. iApply ihandler_mono; last done.
      * iIntros (a) "Hwp". iNext. rewrite !wpi_update_post. iApply "IH".
        + pclearbot. iPureIntro. apply Hinstant'.
        + done.
      * iModIntro. iIntros (a) "Hwp". iNext.
        rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask). iApply "IH".
        + pclearbot. iPureIntro. apply Hinstant'.
        + done.
  Qed.
  Theorem angelicH_adequate (t : itree (angelicE +' E) R) (t' : itree E R) M Φ :
    angelic_instantiates t t' →
    WPi t @ angelicH ⊕ H; M {{ Φ }} -∗
    WPi t' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hinstant) "Hwp". rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iApply angelicH_adequate'.
    - pclearbot. apply Hinstant.
    - done.
  Qed.
End angelic_adequacy.
