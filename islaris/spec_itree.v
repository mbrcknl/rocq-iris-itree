From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree Require Import trace.
From ITree Require Import ITree.
From Paco Require Import paco.
From Paco Require Import paco3.
From ITree Require Import Eqit.
Require Import isla.spec.
Require Import isla.opsem.
Require Import isla.ghost_state.
Require Import isla.lifting.

Inductive specE : Type → Type :=
  | EEmitLabel (κ : seq_label) : specE unit.

Definition emit_label `{!specE -< E} (κ : seq_label) : itree E unit :=
  trigger (EEmitLabel κ).

Lemma emit_label_to_translate {E1 E2} κ (HE1 : specE -< E1) (HE2 : specE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (emit_label κ) Hin (emit_label κ).
Proof. move => ?. rewrite /emit_label. by apply trigger_to_translate. Qed.
Global Hint Resolve emit_label_to_translate : itree_auto.

Section handler.
  Context {Σ : gFunctors} `{!heapG Σ}.

  Program Definition specH : iHandler Σ specE :=
    IHandler (λ A e,
        match e with
        | EEmitLabel κ => λ Φ _,
            ∃ Pκs, ⌜Pκs [κ]⌝ ∗ spec_trace Pκs ∗
              (spec_trace (λ κs, Pκs (κ::κs)) -∗ Φ tt)
        end)%I _.
  Next Obligation.
    iIntros (? e ????) "HΦ ?". destruct e => //.
    iDestruct 1 as (??) "[? Hcont]".
    iExists _. iFrame. iSplit; [done|]. iIntros "Hspec".
    iApply "HΦ". by iApply "Hcont".
  Qed.
  Global Instance specH_Sequential :
    Sequential specH.
  Proof.
    iIntros (A e Φ s) "HH". by destruct e.
  Qed.
End handler.

Section wp_spec.
  Context {E : Type → Type} `{!islaG Σ}.
  Context {H : iHandler Σ E} `{!specE -< E} `{!inH specH H}.

  Lemma wpi_emit_label {R} (k : itree E R) Pκs κ (M : coPset) (Φ : R → iProp Σ) :
    Pκs [κ] →
    spec_trace Pκs -∗
    (spec_trace (λ κs, Pκs (κ::κs)) -∗ WPi k @ H; M {{ Φ }}) -∗
    WPi emit_label κ;; k @ H; M {{ Φ }}.
  Proof using Type*.
    iIntros (HPκs) "Hspec Hwp". iApply wpi_bind. iApply wpi_trigger => /=.
    iApply fupd_mask_intro; first set_solver. iIntros "Hfupd".
    iExists _. iFrame. iSplit; [done|]. iIntros "Hspec".
    iMod "Hfupd". iModIntro. by iApply "Hwp".
  Qed.
End wp_spec.

Section specH_adequacy.
  Context {E : Type → Type} `{!islaG Σ}.
  Context {H : iHandler Σ E} `{!specE -< E} `{!inH specH H}.
  Context {R : Type}.
  Context (Pκs : list seq_label → Prop).

  Context `{!Sequential H}.

  Variant assume_specF
    (assume_spec : list seq_label → itree (specE +' E) R → itree E R → Prop)
    : list seq_label
    → itree' (specE +' E) R
    → itree' E R
    → Prop :=
  | ForwardRet κs r :
    assume_specF assume_spec κs (RetF r) (RetF r)
  | ForwardTau κs t t' :
    assume_spec κs t t' →
    assume_specF assume_spec κs (TauF t) (TauF t')
  | ForwardVis κs A e k k' :
    (∀ a : A, assume_spec κs (k a) (k' a)) →
    assume_specF assume_spec κs (VisF (inr1 e) k) (VisF e k')
  | EmitLabel κs κ k t :
    (** Key point: We can assume that the trace fulfills the spec,
    otherwise t is unconstrained (and can be spin or ub). *)
    (Pκs (κs ++ [κ]) → assume_spec (κs ++ [κ]) (k tt) t) →
    assume_specF assume_spec κs (VisF (inl1 (EEmitLabel κ)) k) (TauF t).

  Hint Constructors assume_specF : iris_itree.
  Definition assume_spec_
    (assume_spec : list seq_label → itree (specE +' E) R → itree E R → Prop)
    : list seq_label
    → itree (specE +' E) R
    → itree E R
    → Prop :=
    λ s t t', assume_specF assume_spec s (observe t) (observe t').

  Lemma assume_specF_mono assume_spec assume_spec' s t t' :
    assume_spec <3= assume_spec' →
    assume_specF assume_spec  s t t' →
    assume_specF assume_spec' s t t'.
  Proof.
    intros Hleq Hassume_specF. destruct Hassume_specF; eauto with iris_itree.
  Qed.
  Lemma assume_spec__mono :
    monotone3 assume_spec_.
  Proof.
    rewrite /monotone3 /assume_spec_. intros. by eapply assume_specF_mono; last done.
  Qed.
  Hint Resolve assume_spec__mono : paco.

  Definition assume_spec :
    list seq_label → itree (specE +' E) R → itree E R → Prop :=
    paco3 assume_spec_ bot3.

  Global Instance assume_spec_proper_unilateral :
    Proper ((=) ==> eqit (=) false false ==> eqit (=) false false ==> impl) assume_spec.
  Proof.
    pcofix CIH.
    intros s s' <- t1 t2 Ht t1' t2' Ht' Hassume_spec.
    pfold. rewrite /assume_spec_.
    punfold Ht. punfold Ht'. punfold Hassume_spec. rewrite /assume_spec_ in Hassume_spec.
    destruct Ht, Ht'; try discriminate; try inversion Hassume_spec.
    - simplify_eq. inversion Hassume_spec. constructor.
    - constructor. pclearbot. simplify_eq. right. eapply CIH; first reflexivity.
      * apply REL.
      * done.
      * clear REL REL0. by pclearbot.
    - do 2 simplify_K. pclearbot. eapply EmitLabel. right. eapply CIH; first reflexivity.
      + apply REL.
      + done.
      + clear REL REL0. ospecialize* H3; [done|]. by pclearbot.
    - do 2 simplify_K. pclearbot. inversion Hassume_spec. constructor. right.
      destruct (H4 a) as [H4'|X]; [|contradiction X]. simplify_K.
      eapply CIH; last apply H4'; first reflexivity.
      * apply REL.
      * apply REL0.
  Qed.
  Global Instance assume_spec_proper :
    Proper (pointwise_relation (list seq_label) (eqit (=) false false ==> eqit (=) false false ==> (↔))%signature) assume_spec.
  Proof.
    intros s t1 t2 Ht t1' t2' Ht'.
    split; rewrite Ht Ht' //.
  Qed.

  Definition spec_ctx (κs : list seq_label) : iProp Σ :=
    ∃ Pκs', ⌜Pκs' ⊆ λ κs', Pκs (κs ++ κs')⌝ ∗
    spec_trace_raw Pκs'.

  Lemma spec_ctx_cons κ κs (Pκs' : spec) :
    Pκs' [κ] →
    spec_ctx κs -∗
    spec_trace Pκs' ==∗
    ⌜Pκs (κs ++ [κ])⌝ ∗ spec_ctx (κs ++ [κ]) ∗ spec_trace (λ κs, Pκs' (κ::κs)).
  Proof.
    move => Hκ.
    iDestruct 1 as (Pκs'' Hspec) "Hsc".
    rewrite spec_trace_eq. iDestruct 1 as (Pκs''' HPκs''') "Hs".
    iDestruct (spec_trace_raw_agree with "Hsc Hs") as %HPκs.
    iMod (spec_trace_raw_update with "Hsc Hs") as "[Ht ?]".
    iModIntro. iFrame. repeat iSplit; iPureIntro.
    - spec_solver.
    - apply reflexivity.
    - move => ?. rewrite -app_assoc -cons_middle. spec_solver.
  Qed.

  (** A technical version of adequacy, amenable to induction. See corollary below for a
  more meaningful statement. *)
  Theorem wpi_spec_ind κs t t' M Φ :
    assume_spec κs t t' →
    spec_ctx κs -∗
    WPi t @ specH ⊕ H; ∅ {{ v, |={∅, M}=> Φ v }} -∗
    WPi t' @ H; ∅ {{ v, |={∅, M}=> Φ v }}.
  Proof using Type*.
    iIntros "%Hassume Hspec Hwp".
    pose (G := (λ (t : itree (specE +' E) R) (Φ : R -d> iPropO Σ),
      ∀ t' κs Ψ,
        ⌜assume_spec κs t t'⌝ -∗
        spec_ctx κs -∗
        (∀ v, Φ v -∗ |={∅, M}=> Ψ v) -∗
        WPi t' @ H; ∅ {{ v, |={∅, M}=> Ψ v }}
    )%I).
    iApply (wpi_iter' (H := specH ⊕ H) G with "[] [] [] [Hwp] [] Hspec").
    - solve_proper.
    - clear. iModIntro. iIntros (Φ r) "HΦ". iIntros (t s Ψ Hassume) "Hspec HΨ".
      punfold Hassume. inversion Hassume. simplify_obs.
      iApply wpi_ret. iMod "HΦ". iMod ("HΨ" with "HΦ") as "HΨ". iModIntro. iFrame.
    - clear. iModIntro. iIntros (Φ t) "HG". rewrite /G /=.
      iIntros (t' s Ψ Hassume) "Hspec Hwand".
      punfold Hassume. inversion Hassume. simplify_obs. rewrite -wpi_tau.
      iApply wpi_update. iMod "HG". iModIntro. iApply ("HG" with "[] Hspec Hwand").
      by pclearbot.
    - clear Φ t' Hassume κs. iModIntro. iIntros (Φ A e k) "HH".
      iEval (rewrite /G /=). iIntros (t' κs Ψ Hassume) "Hspec Hwand".
      punfold Hassume. inversion Hassume.
      * simplify_K. simplify_obs. iApply wpi_vis. iMod "HH". simpl. iModIntro.
        iDestruct (is_seq with "HH") as "HH".
        iApply (ihandler_mono with "[Hspec Hwand]"); last done.
        + iIntros (a) "Hwp". iApply wpi_update_post.
          iApply ("Hwp" with "[] Hspec Hwand").
          iPureIntro. pclearbot. apply H3.
        + by iIntros "!>" (?) "?".
      * simplify_K. simplify_obs. simplify_K. simpl. rewrite -wpi_tau.
        iApply wpi_update. iMod "HH" as (??) "[Ht Hcont]".
        iMod (spec_ctx_cons with "Hspec Ht") as (?) "[Hspec Ht]"; [done|].
        iModIntro. iApply ("Hcont" with "Ht [%] Hspec Hwand").
        ospecialize* H3; [done|]. by pclearbot.
    - done.
    - done.
    - eauto.
  Qed.

  (** Adequacy for [specH ⊕ H]. *)
  (* TODO: naming of the lemma *)
  Theorem wpi_spec x1 x2 t t' M Φ :
    assume_spec [] t t' →
    spec_trace_raw x1 -∗
    spec_trace_raw x2 -∗
    (spec_trace Pκs -∗ WPi t @ specH ⊕ H; M {{ v, Φ v }}) -∗
    WPi t' @ H; M {{ v, Φ v }}.
  Proof using Type*.
    iIntros (Hassume) "Hr1 Hr2 Hcont". rewrite -wpi_clear_mask.
    iEval (rewrite -wpi_clear_mask).
    iMod (spec_trace_raw_update _ _ Pκs with "Hr1 Hr2") as "[Hr1 Hr2]".
    iMod ("Hcont" with "[Hr1]"). { rewrite spec_trace_eq. by iFrame. }
    iModIntro. iApply (wpi_spec_ind with "[Hr2] [$]"); [done|].
    by iFrame.
  Qed.
End specH_adequacy.
