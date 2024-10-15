From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import itree wpi trace handler exec.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Eqit.

(** Step events. The main application of this event type is for doing
termination insensitive reasoning in spite of our [WPi] being defined as a
least fixpoint (and thus being termination sensitive "by default"). *)
Variant stepE : Type → Type :=
  (** An event that marks that a step has been taken. This can be thought of as
  the semantic analogue of the logical later modality [▷ P]. *)
  | EStep : stepE ().

Definition step `{stepE -< E} : itree E () :=
  trigger EStep.

Lemma step_to_translate {E1 E2} (HE1 : stepE -< E1) (HE2 : stepE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate step Hin step.
Proof. move => ?. rewrite /step. by apply trigger_to_translate. Qed.
Global Hint Resolve step_to_translate : itree_auto.

Global Instance AnswerEqDecision_stepE :
  AnswerEqDecision stepE.
Proof. intros A [] [] []. by left. Qed.

(** Choice of modality for handling [EStep]. *)
Variant later_modality : Set :=
  (** No modality. *)
  | Identity
  (** Later modality [▷ P]. *)
  | Later.

Section lat.
  Context `{Σ : gFunctors}.

  (** Apply a modality [later_modality] to an [iProp]. *)
  Definition lat (m : later_modality) (P : iProp Σ) : iProp Σ :=
    match m with
    | Identity => P
    | Later => ▷ P
    end.

  Lemma lat_mono m (Φ Ψ : iProp Σ) :
    (Φ -∗ Ψ) -∗
    lat m Φ -∗ lat m Ψ.
  Proof.
    iIntros "Hwand HΦ". destruct m; by iApply "Hwand".
  Qed.

  Lemma lat_intro m (Φ : iProp Σ) :
    Φ -∗
    lat m Φ.
  Proof.
    iIntros "HΦ". by destruct m.
  Qed.

  Global Instance lat_proper_undirectional m :
    Proper ((⊢) ==> (⊢)) (lat m).
  Proof.
    iIntros (Φ1 Φ2 HΦ) "HΦ1".
    iApply lat_mono; last done.
    by iDestruct HΦ as "Hwand".
  Qed.

  Global Instance lat_proper_bidirectional m :
    Proper ((⊣⊢) ==> (⊣⊢)) (lat m).
  Proof.
    iIntros (Φ1 Φ2 HΦ).
    iSplit.
    - iApply lat_proper_undirectional. rewrite HΦ //.
    - iApply lat_proper_undirectional. rewrite HΦ //.
  Qed.
End lat.

Section handler.
  Context {Σ : gFunctors}.

  Program Definition stepH (m : later_modality) : iHandler Σ stepE :=
    IHandler (λ A e,
      match e with
      | EStep => λ Φ _, lat m (Φ ())
      end
    )%I _.
  Next Obligation.
    iIntros (???????) "HΦwand _". destruct e.
    iIntros "HΦ". by iApply (lat_mono with "HΦwand").
  Qed.
  Global Instance stepH_Sequential m :
    Sequential (stepH m).
  Proof.
    by iIntros (A [] Φ s) "HH".
  Qed.

  Global Instance wandH_stepH :
    wandH (stepH Identity) (stepH Later).
  Proof. iIntros (A [] Φ s) "Hlat". by simpl. Qed.
End handler.

Section wpi.
  Context `{!invGS_gen hlc Σ} {E : Type → Type} {H : iHandler Σ E} {m : later_modality}.
  Context `{stepE -< E} `{inH Σ stepE E (stepH m) H}.

  Lemma wpi_step M (Φ : () → iProp Σ) :
    (lat m (|={M}=> Φ ())) -∗
    WPi step @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply is_inH. simpl. iApply (lat_mono with "[Hfupd]"); last done.
    iIntros "HΦ". iApply wpi_ret. by iMod "Hfupd".
  Qed.
End wpi.

Section ifn.
  (* TODO: Use consistent convention with having definitions outside sections. *)

  (** Return type for executions that timeout because too many [EStep]s were
  encountered. *)
  Variant step_exhausted : Set := StepExhausted.

  Definition step_ifn_loop {R E} (n : option nat) (t : itree (stepE +' E) R) : itree E ((option nat * itree (stepE +' E) R) + (R + step_exhausted)) :=
      match observe t with
      | RetF r => Ret (inr (inl r))
      | TauF t => Ret (inl (n, t))
      | VisF (inl1 e) k =>
          if bool_decide (n = Some 0) then
            Ret (inr (inr StepExhausted))
          else
            match e in stepE T return (T → _) → _ with
              EStep => λ k, Ret (inl ((λ x, x - 1) <$> n, k ()))
            end k
      | VisF (inr1 e) k => ITree.map (λ x, inl (n, k x)) (trigger e)
      end.

  (** Interpretation function for [stepE]. It replaces [EStep]s by [Tau]s. If
  [n = Some n'], it will truncate after [n'] of [EStep]s, that is, put
  [Ret (inr StepExhausted)] in branches where [n'] laters have been
  encountered. *)
  Definition step_ifn {R E} (n : option nat) (t : itree (stepE +' E) R) : itree E (R + step_exhausted) :=
    ITree.iter (λ '(n, t), step_ifn_loop n t) (n, t).

  Lemma step_ifn_unfold R E n (t : itree (stepE +' E) R) :
    step_ifn n t ≈ r ← step_ifn_loop n t;
     match r with
     | inl (n, t) => step_ifn n t
     | inr r => Ret r
     end.
  Proof. rewrite /step_ifn unfold_iter. f_equiv => -[[??]|//]. by rewrite tau_eutt. Qed.

  (** Interpretation relation for [stepE] obtained from turning [step_ifn]
  into a relation. *)
  Definition step_irel {R E} (n : option nat) (t : itree (stepE +' E) R) (t' : itree E (R + step_exhausted)) : Prop :=
    t' = step_ifn n t.

  Lemma step_ifn_irel {R E} (n : option nat) (t : itree (stepE +' E) R) :
    step_irel n t (step_ifn n t).
  Proof. reflexivity. Qed.
End ifn.

Section adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS Σ} {H : iHandler Σ E}.

  (** Adequacy for [stepH]. *)
  Theorem step_adequacy_empty (t : itree (stepE +' E) R) t' m Φ n `{!Sequential H}:
    step_irel n t t' →
    (* When the [Later] modality is enabled, we need [£ n] so that we can strip
    [n] laters in the goal. *)
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    WPi t @ stepH m ⊕ H; ∅ {{ Φ }} -∗
    WPi t' @ H; ∅ {{ r,
      match r with
      | inl r => Φ r
      (* We can only exhaust laters if we set a timeout in the first place. *)
      | inr StepExhausted => ⌜is_Some n⌝
      end
    }}.
  Proof.
    iIntros (->) "Hlc Hwp". iRevert (n) "Hlc".
    iRevert (t Φ) "Hwp". iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". iIntros (n) "Hlc".
      rewrite step_ifn_unfold /step_ifn_loop/=. wpi_norm. by iApply wpi_ret'.
    - iIntros "!>" (Φ t) "Hwp". iIntros (n) "Hlc".
      iEval (rewrite step_ifn_unfold /step_ifn_loop/=). wpi_norm/=.
      iApply wpi_update. iMod "Hwp". iModIntro. by iApply "Hwp".
    - iIntros "!>" (Φ A [[]|e] k) "HH"; iIntros (n) "Hlc".
      + iEval (rewrite step_ifn_unfold /step_ifn_loop/=).
        case_bool_decide; wpi_norm/=.
        * iApply wpi_ret'. iModIntro. iPureIntro. naive_solver.
        * iApply wpi_update. iMod "HH". destruct n; simplify_eq/=.
          -- destruct m.
             ++ iApply wpi_wand; last iApply "HH".
                ** iIntros (r) "H". case_match; first done. by case_match.
                ** iIntros "!>" ([=]).
              ++ destruct n => //.
                 iDestruct ("Hlc" with "[//]") as "[? ?]". iApply (lc_fupd_elim_later with "[$]").
                 iModIntro. simpl. replace (n - 0) with n by lia.
                 iApply wpi_wand; last iApply "HH"; eauto.
                 iIntros (r) "H". case_match; first done. by case_match.
          -- destruct m; last first. { iDestruct ("Hlc" with "[//]") as "[]". }
             iModIntro. by iApply "HH".
      + iEval (rewrite step_ifn_unfold /step_ifn_loop/=).
        rewrite /ITree.map. wpi_norm/=.
        iApply wpi_bind. iApply wpi_trigger. iMod "HH". iModIntro.
        iDestruct (is_seq with "HH") as "HH".
        iApply (ihandler_mono with "[Hlc]"); last done. 2: by iIntros "!>" (??).
        iIntros (a) "Hwp".
        iModIntro. by iApply "Hwp".
  Qed.

  (* TODO: can we get this?
  Theorem step_adequacy (t : itree (stepE +' E) R) m Φ n M `{!Sequential H} :
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    WPi t @ stepH m ⊕ H; M {{ Φ }} -∗
    WPi step_ifn n t @ H; M {{ r,
      match r with
      | inl r => Φ r
      | inr StepExhausted => ⌜is_Some n⌝
      end
    }}.
  Proof.
    iIntros "Hlc Hwp".
    rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iDestruct (step_adequacy_empty with "Hlc Hwp") as "Hwp".
    iApply wpi_wand; last done. iIntros (r). destruct r.
    - eauto.
    - (* Where do we get the mask from? *)
  Abort.
   *)
End adequacy.

Section trace.
  Context {R : Type} {E : Type → Type}.

  (** Interpret away [stepE] events in [trcae (stepE +' E)]. Akin to the
  definition of [step_ifn], if [n = Some n'] and more than [n'] [EStep]s are
  reached, [inr StepExhausted] is returned to mark that a timeout has
  happened. *)
  Fixpoint interp_tr_step (n : option nat) (tr : trace (stepE +' E) R) : trace E (R + step_exhausted) :=
    match tr with
    | TRet r => TRet (inl r)
    | TVis A (inl1 EStep) a k =>
        match n with
        | Some 0 => TRet (inr StepExhausted)
        | Some (S n') => interp_tr_step (Some n') k
        | None => interp_tr_step None k
        end
    | TVis A (inr1 e) a k => TVis A e a (interp_tr_step n k)
    | TVisEmpty A (inr1 e) => TVisEmpty A e
    | _ => TCut
    end.

  (** Intermediate statement for induction. *)
  Lemma step_trace' (tr : trace (stepE +' E) R) n t :
    is_trace tr t →
    is_trace (interp_tr_step (Some n) tr) (step_ifn (Some n) t).
  Proof.
    intros Htr. rewrite /is_trace in Htr.
    revert t tr Htr. induction n; intros t tr Htr.
    - remember (observe t) as ot. revert t Heqot.
      induction Htr; intros t_ Heqot; simplify_obs.
      * constructor.
      * destruct e as [e|e]; first destruct e as [].
        + rewrite step_ifn_unfold. rewrite /step_ifn_loop /=.
          simpl_itree. constructor.
        + simpl. rewrite step_ifn_unfold. rewrite /step_ifn_loop. simpl_itree.
          rewrite bind_trigger. constructor. by apply IHHtr.
      * destruct e as [e|e].
        + destruct e. constructor.
        + rewrite step_ifn_unfold /step_ifn_loop /=. simpl_itree. rewrite bind_trigger.
          by constructor.
      * constructor.
      * rewrite step_ifn_unfold /step_ifn_loop /=. simpl_itree. by apply IHHtr.
    - remember (observe t) as ot. revert t Heqot IHn.
      induction Htr; intros t_ Heqot IHn; simplify_obs.
      * constructor.
      * destruct e as [e|e]; first destruct e as [].
        + rewrite step_ifn_unfold. rewrite /step_ifn_loop /=.
          simpl_itree. replace (n - 0) with n by lia. apply IHn.
          by destruct a.
        + simpl. rewrite step_ifn_unfold. rewrite /step_ifn_loop. simpl_itree.
          rewrite bind_trigger. constructor. by apply IHHtr.
      * destruct e as [e|e].
        + destruct e. constructor.
        + rewrite step_ifn_unfold /step_ifn_loop /=. simpl_itree. rewrite bind_trigger.
          by constructor.
      * constructor.
      * rewrite step_ifn_unfold /step_ifn_loop /=. simpl_itree. by apply IHHtr.
  Qed.
  (** Traces are preserved by [step_ifn]. *)
  Lemma step_ifn_trace (tr : trace (stepE +' E) R) n t :
    is_trace tr t →
    is_trace (interp_tr_step n tr) (step_ifn n t).
  Proof.
    intros Htr. destruct n; first by apply step_trace'.
    rewrite /is_trace in Htr.
    remember (observe t) as ot. revert t Heqot.
    induction Htr; intros t_ Heqot; simplify_obs.
    * constructor.
    * destruct e as [e|e]; first destruct e as [].
      + rewrite step_ifn_unfold. rewrite /step_ifn_loop /=.
        simpl_itree. apply IHHtr. by destruct a.
      + simpl. rewrite step_ifn_unfold. rewrite /step_ifn_loop. simpl_itree.
        rewrite bind_trigger. constructor. by apply IHHtr.
    * destruct e as [e|e].
      + destruct e. constructor.
      + rewrite step_ifn_unfold /step_ifn_loop /=. simpl_itree. rewrite bind_trigger.
        by constructor.
    * constructor.
    * rewrite step_ifn_unfold /step_ifn_loop /=. simpl_itree. by apply IHHtr.
  Qed.

  (** A version of [step_ifn_trace] that looks more like other lemmata such as
  [demonic_trace]. *)
  Lemma step_trace (tr : trace (stepE +' E) R) n t :
    is_trace tr t →
    ∃ t', step_irel n t t' ∧ is_trace (interp_tr_step n tr) t'.
  Proof.
    intros Htr. apply step_ifn_trace with (n := n) in Htr.
    exists (step_ifn n t). by split.
  Qed.
End trace.

(** Definitions for exec *)
Local Unset Program Cases.

Program Definition stepEH lat : seHandler stepE :=
  SEHandler nat (λ A e s, match e with | EStep =>
     λ C, ∃ s', s = S s' ∧ C tt (if lat is Later then s' else s) end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance stepEH_adequate {Σ} `{!invGS Σ} lat :
  seHandlerAdequate (stepH lat) (stepEH lat) := {| sehandler_inv s := £ s |}.
Next Obligation.
  move => /= ?? lat ?????? HP.
  iIntros "Hp Hs". case_match.
  destruct HP as [? [??]]; subst.
  destruct lat => /=.
  - iModIntro. by iFrame.
  - rewrite lc_succ. iDestruct "Hs" as "[Hl $]". iApply (lc_fupd_elim_later with "[$]").
    iModIntro. by iFrame.
Qed.
