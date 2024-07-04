From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import itree wpi trace handler.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Eqit.

(** Later events. The main application of this event type is for doing
termination insensitive reasoning in spite of our [WPi] being defined as a
least fixpoint (and thus being termination sensitive "by default"). *)
Variant laterE : Type → Type :=
  (** An event that marks that a step has been taken. This can be thought of as
  the semantic analogue of the logical later modality [▷ P]. *)
  | ELater : laterE ().

Definition step `{laterE -< E} : itree E () :=
  trigger ELater.

Lemma step_to_translate {E1 E2} (HE1 : laterE -< E1) (HE2 : laterE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate step Hin step.
Proof. move => ?. rewrite /step. by apply trigger_to_translate. Qed.
Global Hint Resolve step_to_translate : itree_auto.

Global Instance AnswerEqDecision_laterE :
  AnswerEqDecision laterE.
Proof. intros A [] [] []. by left. Qed.

(** Choice of modality for handling [ELater]. *)
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

  Program Definition laterH (m : later_modality) : iHandler Σ laterE :=
    IHandler (λ A e,
      match e with
      | ELater => λ Φ _, lat m (Φ ())
      end
    )%I _.
  Next Obligation.
    iIntros (???????) "HΦwand _". destruct e.
    iIntros "HΦ". by iApply (lat_mono with "HΦwand").
  Qed.
  Global Instance laterH_Sequential m :
    Sequential (laterH m).
  Proof.
    by iIntros (A [] Φ s) "HH".
  Qed.

  Global Instance wandH_laterH :
    wandH (laterH Identity) (laterH Later).
  Proof. iIntros (A [] Φ s) "Hlat". by simpl. Qed.
End handler.

Section wpi.
  Context `{!invGS_gen hlc Σ} {E : Type → Type} {H : iHandler Σ E} {m : later_modality}.
  Context `{laterE -< E} `{inH Σ laterE E (laterH m) H}.

  Lemma wpi_later M (Φ : () → iProp Σ) :
    (lat m (|={M}=> Φ ())) -∗
    WPi (trigger ELater) @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply is_inH. simpl. iApply (lat_mono with "[Hfupd]"); last done.
    iIntros "HΦ". iApply wpi_ret. by iMod "Hfupd".
  Qed.

  (* TODO: consistently use step vs trigger ELater and get rid of this
  or the previous lemma *)
  Lemma wpi_step M (Φ : () → iProp Σ) :
    (lat m (|={M}=> Φ ())) -∗
    WPi step @ H; M {{ Φ }}.
  Proof. exact: wpi_later. Qed.
End wpi.

Section ifn.
  (* TODO: Use consistent convention with having definitions outside sections. *)

  (** Return type for executions that timeout because too many [ELater]s were
  encountered. *)
  Variant later_exhausted : Set := LaterExhausted.

  Definition later_ifn_loop {R E} (n : option nat) (t : itree (laterE +' E) R) : itree E ((option nat * itree (laterE +' E) R) + (R + later_exhausted)) :=
      match observe t with
      | RetF r => Ret (inr (inl r))
      | TauF t => Ret (inl (n, t))
      | VisF (inl1 e) k =>
          if bool_decide (n = Some 0) then
            Ret (inr (inr LaterExhausted))
          else
            match e in laterE T return (T → _) → _ with
              ELater => λ k, Ret (inl ((λ x, x - 1) <$> n, k ()))
            end k
      | VisF (inr1 e) k => ITree.map (λ x, inl (n, k x)) (trigger e)
      end.

  (** Interpretation function for [laterE]. It replaces [ELater]s by [Tau]s. If
  [n = Some n'], it will truncate after [n'] of [ELater]s, that is, put
  [Ret (inr LaterExhausted)] in branches where [n'] laters have been
  encountered. *)
  Definition later_ifn {R E} (n : option nat) (t : itree (laterE +' E) R) : itree E (R + later_exhausted) :=
    ITree.iter (λ '(n, t), later_ifn_loop n t) (n, t).

  Lemma later_ifn_unfold R E n (t : itree (laterE +' E) R) :
    later_ifn n t ≈ r ← later_ifn_loop n t;
     match r with
     | inl nt => later_ifn nt.1 nt.2
     | inr r => Ret r
     end.
  Proof. rewrite /later_ifn unfold_iter. f_equiv => -[[??]|//]. by rewrite tau_eutt. Qed.
End ifn.

Section adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS Σ} {H : iHandler Σ E}.

  (** Adequacy for [laterH]. *)
  Theorem later_adequacy_empty (t : itree (laterE +' E) R) m Φ n `{!Sequential H}:
    (* When the [Later] modality is enabled, we need [£ n] so that we can strip
    [n] laters in the goal. *)
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    WPi t @ laterH m ⊕ H; ∅ {{ Φ }} -∗
    WPi later_ifn n t @ H; ∅ {{ r,
      match r with
      | inl r => Φ r
      (* We can only exhaust laters if we set a timeout in the first place. *)
      | inr LaterExhausted => ⌜is_Some n⌝
      end
    }}.
  Proof.
    iIntros "Hlc Hwp". iRevert (n) "Hlc".
    iRevert (t Φ) "Hwp". iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". iIntros (n) "Hlc".
      rewrite later_ifn_unfold /later_ifn_loop/=. wpi_norm. by iApply wpi_ret'.
    - iIntros "!>" (Φ t) "Hwp". iIntros (n) "Hlc".
      iEval (rewrite later_ifn_unfold /later_ifn_loop/=). wpi_norm/=.
      iApply wpi_update. iMod "Hwp". iModIntro. by iApply "Hwp".
    - iIntros "!>" (Φ A [[]|e] k) "HH"; iIntros (n) "Hlc".
      + iEval (rewrite later_ifn_unfold /later_ifn_loop/=).
        case_bool_decide; wpi_norm/=.
        * iApply wpi_ret'. iModIntro. iPureIntro. naive_solver.
        * iApply wpi_update. iMod "HH". destruct n; simplify_eq/=.
          -- destruct m.
             ++ iApply wpi_wand; last iApply "HH".
                ** iIntros (r) "H". destruct r; first done. by destruct l.
                ** iIntros "!>" ([=]).
              ++ destruct n => //.
                 iDestruct ("Hlc" with "[//]") as "[? ?]". iApply (lc_fupd_elim_later with "[$]").
                 iModIntro. simpl. replace (n - 0) with n by lia.
                 iApply wpi_wand; last iApply "HH"; eauto.
                 iIntros (r) "H". destruct r; first done. by destruct l.
          -- destruct m; last first. { iDestruct ("Hlc" with "[//]") as "[]". }
             iModIntro. by iApply "HH".
      + iEval (rewrite later_ifn_unfold /later_ifn_loop/=).
        rewrite /ITree.map. wpi_norm/=.
        iApply wpi_bind. iApply wpi_trigger. iMod "HH". iModIntro.
        iDestruct (is_seq with "HH") as "HH".
        iApply (ihandler_mono with "[Hlc]"); last done. 2: by iIntros "!>" (??).
        iIntros (a) "Hwp".
        iModIntro. by iApply "Hwp".
  Qed.

  (* TODO: can we get this?
  Theorem later_adequacy (t : itree (laterE +' E) R) m Φ n M `{!Sequential H} :
    (⌜m = Later⌝ → match n with Some n => £ n | None => False end) -∗
    WPi t @ laterH m ⊕ H; M {{ Φ }} -∗
    WPi later_ifn n t @ H; M {{ r,
      match r with
      | inl r => Φ r
      | inr LaterExhausted => ⌜is_Some n⌝
      end
    }}.
  Proof.
    iIntros "Hlc Hwp".
    rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iDestruct (later_adequacy_empty with "Hlc Hwp") as "Hwp".
    iApply wpi_wand; last done. iIntros (r). destruct r.
    - eauto.
    - (* Where do we get the mask from? *)
  Abort.
   *)
End adequacy.

Section trace.
  Context {R : Type} {E : Type → Type}.

  (** Interpret away [laterE] events in [trcae (laterE +' E)]. Akin to the
  definition of [later_ifn], if [n = Some n'] and more than [n'] [ELater]s are
  reached, [inr LaterExhausted] is returned to mark that a timeout has
  happened. *)
  Fixpoint interp_tr_later (n : option nat) (tr : trace (laterE +' E) R) : trace E (R + later_exhausted) :=
    match tr with
    | TRet r => TRet (inl r)
    | TVis A (inl1 ELater) a k =>
        match n with
        | Some 0 => TRet (inr LaterExhausted)
        | Some (S n') => interp_tr_later (Some n') k
        | None => interp_tr_later None k
        end
    | TVis A (inr1 e) a k => TVis A e a (interp_tr_later n k)
    | TVisEmpty A (inr1 e) => TVisEmpty A e
    | _ => TCut
    end.

  (** Intermediate statement for induction. *)
  Lemma later_trace' (tr : trace (laterE +' E) R) n t :
    is_trace tr t →
    is_trace (interp_tr_later (Some n) tr) (later_ifn (Some n) t).
  Proof.
    intros Htr. rewrite /is_trace in Htr.
    revert t tr Htr. induction n; intros t tr Htr.
    - remember (observe t) as ot. revert t Heqot.
      induction Htr; intros t_ Heqot; simplify_obs.
      * constructor.
      * destruct e as [e|e]; first destruct e as [].
        + rewrite later_ifn_unfold. rewrite /later_ifn_loop /=.
          simpl_itree. constructor.
        + simpl. rewrite later_ifn_unfold. rewrite /later_ifn_loop. simpl_itree.
          rewrite bind_trigger. constructor. by apply IHHtr.
      * destruct e as [e|e].
        + destruct e. constructor.
        + rewrite later_ifn_unfold /later_ifn_loop /=. simpl_itree. rewrite bind_trigger.
          by constructor.
      * constructor.
      * rewrite later_ifn_unfold /later_ifn_loop /=. simpl_itree. by apply IHHtr.
    - remember (observe t) as ot. revert t Heqot IHn.
      induction Htr; intros t_ Heqot IHn; simplify_obs.
      * constructor.
      * destruct e as [e|e]; first destruct e as [].
        + rewrite later_ifn_unfold. rewrite /later_ifn_loop /=.
          simpl_itree. replace (n - 0) with n by lia. apply IHn.
          by destruct a.
        + simpl. rewrite later_ifn_unfold. rewrite /later_ifn_loop. simpl_itree.
          rewrite bind_trigger. constructor. by apply IHHtr.
      * destruct e as [e|e].
        + destruct e. constructor.
        + rewrite later_ifn_unfold /later_ifn_loop /=. simpl_itree. rewrite bind_trigger.
          by constructor.
      * constructor.
      * rewrite later_ifn_unfold /later_ifn_loop /=. simpl_itree. by apply IHHtr.
  Qed.
  (** Traces are preserved by [later_ifn]. *)
  Lemma later_trace (tr : trace (laterE +' E) R) n t :
    is_trace tr t →
    is_trace (interp_tr_later n tr) (later_ifn n t).
  Proof.
    intros Htr. destruct n; first by apply later_trace'.
    rewrite /is_trace in Htr.
    remember (observe t) as ot. revert t Heqot.
    induction Htr; intros t_ Heqot; simplify_obs.
    * constructor.
    * destruct e as [e|e]; first destruct e as [].
      + rewrite later_ifn_unfold. rewrite /later_ifn_loop /=.
        simpl_itree. apply IHHtr. by destruct a.
      + simpl. rewrite later_ifn_unfold. rewrite /later_ifn_loop. simpl_itree.
        rewrite bind_trigger. constructor. by apply IHHtr.
    * destruct e as [e|e].
      + destruct e. constructor.
      + rewrite later_ifn_unfold /later_ifn_loop /=. simpl_itree. rewrite bind_trigger.
        by constructor.
    * constructor.
    * rewrite later_ifn_unfold /later_ifn_loop /=. simpl_itree. by apply IHHtr.
  Qed.
End trace.
