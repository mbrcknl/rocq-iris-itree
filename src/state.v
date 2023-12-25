From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From ITree Require Import ITree.
From Paco Require Import paco.
From Paco Require Import paco3.
From ITree Require Import Eqit.

(** An event type for stateful programs. *)
Inductive stateE (S : Type) : Type → Type :=
  (** Get the global state. *)
  | EGetState : stateE S S
  (** Set the global state. *)
  | ESetState (x : S) : stateE S unit.
Arguments EGetState {_}.
Arguments ESetState {_} _.

(** State interpretation predicate which is enforced at every [EGet]
and [ESet]. *)
Class stateInterp (Σ : gFunctors) (S : Type) := state_interp : S → iProp Σ.

Section stateH.
  Context {Σ} (S : Type) `{!stateInterp Σ S} `{!invGS_gen hlc Σ}.

  (** [iHandler] for [stateE]. *)
  Program Definition stateH : iHandler Σ (stateE S) :=
    IHandler (λ A e,
      match e with
      | EGetState    => λ Φ _, (∀ s, state_interp s ={∅}=∗ (state_interp s  ∗ Φ s ))
      | ESetState s' => λ Φ _, (∀ s, state_interp s ={∅}=∗ (state_interp s' ∗ Φ ()))
      end
    )%I _.
  Next Obligation.
    iIntros (? e ????) "HΦwand Hswand". destruct e.
    - iIntros "Hget" (?) "Hstate". iDestruct ("Hget" with "Hstate") as ">[$ HΦ]". by iApply "HΦwand".
    - iIntros "Hset" (?) "Hstate". iDestruct ("Hset" with "Hstate") as ">[$ HΦ]". by iApply "HΦwand".
  Qed.

  Global Instance stateH_Sequential :
    Sequential stateH.
  Proof.
    iIntros (A e Φ s) "HH". by destruct e.
  Qed.
End stateH.

Section wp_state.
  Context {S : Type} `{!stateHGS Σ S} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context `{!stateInterp Σ S}.
  Context {H : iHandler Σ E} `{stateE S -< E} `{inH Σ (stateE S) E (stateH S) H}.

  Lemma wpi_get {R} (k : S → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s ={M}=∗ state_interp s ∗ WPi (k s) @ H; M {{ Φ }}) -∗
    WPi (vis EGetState k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". iDestruct ("Hwp" with "Hs") as "Hswp".
    iMod "Hfupd" as "_". iMod "Hswp". iDestruct "Hswp" as "[Hwp Hs]". iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply wpi_update. iMod "Hfupd". rewrite wpi_clear_mask //.
  Qed.

  Lemma wpi_set {R} (s' : S) (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s ={M}=∗ state_interp s' ∗ WPi (k tt) @ H; M {{ Φ }}) -∗
    WPi (vis (ESetState s') k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". simpl. iMod "Hfupd" as "_".
    iDestruct ("Hwp" with "Hs") as ">[Hs Hwp]". iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    rewrite -wpi_clear_mask. iApply wpi_update. iMod "Hfupd". by iMod "Hwp".
  Qed.
End wp_state.

Section stateH_adequacy.
  Context {S : Type} `{!stateHGS Σ S} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context `{!stateInterp Σ S}.
  Context {H : iHandler Σ E} `{stateE S -< E} `{inH Σ (stateE S) E (stateH S) H}.
  Context {R : Type}.
  (** This sequentiality assumption is used for the [ForwardVis] case in the adequacy
  proof below. *)
  Context `{!Sequential H}.

  (** The evaluation relation, prior to taking the fixpoint. This relation relates
  an [itree (stateE S +' E) R] to its evaluated [itree E (S * R)] where the
  final state is put in the first component of its return value. *)
  Variant evalF
    (eval : S → itree (stateE S +' E) R → itree E (S * R) → Prop)
    : S
    → itree' (stateE S +' E) R
    → itree' E (S * R)
    → Prop :=
  (** Forwarding what doesn't affect the state. *)
  | ForwardRet s r :
    evalF eval s (RetF r) (RetF (s, r))
  | ForwardTau s t t' :
    eval s t t' →
    evalF eval s (TauF t) (TauF t')
  | ForwardVis s A e k k' :
    (∀ a : A, eval s (k a) (k' a)) →
    evalF eval s (VisF (inr1 e) k) (VisF e k')
  (** Setting the state from [s] to [s']. *)
  | SetState s s' k t :
    eval s' (k tt) t →
    evalF eval s (VisF (inl1 (ESetState s')) k) (TauF t)
  (** Getting the state [s]. *)
  | GetState s k t :
    eval s (k s) t →
    evalF eval s (VisF (inl1 EGetState) k) (TauF t).
  Hint Constructors evalF : iris_itree.
  Definition eval_
    (eval : S → itree (stateE S +' E) R → itree E (S * R) → Prop)
    : S
    → itree (stateE S +' E) R
    → itree E (S * R)
    → Prop :=
    λ s t t', evalF eval s (observe t) (observe t').

  (* TODO: Lemma relating this relation to interp in itree library. *)

  Lemma evalF_mono eval eval' s t t' :
    eval <3= eval' →
    evalF eval  s t t' →
    evalF eval' s t t'.
  Proof.
    intros Hleq HevalF. destruct HevalF; eauto with iris_itree.
  Qed.
  Lemma eval__mono :
    monotone3 eval_.
  Proof.
    rewrite /monotone3 /eval_. intros. by eapply evalF_mono; last done.
  Qed.
  Hint Resolve eval__mono : paco.

  (** The evaluation relation. See comment above. *)
  Definition eval :
    S → itree (stateE S +' E) R → itree E (S * R) → Prop :=
    paco3 eval_ bot3.

  Global Instance eval_proper_unilateral :
    Proper ((=) ==> eqit (=) false false ==> eqit (=) false false ==> impl) eval.
  Proof.
    pcofix CIH.
    intros s s' <- t1 t2 Ht t1' t2' Ht' Heval.
    pfold. rewrite /eval_.
    punfold Ht. punfold Ht'. punfold Heval. rewrite /eval_ in Heval.
    destruct Ht, Ht'; try discriminate; try inversion Heval.
    - simplify_eq. inversion Heval. constructor.
    - constructor. pclearbot. simplify_eq. right. eapply CIH; first reflexivity.
      * apply REL.
      * done.
      * clear REL REL0. by pclearbot.
    - do 2 simplify_K. pclearbot. eapply SetState. right. eapply CIH; first reflexivity.
      + apply REL.
      + done.
      + clear REL REL0. by pclearbot.
    - do 2 simplify_K. pclearbot. inversion Heval. constructor. right.
      destruct H4 as [H4|X]; [|contradiction X].
      pclearbot. eapply CIH; last apply H4; first reflexivity.
      * apply REL.
      * apply REL0.
    - do 2 simplify_K. pclearbot. inversion Heval. constructor. right.
      destruct (H5 a) as [H5'|X]; [|contradiction X]. simplify_K.
      eapply CIH; last apply H5'; first reflexivity.
      * apply REL.
      * apply REL0.
  Qed.
  Global Instance eval_proper :
    Proper (pointwise_relation S (eqit (=) false false ==> eqit (=) false false ==> (↔))%signature) eval.
  Proof.
    intros s t1 t2 Ht t1' t2' Ht'.
    split; rewrite Ht Ht' //.
  Qed.

  (** A technical version of adequacy, amenable to induction. See corollary below for a
  more meaningful statement. *)
  Theorem wpi_state' s t t' M Φ :
    eval s t t' →
    state_interp s -∗
    WPi t @ stateH S ⊕ H; ∅ {{ v, |={∅, M}=> Φ v }} -∗
    WPi t' @ H; ∅ {{ x, |={∅, M}=> let (s, v) := x in state_interp s ∗ Φ v }}.
  Proof.
    iIntros "%Heval Hstate Hwp".
    pose (G := (λ (t : itree (stateE S +' E) R) (Φ : R -d> iPropO Σ),
      ∀ t' s Ψ,
        ⌜eval s t t'⌝ →
        state_interp s -∗
        (∀ v, Φ v -∗ |={∅, M}=> Ψ v) -∗
        WPi t' @ H; ∅ {{ x, |={∅, M}=> let (s, v) := x in state_interp s ∗ Ψ v }}
    )%I).
    iApply (wpi_iter' (H := stateH S ⊕ H) G with "[] [] [] [Hwp] [] Hstate").
    - solve_proper.
    - clear. iModIntro. iIntros (Φ r) "HΦ". iIntros (t s Ψ Heval) "Hstate HΨ".
      punfold Heval. inversion Heval. simplify_obs.
      iApply wpi_ret. iMod "HΦ". iMod ("HΨ" with "HΦ") as "HΨ". iModIntro. iFrame.
    - clear. iModIntro. iIntros (Φ t) "HG". rewrite /G /=. iIntros (t' s Ψ Heval) "Hstate Hwand".
      punfold Heval. inversion Heval. simplify_obs. rewrite -wpi_tau.
      iApply wpi_update. iMod "HG". iModIntro. iApply ("HG" with "[] Hstate Hwand").
      by pclearbot.
    - clear Φ t' Heval s. iModIntro. iIntros (Φ A e k) "HH". iEval (rewrite /G /=).
      iIntros (t' s Ψ Heval) "Hstate Hwand". punfold Heval. inversion Heval.
      * simplify_K. simplify_obs. iApply wpi_vis. iMod "HH". simpl. iModIntro.
        iDestruct (is_seq with "HH") as "HH".
        iApply (ihandler_mono with "[Hstate Hwand]"); last done.
        + iIntros (a) "Hwp". iApply wpi_update_post. iApply ("Hwp" with "[] Hstate Hwand").
          iPureIntro. pclearbot. apply H4.
        + by iIntros "!>" (?) "?".
      * simplify_K. simplify_obs. simplify_K. simpl. rewrite -wpi_tau. iApply wpi_update. iMod "HH".
        iMod ("HH" with "Hstate") as "[Hstate HH]". pclearbot. by iApply ("HH" with "[] Hstate").
      * simplify_K. simplify_obs. simplify_K. simpl. rewrite -wpi_tau. iApply wpi_update. iMod "HH".
        iMod ("HH" with "Hstate") as "[Hstate HH]". pclearbot. by iApply ("HH" with "[] Hstate").
    - done.
    - done.
    - eauto.
  Qed.

  (** Adequacy for [stateH S ⊕ H]. This says that if you can prove the
  weakest precondition an [itree (stateE S +' E) R] then you get the weakest
  precondition its evaluated [itree E (S * R)]. *)
  Theorem wpi_state s t t' M Φ :
    eval s t t' →
    state_interp s -∗
    WPi t @ stateH S ⊕ H; M {{ v, Φ v }} -∗
    WPi t' @ H; M {{ x, let (s, v) := x in state_interp s ∗ Φ v }}.
  Proof.
    iIntros (Heval) "Hstate Hwp". rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    by iApply (wpi_state' with "Hstate").
  Qed.
End stateH_adequacy.
