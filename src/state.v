From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.itree Require Import trace.
From iris.itree Require Import exec.
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

Definition get_state {S} `{stateE S -< E} : itree E S :=
  trigger EGetState.
Definition set_state {S} `{stateE S -< E} (x : S) : itree E unit :=
  trigger (ESetState x).

Lemma get_state_to_translate {E1 E2 S} (HE1 : stateE S -< E1) (HE2 : stateE S -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate get_state Hin get_state.
Proof. move => ?. rewrite /get_state. by apply trigger_to_translate. Qed.
Global Hint Resolve get_state_to_translate : itree_auto.
Lemma set_state_to_translate {E1 E2 S} s (HE1 : stateE S -< E1) (HE2 : stateE S -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (set_state s) Hin (set_state s).
Proof. move => ?. rewrite /set_state. by apply trigger_to_translate. Qed.
Global Hint Resolve set_state_to_translate : itree_auto.

Global Instance AnswerEqDecision_stateE {S} `{EqDecision S} :
  AnswerEqDecision (stateE S).
Proof. intros A [|x]; apply _. Qed.

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
  Context {S : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context `{!stateInterp Σ S}.
  Context {H : iHandler Σ E} `{stateE S -< E} `{inH Σ (stateE S) E (stateH S) H}.

  Lemma wpi_get_state (M : coPset) (Φ : S → iProp Σ) :
    (∀ s, state_interp s ={∅}=∗ state_interp s ∗ Φ s) -∗
    WPi get_state @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    simpl. iIntros (s) "Hs".
    iMod ("HΦ" with "Hs") as "[Hs HΦ]".
    iFrame. iApply wpi_ret. iModIntro. by iMod "Hfupd".
  Qed.

  Lemma wpi_set_state (s' : S) (M : coPset) (Φ : unit → iProp Σ) :
    (∀ s, state_interp s ={∅}=∗ state_interp s' ∗ Φ ()) -∗
    WPi set_state s' @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    simpl. iIntros (s) "Hs".
    iMod ("HΦ" with "Hs") as "[Hs HΦ]".
    iFrame. iApply wpi_ret. iModIntro. by iMod "Hfupd".
  Qed.
End wp_state.

Section stateH_adequacy.
  Context {S : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context `{!stateInterp Σ S}.
  Context {H : iHandler Σ E} `{stateE S -< E} `{inH Σ (stateE S) E (stateH S) H}.
  Context {R : Type}.
  (** This sequentiality assumption is used for the [ForwardVis] case in the adequacy
  proof below. *)
  Context `{!Sequential H}.

  (** The evaluation relation, prior to taking the fixpoint. This relation relates
  an [itree (stateE S +' E) R] to its evaluated [itree E (S * R)] where the
  final state is put in the first component of its return value. *)
  Variant state_irelF
    (state_irel : S → itree (stateE S +' E) R → itree E (S * R) → Prop)
    : S
    → itree' (stateE S +' E) R
    → itree' E (S * R)
    → Prop :=
  (** Forwarding what doesn't affect the state. *)
  | state_Ret s r :
    state_irelF state_irel s (RetF r) (RetF (s, r))
  | state_Tau s t t' :
    state_irel s t t' →
    state_irelF state_irel s (TauF t) (TauF t')
  | state_Vis s A e k k' :
    (∀ a : A, state_irel s (k a) (k' a)) →
    state_irelF state_irel s (VisF (inr1 e) k) (VisF e k')
  (** Setting the state from [s] to [s']. *)
  | state_ESetState s s' k t :
    state_irel s' (k tt) t →
    state_irelF state_irel s (VisF (inl1 (ESetState s')) k) (TauF t)
  (** Getting the state [s]. *)
  | state_EGetState s k t :
    state_irel s (k s) t →
    state_irelF state_irel s (VisF (inl1 EGetState) k) (TauF t).
  Hint Constructors state_irelF : iris_itree.
  Definition state_irel_
    (state_irel : S → itree (stateE S +' E) R → itree E (S * R) → Prop)
    : S
    → itree (stateE S +' E) R
    → itree E (S * R)
    → Prop :=
    λ s t t', state_irelF state_irel s (observe t) (observe t').

  (* TODO: Lemma relating this relation to interp in itree library. *)

  Lemma state_irelF_mono state_irel state_irel' s t t' :
    state_irel <3= state_irel' →
    state_irelF state_irel  s t t' →
    state_irelF state_irel' s t t'.
  Proof.
    intros Hleq Hstate_irelF. destruct Hstate_irelF; eauto with iris_itree.
  Qed.
  Lemma state_irel__mono :
    monotone3 state_irel_.
  Proof.
    rewrite /monotone3 /state_irel_. intros. by eapply state_irelF_mono; last done.
  Qed.
  Hint Resolve state_irel__mono : paco.

  (** The state_ireluation relation. See comment above. *)
  Definition state_irel :
    S → itree (stateE S +' E) R → itree E (S * R) → Prop :=
    paco3 state_irel_ bot3.

  Global Instance state_irel_proper_unilateral :
    Proper ((=) ==> eqit (=) false false ==> eqit (=) false false ==> impl) state_irel.
  Proof.
    pcofix CIH.
    intros s s' <- t1 t2 Ht t1' t2' Ht' Heval.
    pfold. rewrite /state_irel_.
    punfold Ht. punfold Ht'. punfold Heval. rewrite /state_irel_ in Heval.
    destruct Ht, Ht'; try discriminate; try inversion Heval.
    - simplify_eq. inversion Heval. constructor.
    - constructor. pclearbot. simplify_eq. right. eapply CIH; first reflexivity.
      * apply REL.
      * done.
      * clear REL REL0. by pclearbot.
    - do 2 simplify_K. pclearbot. eapply state_ESetState. right. eapply CIH; first reflexivity.
      + apply REL.
      + done.
      + clear REL REL0. by pclearbot.
    - do 2 simplify_K. pclearbot. inversion Heval. constructor. right.
      eapply CIH; last apply H4; first reflexivity.
      * apply REL.
      * apply REL0.
    - do 2 simplify_K. pclearbot. inversion Heval. constructor. right.
      destruct (H5 a); [|contradiction]. simplify_K.
      eapply CIH; last done; first reflexivity.
      * apply REL.
      * apply REL0.
  Qed.
  Global Instance state_irel_proper :
    Proper (pointwise_relation S (eqit (=) false false ==> eqit (=) false false ==> (↔))%signature) state_irel.
  Proof.
    intros s t1 t2 Ht t1' t2' Ht'.
    split; rewrite Ht Ht' //.
  Qed.

  (** A technical version of adequacy, amenable to induction. See corollary below for a
  more meaningful statement. *)
  Theorem state_adequacy_empty s t t' M Φ :
    state_irel s t t' →
    state_interp s -∗
    WPi t @ stateH S ⊕ H; ∅ {{ v, |={∅, M}=> Φ v }} -∗
    WPi t' @ H; ∅ {{ x, |={∅, M}=> let (s, v) := x in state_interp s ∗ Φ v }}.
  Proof.
    iIntros "%Heval Hstate Hwp".
    pose (G := (λ (t : itree (stateE S +' E) R) (Φ : R -d> iPropO Σ),
      ∀ t' s Ψ,
        ⌜state_irel s t t'⌝ →
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
  Theorem state_adequacy s t t' M Φ :
    state_irel s t t' →
    state_interp s -∗
    WPi t @ stateH S ⊕ H; M {{ Φ }} -∗
    WPi t' @ H; M {{ x, let (s, v) := x in state_interp s ∗ Φ v }}.
  Proof.
    iIntros (Heval) "Hstate Hwp". rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    by iApply (state_adequacy_empty with "Hstate").
  Qed.
End stateH_adequacy.

Section ifn.
  Context {S R : Type} {E : Type → Type}.

  (** Interpretation function for [stateE]. It turns out that this function is
  equivalent to [state_irel], in the sense that every [itree (stateE S +' E) R]
  admits exactly one relational interpretation. However, for consistency (and
  extendability), we have both perspectives. *)
  Definition state_ifn : S → itree (stateE S +' E) R → itree E (S * R) :=
    cofix _state_ifn s t :=
        match observe t with
        | RetF r  => Ret (s, r)
        | TauF t' => Tau (_state_ifn s t')
        | @VisF _ _ _ A (inl1 e) k =>
          (match e with
          | EGetState => λ k, Tau (_state_ifn s (k s))
          | ESetState s' => λ k, Tau (_state_ifn s' (k ()))
          end : (A → _) → _) k
        | VisF (inr1 e) k => Vis e (λ a, _state_ifn s (k a))
        end.
  Notation state_ifn_ s t :=
      match observe t with
      | RetF r  => Ret (s, r)
      | TauF t' => Tau (state_ifn s t')
      | @VisF _ _ _ A (inl1 e) k =>
        (match e with
        | EGetState => λ k, Tau (state_ifn s (k s))
        | ESetState s' => λ k, Tau (state_ifn s' (k ()))
        end : (A → _) → _) k
      | VisF (inr1 e) k => Vis e (λ a, state_ifn s (k a))
      end.

  Lemma unfold_state_ifn s t :
    state_ifn s t = state_ifn_ s t.
  Proof.
    apply bisimulation_is_eq. apply observing_sub_eqit; constructor; reflexivity.
  Qed.

  (** The function [state_ifn] instantiates the relation [state_irel]. *)
  (* TODO: Prove the converse uniqueness property. *)
  Lemma state_ifn_irel s t :
    state_irel s t (state_ifn s t).
  Proof.
    remember (state_ifn s t) as t'.
    revert s t t' Heqt'. pcofix CIH. pfold. intros s t t' ->.
    rewrite unfold_state_ifn /state_irel_.
    destruct (observe t) as [r'|t'|A e k].
    - constructor.
    - constructor. right. by apply (CIH s t').
    - destruct e as [e|e]; first destruct e as [|s'];
      constructor; right; by apply CIH.
  Qed.
End ifn.

Section trace.
  Context {S R : Type} `{EqDecision S} {E : Type → Type}.

  (** Interpret away state events in a [trace (stateE S +' E) R]. [None] is
  returned if the state is not coherent, that is, the trace claims that a state
  that does not match the actual state is read. The final state of the trace is
  incorporated in the return value of type [S * R]. *)
  Fixpoint interp_tr_state (s : S) (tr : trace (stateE S +' E) R) : option (trace E (S * R)) :=
    match tr with
    | TRet r => Some (TRet (s, r))
    | TVis A (inl1 e) a k =>
        (match e : stateE S A with
          | EGetState => λ a, if decide (a = s) then interp_tr_state s k else None
          | ESetState s' => λ a, interp_tr_state s' k
        end : A → _) a
    | TVis A (inr1 e) a k => fmap (TVis A e a) (interp_tr_state s k)
    | TVisEmpty A (inl1 e) => None
    | TVisEmpty A (inr1 e) => Some (TVisEmpty A e)
    | TCut => Some TCut
    end.

  (** Traces are preserved by [state_ifn]. *)
  Lemma state_trace_preserved (tr : trace (stateE S +' E) R) tr' t s :
    is_trace tr t →
    interp_tr_state s tr = Some tr' →
    is_trace tr' (state_ifn s t).
  Proof.
    intros Htr. revert s tr'. setoid_rewrite unfold_state_ifn. induction Htr.
    - intros s tr' [=<-]. constructor.
    - intros s tr'' Hst. setoid_rewrite <- unfold_state_ifn in IHHtr.
      destruct e as [e|e]; first destruct e as [|s'].
      * simpl in Hst.
        destruct (decide (a = s)) as [->|]; last discriminate.
        constructor.
        by apply IHHtr.
      * simpl in Hst.
        constructor.
        destruct a. by apply IHHtr.
      * simpl in Hst. destruct (interp_tr_state s tr') as [tr'''|] eqn:Heq'; last done.
        injection Hst as Heq. rewrite -Heq.
        constructor. by apply IHHtr.
    - intros s tr' Hst. destruct e as [e|e].
      * discriminate.
      * injection Hst as <-. by constructor.
    - intros s tr' Hst. injection Hst as <-. constructor.
    - intros s tr' Hst. constructor.
      setoid_rewrite <- unfold_state_ifn in IHHtr. by apply IHHtr.
  Qed.

  (** Construct a relational interpretation from a trace. *)
  Theorem state_trace (tr : trace (stateE S +' E) R) tr' t s :
    is_trace tr t →
    interp_tr_state s tr = Some tr' →
    ∃ t', state_irel s t t' ∧ is_trace tr' t'.
  Proof.
    intros Htr Hst. exists (state_ifn s t).
    split; first apply state_ifn_irel.
    by eapply state_trace_preserved.
  Qed.
End trace.

(** Definitions for exec *)
Program Definition stateEH S : seHandler (stateE S) :=
  SEHandler S (λ A e s,
      match e with
      | EGetState    => λ C, C s s
      | ESetState s' => λ C, C tt s'
      end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance stateEH_adequate {Σ} `{!invGS_gen hlc Σ} S `{!stateInterp Σ S} :
    seHandlerAdequate (stateH S) (stateEH S) := {| sehandler_inv s := state_interp s |}.
Next Obligation.
  move => ??????????? HEH.
  iIntros "HH Hs". rewrite /stateH/=. case_match.
  - iMod ("HH" with "Hs") as "[$ $]". by iModIntro.
  - iMod ("HH" with "Hs") as "[$ $]". by iModIntro.
Qed.
