From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From ITree Require Import ITree.
From Paco Require Import paco.
From Paco Require Import paco3.

Class stateHPreG (Σ : gFunctors) (S : Type) := StateHPreG {
  stateH_pre_ghost_varG :> ghost_varG Σ S;
}.
Class stateHGS (Σ : gFunctors) (S : Type) := StateHGS {
  stateH_ghost_varG :> ghost_varG Σ S;
  stateH_name : gname;
}.
Definition stateHΣ S : gFunctors :=
  #[ ghost_varΣ S ].
Global Instance subG_stateHΣ Σ S :
  subG (stateHΣ S) Σ → stateHPreG Σ S.
Proof. solve_inG. Qed.

(** An event type for stateful programs. *)
Inductive stateE (S : Type) : Type → Type :=
  (** Get the global state. *)
  | EGetState : stateE S S
  (** Set the global state. *)
  | ESetState (x : S) : stateE S unit.
Arguments EGetState {_}.
Arguments ESetState {_} _.

(** State interpretation predicate which is enforced at every [EYield], [EGet]
and [ESet]. *)
Class stateInterp (Σ : gFunctors) (S : Type) := state_interp : S → iProp Σ.

(** Proposition asserting read-only access to the state interpretation. *)
Definition state_ro {S} `{!stateInterp Σ S} (s : S) : iProp Σ :=
  ∀ s', state_interp s' -∗ state_interp s' ∗ ⌜ s = s' ⌝.

Section stateH.
  Context {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HasNoLc Σ}.

  (** [iHandler] for [stateE]. *)
  Program Definition stateH : iHandler Σ (stateE S) :=
    IHandler (λ A e,
      match e with
      | EGetState    => λ Φ _, (∀ s, state_interp s -∗ (state_interp s ∗ Φ s))
      | ESetState s' => λ Φ _, (∀ s, state_interp s ={∅}=∗ (state_interp s' ∗ Φ tt))
      end
    )%I _.
  Next Obligation.
    iIntros (? e ????) "HΦwand Hswand". destruct e.
    - iIntros "Hget" (?) "Hstate". iDestruct ("Hget" with "Hstate") as "[$ HΦ]". by iApply "HΦwand".
    - iIntros "Hset" (?) "Hstate". iDestruct ("Hset" with "Hstate") as ">[$ HΦ]". by iApply "HΦwand".
  Qed.

  Global Instance stateH_Sequential :
    Sequential stateH.
  Proof.
    iIntros (A e Φ s s') "HH". by destruct e.
  Qed.
End stateH.

Section wp_state.
  Context {S : Type} `{!stateHGS Σ S} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.
  Context `{!stateInterp Σ S}.
  Context {H : iHandler Σ E} `{stateE S -< E} `{inH Σ (stateE S) E (stateH S) H}.

  Lemma wpi_get {R} (k : S → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s -∗ state_interp s ∗ ▷ WPi (k s) @ H; M {{ Φ }}) -∗
    WPi (vis EGetState k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". iDestruct ("Hwp" with "Hs") as "[Hs Hwp]". iFrame.
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.

  Lemma wpi_set {R} (s' : S) (k : unit → itree E R) (M : coPset) (Φ : R → iProp Σ) :
    (∀ s, state_interp s ={M}=∗ state_interp s' ∗ ▷ WPi (k tt) @ H; M {{ Φ }}) -∗
    WPi (vis (ESetState s') k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_vis.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd". iApply is_inH.
    rewrite /stateH. iIntros (s) "Hs". simpl. iMod "Hfupd" as "_".
    iDestruct ("Hwp" with "Hs") as ">[Hs Hwp]". iFrame.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. rewrite -wpi_clear_mask. iMod "Hfupd". by iMod "Hwp".
  Qed.
End wp_state.

Section stateH_adequacy.
  Context {S : Type} `{!stateHGS Σ S} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.
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

  (** A technical version of adequacy, amenable to induction. See corollary below for a
  more meaningful statement. *)
  Theorem wpi_state' s t t' M Φ :
    eval s t t' →
    state_interp s -∗
    WPi t @ stateH S ⊕ H; ∅ {{ v, |={∅, M}=> Φ v }} -∗
    WPi t' @ H; ∅ {{ x, |={∅, M}=> let (s, v) := x in state_interp s ∗ Φ v }}.
  Proof.
    iIntros "%Heval Hstate Hwp".
    iLöb as "IH" forall (t t' s Heval M Φ). punfold Heval.
    inversion Heval as
      [s_ r Hs Ht Ht'
      |s_ t_ t_' Heval' Hs Ht Ht'
      |s_ A e k k' Heval' Hs Ht Ht'
      |s_ s_' k t_ Heval' Hs Ht Ht'
      |s_ k t_ Heval' Hs Ht Ht'
      ].
    - (* ForwardRet s_ r *)
      destruct Hs. apply ret_observe_eqit in Ht as <-. apply ret_observe_eqit in Ht' as <-.
      rewrite -!wpi_ret'. iMod "Hwp". iModIntro. iMod "Hwp". iModIntro. iFrame.
    - (* FowardTau s_ t_ t_' *)
      destruct Hs. apply tau_observe_eqit in Ht as <-. apply tau_observe_eqit in Ht' as <-.
      rewrite -!wpi_tau'. iMod "Hwp". iModIntro. iNext. iEval (rewrite wpi_update_post).
      pclearbot. iApply ("IH" with "[//] Hstate"). rewrite wpi_update_post //.
    - (* FowardVis s_ A e k k' *)
      destruct Hs. apply vis_observe_eqit in Ht as <-. apply vis_observe_eqit in Ht' as <-.
      rewrite -!wpi_vis'. iMod "Hwp". iModIntro.
      iApply is_seq. iApply (ihandler_mono with "[Hstate] [] Hwp").
      * iIntros (a) "Hwp". iNext. pclearbot. iEval (rewrite wpi_update_post).
        iApply ("IH" with "[] Hstate").
        + iPureIntro. apply Heval'.
        + by iApply wpi_update_post.
      * iModIntro. by iIntros (a) "Hwp".
    - (* SetState s_ s_' k t_ *)
      destruct Hs. apply vis_observe_eqit in Ht as <-. apply tau_observe_eqit in Ht' as <-.
      rewrite -wpi_vis'. iMod "Hwp". simpl. iMod ("Hwp" $! s_ with "Hstate") as "[Hstate Hwp]".
      iApply wpi_tau. iNext. pclearbot. iApply ("IH" with "[//] Hstate").
      by iApply wpi_update_post.
    - (* GetState s_ k t_ *)
      destruct Hs. apply vis_observe_eqit in Ht as <-. apply tau_observe_eqit in Ht' as <-.
      rewrite -wpi_vis'. iMod "Hwp". simpl. iDestruct ("Hwp" $! s_ with "Hstate") as "[Hstate Hwp]".
      iApply wpi_tau. iNext. pclearbot. iApply ("IH" with "[//] Hstate").
      by iApply wpi_update_post.
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
