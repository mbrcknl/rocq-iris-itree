From iris.bi Require Import fixpoint.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Import fancy_updates.
From iris.base_logic.lib Require Import invariants.
From iris.itree Require Import handler.
From ITree Require Import ITree.
From ITree Require Import CategoryFunctor.
From ITree Require Import Interp.InterpFacts.
From ITree Require Import Interp.TranslateFacts.
From ITree Require Import Eq.
From ITree Require Import Eqit.
From Paco Require Import paco.
Require Import Coq.Program.Equality.

Global Instance itree_equiv (E : Type → Type) R : Equiv (itree E R) := eq_itree (=).

Global Instance eq_itree_iff {E R} (t' : itree E R) :
  Proper (eq_itree (=) ==> iff) (λ t, t ≅ t').
Proof.
  intros t1 t2 Heqit. by rewrite Heqit.
Qed.

(** TODO: Is this to be found anywhere in the ITree library? *)
Lemma itree_match {E R} (t : itree E R) :
  (∃ r, t ≅ Ret r) ∨
  (∃ t', t ≅ Tau t') ∨
  (∃ A (e : E A) k, t ≅ Vis e k).
Proof.
  rewrite /eq_itree /eqit /eqit_.
  destruct (observe t) as [r|t'|A e k] eqn:Heq.
  - left. exists r. pfold. rewrite Heq. by apply EqRet.
  - right. left. exists t'. pfold. rewrite Heq. apply EqTau. rewrite /upaco2 /bot2. left.
    by apply Reflexive_eqit.
  - right. right. exists A, e, k. pfold. rewrite Heq. apply EqVis. rewrite /upaco2 /bot2. left.
    by apply Reflexive_eqit.
Qed.

Section wp_itree.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.

  Import EqNotations.

  (** The definition of the weakest precondition, prior to taking the fixpoint.

  The result is of type [option R]. [None] represents safe termination. This is
  a workaround to avoid dependent typing while still allowing us to consider
  in addition to [itree E R] also [itree E unit], which is needed for e.g.
  spawning new threads. *)
  Definition wpiF (H : iHandler Σ E)
    (wpi : discreteO (itree E (option R)) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ) :
           discreteO (itree E (option R)) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ :=
    λ t Φ,
      (|={∅}=>
        match observe t with
        (* Used to terminate forked threads. *)
        | RetF None     => |={∅, ⊤}=> True
        | RetF (Some r) => Φ r
        | TauF t'       => ▷ wpi t' Φ
        (* To deal with the fact that [iHandler]s need not be monotonic in the
        continuations, we close [H] so as to make it monotonic. Without this,
        the weakest precondition may fail to satisfy desirable properties such
        as the rule of consequence and the frame rule. *)
        | VisF e k      => H _ e
            (λ a, ▷ wpi (k a) Φ)
            (λ t', ▷ |={⊤, ∅}=> wpi (ITree.map (const None) t') (λ _, (* unreachable *) False))
        end
      )%I.

  Global Instance wpiF_contractive H : Contractive (wpiF H).
  Proof.
    intros n pre1 pre2 Hpre.
    rewrite /wpiF. intros t Φ.
    repeat (f_contractive || f_equiv || apply Hpre).
    - intros a1 a2 ->. f_contractive. apply Hpre.
    - intros t1 t2 ->. f_contractive. repeat f_equiv.
  Qed.

  Definition wpi_opt (H : iHandler Σ E) : itree E (option R) → (R → iProp Σ) → iProp Σ :=
    fixpoint (wpiF H).
  Definition wpi (H : iHandler Σ E) (t : itree E R) (Φ : R → iProp Σ) : iProp Σ :=
    wpi_opt H (ITree.map Some t) Φ.

  Lemma wpi_opt_unfold H (t : itree E (option R)) Φ :
    wpi_opt H t Φ ⊣⊢ wpiF H (wpi_opt H) t Φ.
  Proof.
    rewrite /wpi_opt. apply (fixpoint_unfold (wpiF H)).
  Qed.

  Global Instance wpi_opt_proper H :
    Proper ((eqit (=) false false) ==> ((=) ==> (⊢)) ==> (⊢)) (wpi_opt H).
  Proof.
    intros t1 t2 Hbisim Φ1 Φ2 HΦ.
    iLöb as "IH" forall (t1 t2 Hbisim).
    rewrite /wpi !wpi_opt_unfold /wpiF.
    rewrite /dist in Hbisim. unfold ofe_dist in Hbisim.
    rewrite /discrete_dist /equiv /itree_equiv in Hbisim.
    rewrite /eq_itree /eqit in Hbisim.
    punfold Hbisim.
    rewrite /eqit_ in Hbisim.
    destruct (observe t1), (observe t2).
    - dependent destruction Hbisim. iIntros "Hwp". iMod "Hwp". iModIntro. destruct r0.
      * by iApply HΦ.
      * done.
    - dependent destruction Hbisim. rewrite /is_true // in CHECK.
    - dependent destruction Hbisim.
    - dependent destruction Hbisim. rewrite /is_true // in CHECK.
    - dependent destruction Hbisim.
      * rewrite /upaco2 /bot2 in REL. destruct REL as [REL|?]; last contradiction.
        iIntros "Hwp". iMod "Hwp". iModIntro. iNext. by iApply "IH".
      * rewrite /is_true // in CHECK.
      * rewrite /is_true // in CHECK.
    - dependent destruction Hbisim. rewrite /is_true // in CHECK.
    - dependent destruction Hbisim.
    - dependent destruction Hbisim. rewrite /is_true // in CHECK.
    - dependent destruction Hbisim.
      iIntros "HH". iMod "HH". iModIntro. iApply (mono with "[] [] [HH]"); last done.
      + iIntros (a) "Hwp". iNext.
        rewrite /upaco2 /bot2 in REL. destruct (REL a) as [Hk|?]; last contradiction.
        by iApply "IH".
      + iModIntro. by iIntros (t) "Hwp".
  Qed.
  Global Instance wpi_opt_proper_bidirectional H :
    Proper ((eqit (=) false false) ==> ((=) ==> (⊣⊢)) ==> (⊣⊢)) (wpi_opt H).
  Proof.
    intros t1 t2 Hbisim Φ1 Φ2 HΦ.
    iSplit.
    - iIntros "Hwp". iApply wpi_opt_proper; last done.
      * done.
      * iIntros (r1 r2 Heq) "HΦ1". iApply HΦ; done.
    - iIntros "Hwp". iApply wpi_opt_proper; last done.
      * done.
      * iIntros (r1 r2 Heq) "HΦ1". iApply HΦ; done.
  Qed.

  Global Instance wpi_proper H :
    Proper ((eqit (=) false false) ==> ((=) ==> (⊢)) ==> (⊢)) (wpi H).
  Proof.
    rewrite /wpi.
    intros t1 t2 Hbisim Φ1 Φ2 HΦ.
    apply wpi_opt_proper.
    - by f_equiv.
    - done.
  Qed.
  Global Instance wpi_proper_bidirectional H :
    Proper ((eqit (=) false false) ==> ((=) ==> (⊣⊢)) ==> (⊣⊢)) (wpi H).
  Proof.
    rewrite /wpi.
    intros t1 t2 Hbisim Φ1 Φ2 HΦ.
    apply wpi_opt_proper_bidirectional.
    - by f_equiv.
    - done.
  Qed.
End wp_itree.

Local Notation "'WPi' t @ H {{ Φ } }" := (wpi H t%itree Φ)
  (at level 20, t, Φ at level 200, only parsing) : bi_scope.
Local Notation "'WPi' t @ H {{ v , Q } }" := (wpi H t%itree (λ v, Q))
  (at level 20, t, Q at level 200,
   format "'[hv' 'WPi'  t  '/' @  '[' H ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Section wp_itree.
  Context {Σ : gFunctors} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.
  Context {H : iHandler Σ E}.

  (* Internal helper lemmata. *)

  Lemma safe_termination_independent_post {T R R'} (t : itree E T) (Φ : R → iProp Σ) (Ψ : R' → iProp Σ) :
    wpi_opt H (ITree.map (const None) t) Φ -∗ wpi_opt H (ITree.map (const None) t) Ψ.
  Proof.
    iIntros "Hwp". iLöb as "IH" forall (T t Φ Ψ).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - rewrite !map_ret !wpi_opt_unfold /wpiF //.
    - rewrite !map_tau !wpi_opt_unfold /wpiF. simpl. iMod "Hwp". iModIntro. iNext. by iApply "IH".
    - rewrite /ITree.map !bind_vis !wpi_opt_unfold /wpiF. simpl. iMod "Hwp". iModIntro.
      iApply (mono with "[] [] [Hwp]"); last done.
      * iIntros (a) "Hwp". iNext. by iApply "IH".
      * iModIntro. iIntros (t') "Hwp". iNext. by iApply "IH".
  Qed.
  Lemma wpi_opt_always_None {R R'} Φ (t : itree E (option R)) :
    (wpi_opt H t (const (|={∅,⊤}=> True))) ⊣⊢
    (wpi_opt H (ITree.map (const (@None R')) t) Φ).
  Proof.
    iSplit.
    - iLöb as "IH" forall (R R' Φ t).
      destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
      * rewrite /wpi map_ret !wpi_opt_unfold /wpiF. simpl. destruct r; eauto.
      * rewrite map_tau !wpi_opt_unfold /wpiF. simpl. iIntros "Hwp". iMod "Hwp". iModIntro.
        iNext. by iApply "IH".
      * rewrite /wpi /ITree.map bind_vis !wpi_opt_unfold /wpiF. simpl. iIntros "Hwp".
        iMod "Hwp". iModIntro. iApply (mono with "[] [] [Hwp]"); last done.
        + iIntros (a) "Hwp". iNext. by iApply "IH".
        + iModIntro. iIntros (t') "Hwp". iNext. iMod "Hwp". iModIntro.
          by iApply safe_termination_independent_post.
    (* TODO: Is there a way to repeat a proof twice? *)
    - iLöb as "IH" forall (R R' Φ t).
      destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
      * rewrite /wpi map_ret !wpi_opt_unfold /wpiF. simpl. destruct r; eauto.
      * rewrite map_tau !wpi_opt_unfold /wpiF. simpl. iIntros "Hwp". iMod "Hwp". iModIntro.
        iNext. by iApply "IH".
      * rewrite /wpi /ITree.map bind_vis !wpi_opt_unfold /wpiF. simpl. iIntros "Hwp".
        iMod "Hwp". iModIntro. iApply (mono with "[] [] [Hwp]"); last done.
        + iIntros (a) "Hwp". iNext. by iApply "IH".
        + iModIntro. iIntros (t') "Hwp". iNext. iMod "Hwp". iModIntro.
          by iApply safe_termination_independent_post.
  Qed.

  (* Stepping rules. *)

  Lemma wpi_ret_emp_mask' {R} Φ (r : R):
    (|={∅}=> Φ r) ⊣⊢
    WPi Ret r @ H {{ Φ }}.
  Proof.
    rewrite /wpi map_ret wpi_opt_unfold /wpiF //.
  Qed.
  Lemma wpi_ret_emp_mask {R} Φ (r : R):
    Φ r -∗
    WPi Ret r @ H {{ Φ }}.
  Proof.
    iIntros "HΦ". by iApply wpi_ret_emp_mask'.
  Qed.

  Lemma wpi_tau_emp_mask' {R} Φ (t : itree E R):
    (|={∅}=> ▷ WPi t @ H {{ Φ }}) ⊣⊢
    WPi Tau t @ H {{ Φ }}.
  Proof.
    rewrite /wpi map_tau !wpi_opt_unfold /wpiF. simpl. f_equiv. f_equiv. rewrite wpi_opt_unfold //.
  Qed.
  Lemma wpi_tau_emp_mask {R} Φ (t : itree E R):
    ▷ WPi t @ H {{ Φ }} -∗
    WPi Tau t @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". by iApply wpi_tau_emp_mask'.
  Qed.

  Lemma wpi_vis_emp_mask' {R} Φ A (e : E A) (k : A → itree E R):
    (|={∅}=> H A (subevent A e) (λ r, ▷ WPi k r @ H {{ Φ }}) (λ t, ▷ |={⊤, ∅}=> WPi t @ H {{ const (|={∅, ⊤}=> True) }})) ⊣⊢
    WPi (Vis e k) @ H {{ Φ }}.
  Proof.
    rewrite /wpi /ITree.map bind_vis !wpi_opt_unfold /wpiF. simpl. f_equiv.
    iSplit.
    - iIntros "HH". iApply (mono with "[] [] [HH]"); last done.
      * eauto.
      * iModIntro. iIntros (t) "Hwp". iNext. iMod "Hwp". iModIntro.
        rewrite (_ : ITree.map (const None) t ≅ ITree.map (const None) (ITree.map Some t)).
        + by iApply wpi_opt_always_None.
        + rewrite map_map. f_equiv.
    - iIntros "HH". iApply (mono with "[] [] [HH]"); last done.
      * eauto.
      * iModIntro. iIntros (t) "Hwp". iNext. iMod "Hwp". iModIntro.
        rewrite (_ : ITree.map (const None) t ≅ ITree.map (const None) (ITree.map Some t)).
        + by iApply wpi_opt_always_None.
        + rewrite map_map. f_equiv.
  Qed.
  Lemma wpi_vis_emp_mask {R} Φ A (e : E A) (k : A → itree E R):
    H A (subevent A e) (λ r, ▷ WPi k r @ H {{ Φ }}) (λ t, ▷ |={⊤, ∅}=> WPi t @ H {{ const (|={∅, ⊤}=> True) }}) -∗
    WPi (Vis e k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". by iApply wpi_vis_emp_mask'.
  Qed.

  (* Structural rules. *)

  Lemma wpi_update_emp_mask {R} Φ (t : itree E R) :
    (|={∅}=> WPi t @ H {{ Φ }}) -∗
    (WPi t @ H {{ Φ }}).
  Proof.
    iIntros "Hwp". rewrite /wpi wpi_opt_unfold. by iMod "Hwp".
  Qed.

  Lemma wpi_update_post_emp_mask {R} Φ (t : itree E R) :
    (WPi t @ H {{ v, |={∅}=> Φ v }}) -∗
    (WPi t @ H {{ Φ }}).
  Proof.
    iIntros "Hwp". iLöb as "IH" forall (t).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - rewrite -!wpi_ret_emp_mask'. by iMod "Hwp".
    - rewrite -!wpi_tau_emp_mask'. iMod "Hwp". iModIntro. iNext. by iApply "IH".
    - rewrite -!wpi_vis_emp_mask'. iMod "Hwp". iModIntro.
      iApply (mono with "[] [] [Hwp]"); last done.
      * iIntros (a) "Hwp". iNext. by iApply "IH".
      * iModIntro. by iIntros (t') "Hwp".
  Qed.

  Lemma wpi_wand_emp_mask {R} (t : itree E R) Φ Ψ:
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @ H {{ Φ }} -∗
    WPi t @ H {{ Ψ }}.
  Proof.
    iIntros "Hwand Hwp". iLöb as "IH" forall (t).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - rewrite -!wpi_ret_emp_mask'. by iApply "Hwand".
    - rewrite -!wpi_tau_emp_mask'. iMod "Hwp". iModIntro. iNext. by iApply ("IH" with "Hwand").
    - rewrite -!wpi_vis_emp_mask'. iMod "Hwp". iModIntro.
      iApply (mono with "[Hwand] [] [Hwp]"); last done.
      * iIntros (a) "Hwp". iNext. by iApply ("IH" with "Hwand").
      * iModIntro. by iIntros (t') "Hwp".
  Qed.

  Lemma wpi_bind_emp_mask {R T} (t : itree E T) (k : T → itree E R) Φ :
    WPi t @ H {{ r, WPi (k r) @ H {{ Φ }} }} -∗
    WPi (ITree.bind t k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". iLöb as "IH" forall (t).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k' ->]]]]].
    - rewrite bind_ret_l -!wpi_ret_emp_mask'. by iApply wpi_update_emp_mask.
    - rewrite bind_tau -!wpi_tau_emp_mask'. iMod "Hwp". iModIntro. iNext. by iApply "IH".
    - rewrite bind_vis -!wpi_vis_emp_mask'. iMod "Hwp". iModIntro.
      iApply (mono with "[] [] [Hwp]"); last done.
      * iIntros (a) "Hwp". iNext. by iApply "IH".
      * iModIntro. by iIntros (t') "Hwp".
  Qed.

  (* Derived rules. *)

  Lemma wpi_frame_l_emp_mask {R} Φ (t : itree E R) (P : iProp Σ) :
    P ∗ WPi t @ H {{ Φ }} -∗
    WPi t @ H {{ v, P ∗ Φ v }}.
  Proof.
    iIntros "[HP Hwp]".
    iApply (wpi_wand_emp_mask with "[HP]"); last exact.
    eauto with iFrame.
  Qed.

  Lemma wpi_frame_r_emp_mask {R} Φ (t : itree E R) (P : iProp Σ) :
    WPi t @ H {{ Φ }} ∗ P -∗
    WPi t @ H {{ v, Φ v ∗ P }}.
  Proof.
    iIntros "[Hwp HP]".
    iApply (wpi_wand_emp_mask with "[HP]"); last exact.
    eauto with iFrame.
  Qed.
End wp_itree.

Notation "'WPi' t @ H ; M {{ v , Q } }" := (|={M, ∅}=> wpi H t%itree (λ v, |={∅, M}=> Q))%I
  (at level 20, t, Q at level 200,
   format "'[hv' 'WPi'  t  '/' @  '[' H ; M ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WPi' t @ H ; M {{ Φ } }" := (WPi t @ H; M {{ v, Φ v }})%I
  (at level 20, t, Φ at level 200, only parsing) : bi_scope.

Section wp_itree_mask.
  Context {Σ : gFunctors} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.
  Context {H : iHandler Σ E}.

  (* Structural rules. *)

  Lemma wpi_update {R} M Φ (t : itree E R) :
    (|={M}=> WPi t @ H; M {{ Φ }}) -∗
    (WPi t @ H; M {{ Φ }}).
  Proof.
    iIntros "Hwp". by iMod "Hwp".
  Qed.

  Lemma wpi_wand {R} (t : itree E R) M Φ Ψ :
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @ H; M {{ Φ }} -∗
    WPi t @ H; M {{ Ψ }}.
  Proof.
    iIntros "HΦΨ Hwp". iApply (wpi_wand_emp_mask with "[HΦΨ]").
    - iIntros (r) "Hgoal". by iApply "HΦΨ".
    - done.
  Qed.

  Lemma wpi_bind {R A} (t : itree E A) (k : A → itree E R) M Φ :
    WPi t @ H; M {{ r, WPi (k r) @ H; M {{ Φ }} }} -∗
    WPi (ITree.bind t k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_bind_emp_mask. iMod "Hwp".
    iApply wpi_wand_emp_mask; last done.
    iIntros (a) "Hwp". iApply wpi_update_emp_mask. by iMod "Hwp".
  Qed.

  (* Manipulating masks and invariants. *)

  (* TODO: Rename from "reduce" to something else. *)
  Lemma wpi_reduce_mask {R} M' M (Φ : R → iProp Σ) t :
    (|={M, M'}=> WPi t @ H; M' {{ v, |={M', M}=> Φ v }}) -∗
    WPi t @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iMod "Hwp". iMod "Hwp". iModIntro.
    iApply wpi_wand_emp_mask; last done.
    iIntros (r) "Hgoal". iMod "Hgoal". by iMod "Hgoal".
  Qed.

  Lemma wpi_clear_mask {R} M (Φ : R → iProp Σ) t :
    (|={M, ∅}=> WPi t @ H; ∅ {{ v, |={∅, M}=> Φ v }}) ⊣⊢
    WPi t @ H; M {{ Φ }}.
  Proof.
    iSplit.
    - iIntros "Hwp". by iApply wpi_reduce_mask.
    - iIntros "Hwp". iMod "Hwp". iModIntro. iApply wpi_wand_emp_mask; last done.
      by iIntros (r) "HΦ".
  Qed.

  Lemma wpi_mask_mono {R} M M' (Φ : R → iProp Σ) t :
    M ⊆ M' →
    WPi t @ H; M {{ Φ }} -∗
    WPi t @ H; M' {{ Φ }}.
  Proof.
    iIntros (Hsubset) "Hwp". iApply (wpi_reduce_mask M).
    iApply fupd_mask_intro; first done. iIntros "Hfupd".
    iApply (wpi_wand with "[Hfupd]"); last done.
    iIntros (r) "Hgoal". iMod "Hfupd". iModIntro. iApply "Hgoal".
  Qed.

  (* TODO: Make this rule derived. *)
  Lemma wpi_open_invariant {R} N M (Φ : R → iProp Σ) t P :
    ↑N ⊆ M →
    (▷ P -∗ WPi t @ H; M ∖ ↑N {{ v, ▷ P ∗ Φ v }}) -∗
    own_inv N P -∗ WPi t @ H; M {{ Φ }}.
  Proof.
    iIntros (Hsubset) "Hwp Hinv".
    iMod (own_inv_acc _ with "Hinv") as "[HP Hclose]"; first done.
    iSpecialize ("Hwp" with "HP").
    iMod "Hwp". iModIntro. iApply (wpi_wand_emp_mask with "[Hclose] [Hwp]"); last done.
    iIntros (r) "HP". iMod "HP" as "[HP HΦ]". by iMod ("Hclose" with "HP").
  Qed.

  (* Stepping rules. *)

  Lemma wpi_ret' {R} M Φ (r : R):
    (|={M}=> Φ r) ⊣⊢
    WPi Ret r @ H; M {{ Φ }}.
  Proof.
    rewrite -wpi_ret_emp_mask'.
    iSplit.
    - iIntros "HΦ". iMod "HΦ".
      iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
      iModIntro. iMod "Hfupd". by iModIntro.
    - iIntros "HΦ". iMod "HΦ". by iMod "HΦ".
  Qed.
  Lemma wpi_ret {R} M Φ (r : R):
    Φ r -∗
    WPi Ret r @ H; M {{ Φ }}.
  Proof.
    iIntros "HΦ". by iApply wpi_ret'.
  Qed.

  Lemma wpi_tau' {R} M Φ (t : itree E R):
    (|={M, ∅}=> ▷ WPi t @ H; ∅ {{ v, |={∅, M}=> Φ v }}) ⊣⊢
    WPi Tau t @ H; M {{ Φ }}.
  Proof.
    rewrite -wpi_tau_emp_mask'.
    iSplit.
    - iIntros "HΦ". iMod "HΦ". do 3 iModIntro. iApply wpi_update_emp_mask.
      iMod "HΦ". iModIntro. iApply wpi_wand_emp_mask; last done.
      iIntros (r) "HΦ". by iMod "HΦ".
    - iIntros "HΦ". do 2 iMod "HΦ". do 3 iModIntro. iApply wpi_wand_emp_mask; last done.
      by iIntros (r) "HΦ".
  Qed.
  Lemma wpi_tau {R} M Φ (t : itree E R):
    ▷ WPi t @ H; M {{ Φ }} -∗
    WPi Tau t @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". iApply wpi_tau'.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iNext. iMod "Hfupd". iMod "Hwp". iModIntro. iApply wpi_wand_emp_mask; last done.
    by iIntros (r) "HΦ".
  Qed.

  Lemma wpi_vis' {R} M Φ A (e : E A) (k : A → itree E R) :
    (|={M, ∅}=> H A (subevent A e) (λ r, ▷ WPi k r @ H; ∅ {{ v, |={∅, M}=> Φ v }}) (λ t, ▷ WPi t @ H; ⊤ {{ _, True }})) ⊣⊢
    WPi (Vis e k) @ H; M {{ Φ }}.
  Proof.
    rewrite -wpi_vis_emp_mask'.
    iSplit.
    - iIntros "HH". iMod "HH". iModIntro. iModIntro.
      iApply (mono with "[] [] [HH]"); last done.
      * iIntros (a) "Hwp". iNext. iApply wpi_update_emp_mask. iMod "Hwp". iModIntro.
        iApply wpi_wand_emp_mask; last done. iIntros (r) "HΦ". by iMod "HΦ".
      * iModIntro. iIntros (t) "Hwp". iNext. by iMod "Hwp".
    - iIntros "HH". do 2 iMod "HH". iModIntro.
      iApply (mono with "[] [] [HH]"); last done.
      * iIntros (a) "Hwp". iNext. iApply wpi_update_emp_mask. do 2 iModIntro.
        iApply wpi_wand_emp_mask; last done. iIntros (r) "HΦ". by iModIntro.
      * iModIntro. iIntros (t) "Hwp". iNext. by iMod "Hwp".
  Qed.
  Lemma wpi_vis {R} M Φ A (e : E A) (k : A → itree E R):
    (|={M, ∅}=> H A e (λ r, ▷ WPi k r @ H; ∅ {{ v, |={∅, M}=> Φ v }}) (λ t, ▷ WPi t @ H; ⊤ {{ const True }})) -∗
    WPi (Vis e k) @ H; M {{ Φ }}.
  Proof.
    iIntros "HH". iApply wpi_vis'. iMod "HH". by iModIntro.
  Qed.

  (* Derived rules. *)

  Lemma wpi_frame_l {R} M Φ (t : itree E R) (P : iProp Σ) :
    P ∗ WPi t @ H; M {{ Φ }} -∗
    WPi t @ H; M {{ v, P ∗ Φ v }}.
  Proof.
    iIntros "[HP Hwp]".
    iApply (wpi_wand with "[HP]"); last exact.
    eauto with iFrame.
  Qed.

  Lemma wpi_frame_r {R} M Φ (t : itree E R) (P : iProp Σ) :
    WPi t @ H; M {{ Φ }} ∗ P -∗
    WPi t @ H; M {{ v, Φ v ∗ P }}.
  Proof.
    iIntros "[Hwp HP]".
    iApply (wpi_wand with "[HP]"); last exact.
    eauto with iFrame.
  Qed.
End wp_itree_mask.

Section translation.
  Context {Σ : gFunctors} `{!invGS_gen HasNoLc Σ}.
  Context {E1 E2 : Type → Type}.
  Context {H1 : iHandler Σ E1} {H2 : iHandler Σ E2}.
  Context {f : E1 ~> itree E2}.

  (* Translation lemma. *)

  (** The following lemma allow you to relate weakest preconditions across
  [iHandler]s. Specifically, if you have a function [f] that interprets each
  event [E1 A] as an [itree E2 A], that is, a way to "translate" from events
  [E1] to [E2], then you may want to relate [WPI t @ H1 {{ Φ }}] to [WPI
  interp f t @ H1 {{ Φ }}] for itrees [t]. The following statement gives you
  sufficient conditions for when one implies the other. *)
  Lemma wpi_translation_emp_mask {R} (t : itree E1 R) Φ :
    □ (∀ A (e : E1 A) ψ,
         H1 A (subevent A e)
           (λ a, ▷ ψ a)
           (λ t', ▷ |={⊤, ∅}=> WPi interp f t' @ H2 {{ λ _, |={∅, ⊤}=> True }}) -∗
         WPi (f A e) @ H2 {{ v, ▷ ψ v }}
      ) -∗
    WPi t @ H1 {{ Φ }} -∗ WPi (interp f t) @ H2 {{ Φ }}.
  Proof.
    iIntros "#HH". iLöb as "IH" forall (R t Φ).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k' ->]]]]].
    - iIntros "Hwp". rewrite interp_ret -!wpi_ret_emp_mask' //.
    - iIntros "Hwp". rewrite interp_tau -!wpi_tau_emp_mask'. iMod "Hwp". iModIntro. iNext.
      by iApply "IH".
    - iIntros "Hwp". rewrite interp_vis. iApply wpi_bind_emp_mask.
      rewrite -wpi_vis_emp_mask'. iApply wpi_update_emp_mask. iMod "Hwp". iModIntro.
      iApply wpi_wand_emp_mask; last iApply "HH".
      + iIntros (r) "Hr". iApply wpi_tau_emp_mask. iNext. by iApply "IH".
      + iApply (mono with "[] [] [Hwp]"); last done.
        * by iIntros (a) "Hwp".
        * iModIntro. iIntros (t') "Hwp". iNext. by iApply "IH".
  Qed.

  Lemma wpi_translation {R} (t : itree E1 R) M Φ :
    □ (∀ A (e : E1 A) ψ,
         H1 A (subevent A e)
           (λ a, ▷ ψ a)
           (λ t', ▷ WPi interp f t' @ H2; ⊤ {{ λ _, True }}) -∗
         WPi (f A e) @ H2; ∅ {{ v, ▷ ψ v }}
      ) -∗
    WPi t @ H1; M {{ Φ }} -∗ WPi (interp f t) @ H2; M {{ Φ }}.
  Proof.
    iIntros "#Hwand Hwp".
    iApply wpi_translation_emp_mask; try done.
    iModIntro. iIntros (A e Ψ) "HH". iApply wpi_update_post_emp_mask.
    iApply wpi_update_emp_mask. by iApply "Hwand".
  Qed.
End translation.

Section inH.
  Context {Σ : gFunctors} `{!invGS_gen HasNoLc Σ}.
  Context {E1 E2 : Type → Type}.
  Context {H1 : iHandler Σ E1} {H2 : iHandler Σ E2}.
  Context `{E1 -< E2} `{inH Σ E1 E2 H1 H2}.

  (* TODO: Ideally the following lemmata would be an easy consequence of the
  translation lemmata above. However, the ITree library's definition of
  [interp] is peculiar in that it inserts these [Tau]s, which means that you
  can't define [translate] in terms of [interp] as opposed to what you may have
  expected. This is also why the ▷ in the post-condition appears in the
  lemmata above. *)

  Lemma wpi_inH_emp_mask {R} (t : itree E1 R) Φ :
    WPi t @ H1 {{ Φ }} -∗
    WPi translate (λ A e', subevent A e') t @ H2 {{ Φ }}.
  Proof.
    iLöb as "IH" forall (R t Φ).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k' ->]]]]].
    - iIntros "Hwp". rewrite translate_ret -!wpi_ret_emp_mask' //.
    - iIntros "Hwp". rewrite translate_tau -!wpi_tau_emp_mask'. iMod "Hwp". iModIntro. iNext.
      by iApply "IH".
    - iIntros "Hwp". rewrite translate_vis. iApply wpi_vis_emp_mask'.
      rewrite -wpi_vis_emp_mask'. iMod "Hwp". iModIntro. iApply is_inH.
      iApply (mono with "[] [] [Hwp]"); last done.
      + iIntros (r) "Hr". iNext. by iApply "IH".
      + iModIntro. iIntros (t') "Hwp". iNext. by iApply "IH".
  Qed.
  Lemma wpi_inH {R} (t : itree E1 R) M Φ :
    WPi t @ H1; M {{ Φ }} -∗
    WPi translate (λ A e', subevent A e') t @ H2; M {{ Φ }}.
  Proof.
    iIntros "Hwp". by iApply wpi_inH_emp_mask.
  Qed.
End inH.
