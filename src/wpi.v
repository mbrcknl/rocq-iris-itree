From iris.bi Require Import fixpoint.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Export ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.itree Require Import handler.
From ITree Require Import ITree.
From ITree Require Import Interp.InterpFacts.
From ITree Require Import Eq.

(** Weaken a predicate transformer into a monotonic predicate transformer in a
universal way. *)
Definition bi_mono1 {PROP : bi} {A} (P : (A → PROP) → PROP) : (A → PROP) → PROP :=
  λ Q, (∃ Q', P Q' ∗ (∀ a, Q' a -∗ Q a))%I.

Section bi_mono1.
  Context {PROP : bi} {A : Type}.
  Implicit Types (P : (A → PROP) → PROP).

  Lemma bi_mono1_intro0 P Q :
    P Q -∗
    bi_mono1 P Q.
  Proof. iIntros "?". iExists _. iFrame. iIntros (?) "$". Qed.

  Lemma bi_mono1_mono P Q1 Q2 :
    (∀ x, Q1 x -∗ Q2 x) -∗
    bi_mono1 P Q1 -∗
    bi_mono1 P Q2.
  Proof.
    iIntros "HQ [% [HP HQ1]]". iExists _. iFrame "HP". iIntros (?) "?".
    iApply "HQ". by iApply "HQ1".
  Qed.

  Lemma bi_mono1_mono_l P1 P2 Q :
    (∀ Q, P1 Q -∗ P2 Q) -∗
    bi_mono1 P1 Q -∗
    bi_mono1 P2 Q.
  Proof.
    iIntros "HQ [% [HP HQ1]]". iExists _. iFrame "HQ1". by iApply "HQ".
  Qed.

  Lemma bi_mono1_elim P Q :
    (∀ Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗
    bi_mono1 P Q -∗
    P Q.
  Proof. iIntros "HP [% [??]]". iApply ("HP" with "[$] [$]"). Qed.

  Lemma bi_mono1_dup P Q :
    bi_mono1 (bi_mono1 P) Q -∗
    bi_mono1 P Q.
  Proof.
    iIntros "?".
    iApply (bi_mono1_elim with "[] [$]").
    iIntros (?) "??". by iApply (bi_mono1_mono with "[$]").
  Qed.

  Lemma bi_mono1_intro P Q Q' :
    (∀ x, Q' x -∗ Q x) -∗
    P Q' -∗
    bi_mono1 P Q.
  Proof.
    iIntros "HQ HP".
    iApply (bi_mono1_mono with "HQ [HP]").
    by iApply bi_mono1_intro0.
  Qed.
End bi_mono1.

Section wp_itree.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type}.
  Context `{!invGS_gen HasNoLc Σ}.

  (** The definition of the weakest precondition, prior to taking the fixpoint. *)
  Definition wpi_pre (H : iHandler Σ E)
    (wp_itree : leibnizO (itree E R) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ) :
                leibnizO (itree E R) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ :=
    λ t Φ,
      (|={∅}=>
        (∃ r, ⌜t ≅ Ret r⌝ ∗ Φ r) ∨
        (∃ t', ⌜t ≅ Tau t'⌝ ∗ ▷ wp_itree t' Φ) ∨
        (* To deal with the fact that [iHandler]s need not be monotonic, we
        close [H] so as to make it monotonic. Without this, the weakest
        precondition may fail to satisfy desirable properties such as the rule
        of consequence. *)
        (∃ T (e : E T) k, ⌜t ≅ Vis e k⌝ ∗ bi_mono1 (H T e) (λ x, ▷ wp_itree (k x) Φ))
      )%I.

  Global Instance wpi_pre_ne n H:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) (wpi_pre H).
  Proof.
    move => ?? Hwp ?? -> ?? HΦ. rewrite /wpi_pre/bi_mono1.
    repeat (f_equiv || eapply Hwp || eapply HΦ || reflexivity).
  Qed.

  Lemma wpi_pre_mono H wp1 wp2:
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ)
    → ∀ t Φ, wpi_pre H wp1 t Φ -∗ wpi_pre H wp2 t Φ.
  Proof.
    iIntros "#Hinner" (t Φ) "Hwp".
    iMod "Hwp" as "[?|[[%t' [% ?]]|(%T&%e&%k&%&Hwp)]]"; iModIntro.
    - iLeft. by iFrame.
    - iRight. iLeft. iExists _. iSplit; [done|]. iModIntro. by iApply "Hinner".
    - iRight. iRight. iExists _, _, _. iSplit; [done|].
      iApply (bi_mono1_mono with "[] Hwp"). iIntros (?) "?". by iApply "Hinner".
  Qed.

  Local Instance wpi_pre_monotone H :
    BiMonoPred (λ wp_itree, uncurry (wpi_pre H (curry wp_itree))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply wpi_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => wp_itree Hwp n [??] [??] /= [/=??].
      apply wpi_pre_ne; eauto. move => ?????? /=. by apply: Hwp.
  Qed.

  Definition wp_itree (H : iHandler Σ E) : itree E R → (R → iProp Σ) → iProp Σ :=
    (* It is necessary to uncurry temporarily to get to the form
    [(A → iProp Σ) → (A → iProp Σ)] of which we can take the least fixpoint. *)
    curry (bi_least_fixpoint (λ wp_pre, uncurry (wpi_pre H (curry wp_pre)))).

  Global Instance wpi_ne H n:
    Proper ((=) ==> ((=) ==> dist n) ==> dist n) (wp_itree H).
  Proof. move => ?? -> ?? HΦ. unfold wp_itree. f_equiv. intros ?. by apply HΦ. Qed.
End wp_itree.

Notation "'WPi' t @ H {{ Φ } }" := (wp_itree H t%itree Φ)
  (at level 20, t, Φ at level 200, only parsing) : bi_scope.
Notation "'WPi' t @ H {{ v , Q } }" := (wp_itree H t%itree (λ v, Q))
  (at level 20, t, Q at level 200,
   format "'[hv' 'WPi'  t  '/' @  '[' H ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Section wp_itree.
  Context {Σ : gFunctors} {E : Type → Type} {H : iHandler Σ E}.
  Context `{!invGS_gen HasNoLc Σ}.

  Local Existing Instance wpi_pre_monotone.
  Lemma wpi_unfold {R} (t : itree E R) Φ :
    WPi t @ H {{ Φ }} ⊣⊢ wpi_pre H (wp_itree H) t Φ.
  Proof. rewrite /wp_itree /curry. apply: least_fixpoint_unfold. Qed.

  (* Induction principles for WPi. *)

  Lemma wpi_strong_ind {R} (G: leibnizO (itree E R) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive2 G →
    ⊢ (□ ∀ t Φ, wpi_pre H (λ t' Ψ, G t' Ψ ∧ WPi t' @ H {{ Ψ }}) t Φ -∗ G t Φ)
      -∗ ∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (t Φ) "Hwp".
    rewrite {2}/wp_itree {1}/curry.
    iApply (least_fixpoint_ind _ (uncurry G) with "[] Hwp").
    iIntros "!>" ([??]) "Hwp" => /=. by iApply "HPre".
  Qed.

  Lemma wpi_ind {R} (G: leibnizO (itree E R) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive2 G →
    ⊢ (□ ∀ t Φ, wpi_pre H G t Φ -∗ G t Φ)
      -∗ ∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply wpi_strong_ind. iIntros "!>" (t Φ) "Hwp".
    iApply "HPre". iApply (wpi_pre_mono with "[] Hwp").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.

  Global Instance wpi_proper R :
    Proper ((eqit (=) false false) ==> (=) ==> (⊢)) (wp_itree (R:=R) H).
  Proof.
    move => t1 t2 Heqit ?? ->. iIntros "Hwp".
    rewrite !wpi_unfold.
    iMod "Hwp" as "[[%r [% Hwp]]|[[%t' [% Hwp]]|(%T&%e&%k&%&Hwp)]]";
      iModIntro.
    - iLeft. iExists _. iFrame. by rewrite -Heqit.
    - iRight. iLeft. iExists _. iFrame. by rewrite -Heqit.
    - iRight. iRight. iExists _, _, _. iFrame. by rewrite -Heqit.
  Qed.

  (** Rule of consequence. *)
  Lemma wpi_wand {R} (t : itree E R) Φ Ψ:
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @ H {{ Φ }} -∗
    WPi t @ H {{ Ψ }}.
  Proof.
    iIntros "Hwand Hwp".
    pose (G := (λ t Ψ, ∀ Φ, (∀ r : R, Ψ r -∗ Φ r) -∗ WPi t @ H {{ Φ }})%I).
    iAssert (∀ Φ, WPi t @ H {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hwp"). done. }
    iIntros (?) "Hwp".
    iApply (wpi_ind with "[] Hwp"). { solve_proper. }
    iIntros "!>" (??) "Hwp". iIntros (?) "Hc".
    rewrite wpi_unfold.
    iMod "Hwp" as "[[%r [% Hwp]]|[[%t' [% Hwp]]|(%T&%e&%k&%&Hwp)]]"; iModIntro.
    - iLeft. iExists _. iSplit; [done|]. by iApply "Hc".
    - iRight. iLeft. iExists _. iSplit; [done|]. iModIntro. by iApply "Hwp".
    - iRight. iRight. iExists _, _, _. iSplit; [done|].
      iApply (bi_mono1_mono with "[Hc] Hwp"). iIntros (?) "Hwp". by iApply "Hwp".
  Qed.

  (* Monadic rules. *)

  Lemma wpi_bind {R T} (t : itree E T) (k : T → itree E R) Φ :
    WPi t @ H {{ r, WPi (k r) @ H {{ Φ }} }} -∗
    WPi (ITree.bind t k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp".
    pose (G := (λ t Ψ, ∀ Φ, (∀ r, Ψ r -∗ WPi k r @ H {{ Φ }}) -∗ WPi ITree.bind t k @ H {{ Φ }})%I).
    iAssert (∀ Φ, WPi t @ H {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hwp"). iIntros (?) "?". done. }
    iIntros (?) "Hwp".
    iApply (wpi_ind with "[] Hwp"). { solve_proper. }
    iIntros "!>" (??) "Hwp". iIntros (?) "Hc".
    rewrite wpi_unfold.
    iMod "Hwp" as "[[%r [%Heq Hwp]]|[[%t' [%Heq Hwp]]|(%X&%e&%j&%Heq&Hwp)]]".
    - iDestruct ("Hc" with "[$]") as "Hc". rewrite wpi_unfold.
      iMod "Hc" as "[[%r' [%Heq' Hwp]]|[[%t' [% Hwp]]|(%X&%e&%j&%&Hwp)]]"; iModIntro.
      + iLeft. iExists _. iSplit; [iPureIntro|done]. by rewrite Heq bind_ret_l.
      + iRight. iLeft. iExists _. iSplit; [iPureIntro|done]. by rewrite Heq bind_ret_l.
      + iRight. iRight. iExists _,_,_. iSplit; [iPureIntro|done].
        by rewrite Heq bind_ret_l.
    - iModIntro. iRight. iLeft. iExists _. iSplit. { iPureIntro. by rewrite Heq bind_tau. }
      iModIntro. by iApply "Hwp".
    - iModIntro. iRight. iRight. iExists _, _, _. iSplit.
      { iPureIntro. by rewrite Heq bind_vis. }
      iApply (bi_mono1_mono with "[Hc] Hwp"). iIntros (?) "Hwp". by iApply "Hwp".
  Qed.

  Lemma wpi_ret {R} Φ (r : R):
    Φ r -∗
    WPi Ret r @ H {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite wpi_unfold. iIntros "!>".
    iLeft. iExists _. by iFrame.
  Qed.

  (* Other basic cases. *)

  Lemma wpi_tau {R} Φ (t : itree E R):
    ▷ WPi t @ H {{ Φ }} -∗
    WPi Tau t @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". iEval (rewrite wpi_unfold). iIntros "!>".
    iRight. iLeft. iExists _. iSplit; [done|]. by iModIntro.
  Qed.

  Lemma wpi_vis {R} Φ T e (k : T → itree E R):
    H T e (λ r, WPi k r @ H {{ Φ }}) -∗
    WPi (Vis e k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". iEval (rewrite wpi_unfold). iIntros "!>".
    iRight. iRight. iExists _, _, _. iSplit; [done|].
    iApply (bi_mono1_intro with "[] Hwp"). by iIntros (?) "?".
  Qed.

  (* Derived rules. *)

  Lemma wp_frame_l {R} Φ (t : itree E R) (P : iProp Σ) :
    P ∗ WPi t @ H {{ Φ }} -∗
    WPi t @ H {{ v, P ∗ Φ v }}.
  Proof.
    iIntros "[HP Hwp]".
    iApply (wpi_wand with "[HP]"); last exact.
    eauto with iFrame.
  Qed.

  Lemma wp_frame_r {R} Φ (t : itree E R) (P : iProp Σ) :
    WPi t @ H {{ Φ }} ∗ P -∗
    WPi t @ H {{ v, Φ v ∗ P }}.
  Proof.
    iIntros "[Hwp HP]".
    iApply (wpi_wand with "[HP]"); last exact.
    eauto with iFrame.
  Qed.
End wp_itree.

Section translation.
  Context {Σ : gFunctors} {E1 E2 : Type → Type} {f : E1 ~> itree E2}.
  Context {H1 : iHandler Σ E1} {H2 : iHandler Σ E2}.
  Context `{!invGS_gen HasNoLc Σ}.

  (* Translation lemma. *)

  (** The following lemma allow you to relate weakest preconditions across
  [iHandler]s. Specifically, if you have a function [f] that interprets each
  event [E1 A] as an [itree E2 A], that is, a way to "translate" from events
  [E1] to [E2], then you may want to relate [WPI t @ H1 {{ Φ }}] to [WPI
  interp f t @ H1 {{ Φ }}] for itrees [t]. The following statement gives you
  sufficient conditions for when one implies the other. *)
  Lemma wp_translation {R} :
    □ (∀ A (e : E1 A) Q Q', (∀ v, Q v -∗ Q' v) -∗ H1 A e Q -∗ H1 A e Q') -∗
    □ (∀ A (e : E1 A) ψ, H1 A e ψ -∗ WPi (f A e) @ H2 {{ v, ψ v }}) -∗
    ∀ (t : itree E1 R) Φ, WPi t @ H1 {{ Φ }} -∗ WPi (interp f t) @ H2 {{ Φ }}.
  (** One could hope for a converse statement, but unfortunately the proof
  makes use of [wpi_bind] which is a one-way implication (because it in turn
  makes use of [wpi_ind]). If [wpi_bind] was instead an equivalence, it
  would in fact be possible to prove a converse statement. *)
  Proof.
    iIntros "#Hmon #HH". iApply wpi_ind.
    - intros n t1 t2 Heqnt φ1 φ2 Heqnφ. apply wpi_ne.
      * by setoid_rewrite Heqnt.
      * intros v v' Heqv. rewrite Heqv. apply Heqnφ.
    - iModIntro. iIntros (t Φ) "Hwp". iApply wpi_unfold.
      iDestruct "Hwp" as ">[(%r&%Hret&HΦ)|[(%t'&%Hstep&Hwp)|(%A&%e&%k&%Hvis&Hwp)]]".
      * iModIntro. iLeft. iExists r. iFrame. iPureIntro.
        setoid_rewrite -> Hret. apply interp_ret.
      * iModIntro. iRight. iLeft. iExists (interp f t'). iSplit.
        + iPureIntro. setoid_rewrite -> Hstep. apply interp_tau.
        + done.
      * setoid_rewrite <- wpi_unfold. rewrite Hvis. setoid_rewrite interp_vis.
        iApply wpi_bind. iApply wpi_wand.
        + iIntros (a) "Hwp2". by iApply wpi_tau.
        + iApply "HH". iApply bi_mono1_elim; last done. iIntros (Q) "HQ".
          by iApply "Hmon".
  Qed.
End translation.
