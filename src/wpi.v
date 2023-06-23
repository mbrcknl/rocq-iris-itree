From iris.bi Require Import fixpoint.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Export ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.itree Require Import handler.
From iris.itree Require Import event.
From ITree Require Import ITree.
From ITree Require Import CategoryFunctor.
From ITree Require Import Interp.InterpFacts.
From ITree Require Import Eq.
From ITree Require Import Eqit.

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

(* A variant of [bi_mono1] which makes predicate transformer monotonic only
under a persistency modality. *)
Definition bi_mono1_pers {PROP : bi} {A} (P : (A → PROP) → PROP) : (A → PROP) → PROP :=
  λ Q, (∃ Q', P Q' ∗ □ (∀ a, Q' a -∗ Q a))%I.

Section bi_mono1_pers.
  Context {PROP : bi} {A : Type}.
  Implicit Types (P : (A → PROP) → PROP).

  Lemma bi_mono1_pers_intro0 P Q :
    P Q -∗
    bi_mono1_pers P Q.
  Proof. iIntros "?". iExists _. iFrame. iModIntro. iIntros (?) "$". Qed.

  Lemma bi_mono1_pers_mono P Q1 Q2 :
    □ (∀ x, Q1 x -∗ Q2 x) -∗
    bi_mono1_pers P Q1 -∗
    bi_mono1_pers P Q2.
  Proof.
    iIntros "#HQ [% [HP #HQ1]]". iExists _. iFrame "HP". iModIntro.
    iIntros (?) "?". iApply "HQ". by iApply "HQ1".
  Qed.

  Lemma bi_mono1_pers_mono_l P1 P2 Q :
    (∀ Q, P1 Q -∗ P2 Q) -∗
    bi_mono1_pers P1 Q -∗
    bi_mono1_pers P2 Q.
  Proof.
    iIntros "HQ [% [HP HQ1]]". iExists _. iFrame "HQ1". by iApply "HQ".
  Qed.

  Lemma bi_mono1_pers_elim P Q :
    □ (∀ Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗
    bi_mono1_pers P Q -∗
    P Q.
  Proof. iIntros "#HP [% [?#?]]". iApply ("HP" with "[$] [$]"). Qed.

  Lemma bi_mono1_pers_intro P Q Q' :
    □ (∀ x, Q' x -∗ Q x) -∗
    P Q' -∗
    bi_mono1_pers P Q.
  Proof.
    iIntros "#HQ HP".
    iApply (bi_mono1_pers_mono with "HQ [HP]").
    by iApply bi_mono1_pers_intro0.
  Qed.
End bi_mono1_pers.

Global Instance itree_equiv (E : Type → Type) R : Equiv (itree E R) := eq_itree (=).

Global Instance eq_itree_iff {E R} (t' : itree E R) :
  Proper (eq_itree (=) ==> iff) (λ t, t ≅ t').
Proof.
  intros t1 t2 Heqit. by rewrite Heqit.
Qed.

Section wp_itree.
  Context {Σ : gFunctors} {R : Type} `{!EventFixpoint EF E} `{!invGS_gen HasNoLc Σ}.

  Import EqNotations.

  (** The definition of the weakest precondition, prior to taking the fixpoint.

  The result is of type [option R]. [None] represents safe termination. This is
  a workaround to avoid dependent typing while still allowing us to consider
  in addition to [itree E R] also [itree E unit], which is needed for e.g.
  spawning new threads. *)
  Definition wpi_pre (H : iHandler Σ EF)
    (wpi : discreteO (itree E (option R)) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ) :
           discreteO (itree E (option R)) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ :=
    λ t Φ,
      (|={∅}=>
        (* Used to terminate forked threads. *)
        (⌜t ≅ Ret None⌝ ∗ |={∅, ⊤}=> True) ∨
        (∃ r, ⌜t ≅ Ret (Some r)⌝ ∗ Φ r) ∨
        (∃ t', ⌜t ≅ Tau t'⌝ ∗ ▷ wpi t' Φ) ∨
        (* To deal with the fact that [iHandler]s need not be monotonic in the
        continuations, we close [H] so as to make it monotonic. Without this,
        the weakest precondition may fail to satisfy desirable properties such
        as the rule of consequence and the frame rule. *)
        (∃ A (e : E A) k, ⌜t ≅ Vis e k⌝ ∗
          bi_mono1
            (λ f,
              bi_mono1_pers
                (λ g, H E A (rew [λ T, T A] eq_fix in e) f g)
                (λ t', ▷ |={⊤, ∅}=> wpi (ITree.map (const None) t') (λ _, (* unreachable *) False))
            )
            (λ a, ▷ wpi (k a) Φ)
        )
      )%I.

  Global Instance wpi_pre_ne n H :
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) (wpi_pre H).
  Proof.
    intros wp1 wp2 Hwp t1 t2 Ht Φ1 Φ2 HΦ. rewrite /wpi_pre/bi_mono1/bi_mono1_pers.
    by repeat (apply eq_itree_iff || f_equiv || eapply Hwp).
  Qed.

  Lemma wpi_pre_mono H wp1 wp2:
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ)
    → ∀ t Φ, wpi_pre H wp1 t Φ -∗ wpi_pre H wp2 t Φ.
  Proof.
    iIntros "#Hinner" (t Φ) "Hwp".
    iMod "Hwp" as "[[%Ht >_]|[?|[[%t' [% ?]]|(%A&%e&%k&%&Hwp)]]]".
    - iLeft. iApply fupd_mask_intro; first done. iIntros "Hfupd".
      iSplit; first done. by iMod "Hfupd".
    - iModIntro. iRight. iLeft. by iFrame.
    - iModIntro. iRight. iRight. iLeft. iExists _. iSplit; [done|]. iModIntro. by iApply "Hinner".
    - iModIntro. iRight. iRight. iRight. iExists _, _, _. iSplit; [done|].
      iApply bi_mono1_mono_l; [|iApply (bi_mono1_mono with "[] Hwp")].
      * iIntros (?) "?". iApply bi_mono1_pers_mono; last done.
        iModIntro. iIntros (a) "Hwp1". iNext. iMod "Hwp1". iModIntro.
        by iApply "Hinner".
      * iIntros (a) "Hwp1". iNext. by iApply "Hinner".
  Qed.

  Local Instance wpi_pre_monotone H :
    BiMonoPred (λ wpi, uncurry (wpi_pre H (curry wpi))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply wpi_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => wp_itree Hwp n [??] [??] /= [/=??].
      apply wpi_pre_ne; eauto. move => ?????? /=. by apply: Hwp.
  Qed.

  Definition wpi_opt (H : iHandler Σ EF) : itree E (option R) → (R → iProp Σ) → iProp Σ :=
    (* It is necessary to uncurry temporarily to get to the form
    [(A → iProp Σ) → (A → iProp Σ)] of which we can take the least fixpoint. *)
    curry (bi_least_fixpoint (λ wp_pre, uncurry (wpi_pre H (curry wp_pre)))).
  Definition wpi (H : iHandler Σ EF) (t : itree E R) (Φ : R → iProp Σ) : iProp Σ :=
    wpi_opt H (ITree.map Some t) Φ.

  Global Instance wpi_opt_ne H n:
    Proper ((eq_itree (=)) ==> ((=) ==> dist n) ==> dist n) (wpi_opt H).
  Proof.
    intros t1 t2 Ht Φ1 Φ2 HΦ. unfold wpi_opt. f_equiv; first done. intros ?. by apply HΦ. Qed.
  Global Instance wpi_ne H n:
    Proper ((eq_itree (=)) ==> ((=) ==> dist n) ==> dist n) (wpi H).
  Proof.
    intros t1 t2 Ht Φ1 Φ2 HΦ. unfold wpi. by repeat f_equiv.
  Qed.
End wp_itree.

Notation "'WPi' t @ H {{ Φ } }" := (wpi H t%itree Φ)
  (at level 20, t, Φ at level 200, only parsing) : bi_scope.
Notation "'WPi' t @ H {{ v , Q } }" := (wpi H t%itree (λ v, Q))
  (at level 20, t, Q at level 200,
   format "'[hv' 'WPi'  t  '/' @  '[' H ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Section wp_itree.
  Context {Σ : gFunctors} `{!EventFixpoint EF E} `{!invGS_gen HasNoLc Σ}.
  Context {H : iHandler Σ EF}.

  Local Existing Instance wpi_pre_monotone.
  Lemma wpi_opt_unfold {R} (t : itree E (option R)) Φ :
    wpi_opt H t Φ ⊣⊢ wpi_pre H (wpi_opt H) t Φ.
  Proof. rewrite /wpi /curry. apply: least_fixpoint_unfold. Qed.

  Global Instance wpi_opt_proper R :
    Proper ((eqit (=) false false) ==> ((=) ==> (⊢)) ==> (⊢)) (wpi_opt (R:=R) H).
  Proof.
    move => t1 t2 Heqit Φ1 Φ2 HΦ. iIntros "Hwp".
    iLöb as "IH" forall (t1 t2 Heqit).
    rewrite /wpi !wpi_opt_unfold.
    iMod "Hwp" as "[[%Ht >_]|[[%r [Hret Hr]]|[[%t' [% ?]]|(%A&%e&%k&%&Hwp)]]]".
    - iLeft. iApply fupd_mask_intro; first done. iIntros "Hfupd".
      iFrame. rewrite -Heqit. done.
    - iModIntro. iRight. iLeft. iExists _. rewrite -Heqit. iFrame. by iApply HΦ.
    - iModIntro. iRight. iRight. iLeft. iExists _. rewrite -Heqit. iSplit; first done.
      iNext. by iApply "IH".
    - iModIntro. iRight. iRight. iRight. iExists _, _, _. rewrite -Heqit. iSplit; first done.
      iApply bi_mono1_mono; last done. iIntros (a) "Hwp". iNext. by iApply "IH".
  Qed.
  Global Instance wpi_proper R :
      Proper ((eqit (=) false false) ==> (=) ==> (⊢)) (wpi (R:=R) H).
  Proof.
    move => t1 t2 Heqit ?? ->. iIntros "Hwp".
    rewrite /wpi.
    iApply wpi_opt_proper; last done.
    * by f_equiv.
    * done.
  Qed.

  (* Internal helper lemmata. *)

  Lemma safe_termination_independent_post {T R R'} (t : itree E T) (Φ : R → iProp Σ) (Ψ : R' → iProp Σ) :
    wpi_opt H (ITree.map (const None) t) Φ -∗ wpi_opt H (ITree.map (const None) t) Ψ.
  Proof.
    iIntros "Hwp".
    iLöb as "IH" forall (T t Φ Ψ).
    rewrite !wpi_opt_unfold.
    iMod "Hwp" as "[[%Ht >_]|[[%r [%Hret Hwp]]|[[%t' [%Heq Hwp]]|(%A&%e&%k'&%Heq&Hwp)]]]".
    - iLeft. iApply fupd_mask_intro; first done. iIntros "Hfupd". iFrame. iPureIntro.
      apply eqit_inv_bind_ret in Ht as [tt [-> _]]. rewrite map_ret. reflexivity.
    - apply eqit_inv_bind_ret in Hret as [_ [_ [=]%eqitree_inv_Ret]].
    - iModIntro. iRight. iRight. iLeft. iExists (ITree.map (const None) t').
      iSplit.
      * iPureIntro.
        assert (Heq' : ITree.map (const (@None R')) (ITree.map (const (@None R)) t)
                     ≅ ITree.map (const (@None R')) (Tau t')).
        { by f_equiv. }
        transitivity (ITree.map (const (@None R')) (ITree.map (const (@None R)) t)).
        { rewrite map_map. by apply eqit_eq_map. }
        transitivity (ITree.map (const (@None R')) (Tau t')); first done.
        by rewrite map_tau.
      * iNext. iApply "IH".
        rewrite (_ : ITree.map (const None) t' ≅ t'); first done.
        apply eqit_inv_Tau.
        rewrite -Heq -map_tau -Heq map_map. by apply eqit_eq_map.
    - iModIntro. iRight. iRight. iRight.
      iExists A, e, (λ a, ITree.map (const None) (k' a)).
      iSplit.
      * iPureIntro.
        assert (Heq' : ITree.map (const (@None R')) (ITree.map (const (@None R)) t)
                     ≅ ITree.map (const (@None R')) (Vis e k')).
        { by f_equiv. }
        transitivity (ITree.map (const (@None R')) (ITree.map (const (@None R)) t)).
        { rewrite map_map. by apply eqit_eq_map. }
        transitivity (ITree.map (const (@None R')) (Vis e k')); first done.
        rewrite /ITree.map bind_vis. apply eqit_Vis. reflexivity.
      * iApply bi_mono1_mono_l; [|iApply (bi_mono1_mono with "[] Hwp")].
        + iIntros (Q) "Hwp". iApply bi_mono1_pers_mono; last done. iModIntro.
          iIntros (t') "Hwp". iNext. iMod "Hwp". iModIntro. by iApply "IH".
        + iIntros (a) "Hwp". iNext.
          rewrite {1}(_ : k' a ≅ (ITree.map (const None) (k' a))). { by iApply "IH". }
          generalize a.
          (* Assumes UIP according to ITree documentation. *)
          apply eqit_inv_Vis with (e := e).
          transitivity ((ITree.map (const (@None R))) t); first done.
          transitivity ((ITree.map (const (@None R))) ((ITree.map (const (@None R))) t)).
          { rewrite map_map. by apply eqit_map with (RR:=(=)). }
          transitivity (((ITree.map (const (@None R))) (Vis e k'))); first by f_equiv.
          rewrite /ITree.map -bind_vis //.
  Qed.

  Lemma wpi_opt_always_None {R R'} Φ (t : itree E (option R)) :
    (wpi_opt H t (const (|={∅,⊤}=> True))) ⊣⊢
    (wpi_opt H (ITree.map (const (@None R')) t) Φ).
  Proof.
    iSplit.
    - iIntros "Hwp". iLöb as "IH" forall (R R' Φ t). rewrite /wpi !wpi_opt_unfold.
      iMod "Hwp" as "[[%Ht >_]|[[%r [%Hret Hwp]]|[[%t' [%Heq Hwp]]|(%A&%e&%k'&%Heq&Hwp)]]]".
      * iLeft. iApply fupd_mask_intro; first done. iIntros "Hfupd". iFrame. rewrite Ht map_ret //.
      * simpl. iLeft. iModIntro. iFrame. rewrite Hret map_ret //.
      * iModIntro. iRight. iRight. iLeft. iExists (ITree.map (const None) t').
        iSplit.
        + iPureIntro. rewrite Heq map_tau //.
        + by iApply "IH".
      * iRight. iRight. iRight.
        iModIntro. iExists _, _, _. iSplit. { iPureIntro. rewrite Heq /ITree.map bind_vis //. }
        iApply bi_mono1_mono_l; [|iApply (bi_mono1_mono with "[] Hwp")].
        + iIntros (Q) "Hwp". iApply bi_mono1_pers_mono; last done.
          iModIntro. iIntros (t') "Hwp". iNext. iMod "Hwp". iModIntro.
          by iApply safe_termination_independent_post.
        + iIntros (a) "Hwp". iNext. by iApply "IH".
    - iIntros "Hwp". iLöb as "IH" forall (R R' Φ t). rewrite /wpi !wpi_opt_unfold.
      iMod "Hwp" as "[[%Ht Hfupd]|[[%r [%Hret Hwp]]|[[%t' [%Heq Hwp]]|(%A&%e&%k'&%Heq&Hwp)]]]".
      * iMod "Hfupd" as "_". apply eqit_inv_bind_ret in Ht as [[r|] [Ht _]].
        + iRight. iLeft. iApply fupd_mask_intro; first done. iIntros "Hfupd". iFrame. by iExists r.
        + iLeft. iApply fupd_mask_intro; first done. iIntros "Hfupd". by iFrame.
      * apply eqit_inv_bind_ret in Hret as [_ [_ [=]%eqitree_inv_Ret]].
      * iModIntro. iRight. iRight. iLeft. rewrite /ITree.map in Heq.
        apply eqitree_inv_bind_tau in Heq as [[t'' [Ht Hbind]] | [t'' [_ Hcontr]]].
        + iExists t''. iSplit; first done. iNext. iApply "IH". by rewrite /ITree.map -Hbind.
        + apply eqitree_inv_Tau_r in Hcontr as [t0 [[=] _]].
      * apply eqitree_inv_bind_vis in Heq as [[t'' [Ht Hbind]] | [t'' [_ Hcontr]]].
        + iRight. iRight. iRight. iModIntro. iExists _, _, _. iSplit; first done.
          iApply bi_mono1_mono_l; [|iApply (bi_mono1_mono with "[] Hwp")].
          ++ iIntros (Q) "Hwp". iApply bi_mono1_pers_mono; last done.
             iModIntro. iIntros (t') "Hwp". iNext. iMod "Hwp". iModIntro.
             by iApply safe_termination_independent_post.
          ++ iIntros (a) "Hwp". iNext. iApply "IH". by rewrite /ITree.map -Hbind.
        + apply eqitree_inv_Vis_r in Hcontr as [t0 [[=] _]].
  Qed.
  Lemma wpi_wpi_opt_always_None {R R'} Φ (t : itree E R) :
    (WPi t @ H {{ const (|={∅,⊤}=> True) }}) -∗
    (wpi_opt H (ITree.map (const (@None R')) t) Φ).
  Proof.
    rewrite /wpi.
    rewrite (_ : (ITree.map (const None) t) ≅ (ITree.map (const None) (ITree.map Some t))).
    - rewrite wpi_opt_always_None //.
    - rewrite map_map. by apply eqit_map with (RR:=(=)).
  Qed.

  (* Stepping rules. *)

  Lemma wpi_ret {R} Φ (r : R):
    Φ r -∗
    WPi Ret r @ H {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /wpi wpi_opt_unfold. iIntros "!>".
    iRight. iLeft. iExists _. iFrame. rewrite map_ret //.
  Qed.

  Lemma wpi_tau {R} Φ (t : itree E R):
    ▷ WPi t @ H {{ Φ }} -∗
    WPi Tau t @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". iEval (rewrite /wpi wpi_opt_unfold). iIntros "!>".
    iRight. iRight. iLeft. iExists _. iSplit.
    - by rewrite map_tau.
    - done.
  Qed.

  Lemma wpi_vis' {R} Φ A (e : E A) (k : A → itree E R):
    bi_mono1
      (λ f,
        bi_mono1_pers
          (λ g, H E A (subevent A e) f g)
          (λ t, ▷ |={⊤, ∅}=> WPi t @ H {{ const (|={∅, ⊤}=> True) }})
      )
      (λ r, ▷ WPi k r @ H {{ Φ }}) -∗
    WPi (Vis e k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite /wpi !wpi_opt_unfold. iIntros "!>".
    iRight. iRight. iRight. iExists _, _, _. iSplit.
    - iPureIntro. rewrite /ITree.map bind_vis //.
    - iApply (bi_mono1_mono_l with "[] [Hwp]"); last done.
      iIntros (Q) "Hwp".
      iApply (bi_mono1_pers_mono with "[] [Hwp]"); last done.
      iModIntro. iIntros (t) "Hwp". by iApply wpi_wpi_opt_always_None.
  Qed.
  Lemma wpi_vis {R} Φ A (e : E A) (k : A → itree E R):
    H E A (subevent A e) (λ r, ▷ WPi k r @ H {{ Φ }}) (λ t, ▷ |={⊤, ∅}=> WPi t @ H {{ const (|={∅, ⊤}=> True) }}) -∗
    WPi (Vis e k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp".
    iApply wpi_vis'.
    iApply bi_mono1_intro0.
    by iApply bi_mono1_pers_intro0.
  Qed.

  (* Structural rules. *)

  Lemma wpi_update {R} Φ (t : itree E R) :
    (|={∅}=> WPi t @ H {{ Φ }}) -∗
    (WPi t @ H {{ Φ }}).
  Proof.
    iIntros "Hwp". rewrite /wpi wpi_opt_unfold. by iMod "Hwp".
  Qed.

  Lemma wpi_opt_wand {R} (t : itree E (option R)) Φ Ψ:
    (∀ r, Φ r -∗ Ψ r) -∗
    wpi_opt H t Φ -∗
    wpi_opt H t Ψ.
  Proof.
    iIntros "Hwand Hwp".
    iLöb as "IH" forall (t).
    rewrite /wpi !wpi_opt_unfold.
    iMod "Hwp" as "[[%Ht >_]|[[%r [Hret Hr]]|[[%t' [% ?]]|(%A&%e&%k&%&Hwp)]]]".
    - iLeft. iApply fupd_mask_intro; first done. iIntros "Hfupd". by iSplit.
    - iModIntro. iRight. iLeft. iExists _. iSplit; [done|]. by iApply "Hwand".
    - iModIntro. iRight. iRight. iLeft. iExists _. iSplit; [done|]. iModIntro.
      by iApply ("IH" with "Hwand").
    - iModIntro. iRight. iRight. iRight. iExists A, e, k. iSplit; first done.
      iApply (bi_mono1_mono with "[Hwand] Hwp").
      iIntros (a) "Hwp". iNext. by iApply ("IH" with "Hwand").
  Qed.
  Lemma wpi_wand {R} (t : itree E R) Φ Ψ:
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @ H {{ Φ }} -∗
    WPi t @ H {{ Ψ }}.
  Proof.
    rewrite /wpi. iApply wpi_opt_wand.
  Qed.

  Lemma wpi_bind {R T} (t : itree E T) (k : T → itree E R) Φ :
    WPi t @ H {{ r, WPi (k r) @ H {{ Φ }} }} -∗
    WPi (ITree.bind t k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp".
    iLöb as "IH" forall (t Φ).
    iApply wpi_update. rewrite /wpi wpi_opt_unfold.
    iMod "Hwp" as "[[%Ht Hfupd]|[[%r [%Hret Hwp]]|[[%t' [%Heq Hwp]]|(%A&%e&%k'&%Heq&Hwp)]]]".
    - iModIntro. apply eqit_inv_bind_ret in Ht as [r [_ [=]%eqitree_inv_Ret]].
    - iModIntro. apply eqit_inv_bind_ret in Hret as [r' [-> [=->]%eqitree_inv_Ret]].
      by rewrite bind_ret_l.
    - apply eqitree_inv_bind_tau in Heq as [[t'' [-> Hbind]] | [t'' [_ Hcontr]]].
      * rewrite bind_tau. iApply wpi_tau. rewrite -Hbind. iModIntro. iNext. by iApply "IH".
      * apply eqitree_inv_Tau_r in Hcontr as [t0 [[=] _]].
    - apply eqitree_inv_bind_vis in Heq as [[t'' [Ht Hbind]] | [t'' [_ Hcontr]]].
      * rewrite Ht bind_vis. iApply wpi_vis'. iModIntro.
        iApply bi_mono1_mono_l; [|iApply (bi_mono1_mono with "[] Hwp")].
        + iIntros (Q) "Hwp". iApply bi_mono1_pers_mono; last done. iModIntro.
          iIntros (t') "Hwp". iNext. iMod "Hwp". iModIntro.
          rewrite /wpi wpi_opt_always_None map_map //.
        + iIntros (a) "Hwp". iNext. iApply "IH". rewrite -Hbind //.
      * apply eqitree_inv_Vis_r in Hcontr as [t0 [[=] _]].
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
  Context {Σ : gFunctors} `{!invGS_gen HasNoLc Σ}.
  Context `{!EventFixpoint EF1 E1} `{!EventFixpoint EF2 E2}.
  Context {H1 : iHandler Σ EF1} {H2 : iHandler Σ EF2}.
  Context {f : E1 ~> itree E2}.

  (* Translation lemma. *)

  (** The following lemma allow you to relate weakest preconditions across
  [iHandler]s. Specifically, if you have a function [f] that interprets each
  event [E1 A] as an [itree E2 A], that is, a way to "translate" from events
  [E1] to [E2], then you may want to relate [WPI t @ H1 {{ Φ }}] to [WPI
  interp f t @ H1 {{ Φ }}] for itrees [t]. The following statement gives you
  sufficient conditions for when one implies the other. *)
  Lemma wp_translation {R} :
    □ (∀ A e Φ Φ' s, (∀ v, Φ v -∗ Φ' v) -∗ H1 E1 A e Φ s -∗ H1 E1 A e Φ' s) -∗
    □ (∀ A e Φ s s', (∀ v, s v -∗ s' v) -∗ H1 E1 A e Φ s -∗ H1 E1 A e Φ s') -∗
    □ (∀ A (e : E1 A) ψ,
         H1 E1 A (subevent A e)
           (λ a, ▷ ψ a)
           (λ t', ▷ |={⊤, ∅}=> WPi interp f t' @ H2 {{ λ _, |={∅, ⊤}=> True }}) -∗
         WPi (f A e) @ H2 {{ v, ψ v }}
      ) -∗
    ∀ (t : itree E1 R) Φ, WPi t @ H1 {{ Φ }} -∗ WPi (interp f t) @ H2 {{ Φ }}.
  Proof.
    iIntros "#HmonΦ #Hmons #HH". iLöb as "IH" forall (R).
    iIntros (t Φ) "Hwp".
    rewrite /wpi wpi_opt_unfold.
    iApply wpi_update.
    iMod "Hwp" as "[[%Ht Hfupd]|[[%r [%Hret Hwp]]|[[%t' [%Heq Hwp]]|(%A&%e&%k'&%Heq&Hwp)]]]";
    iModIntro.
    - apply eqit_inv_bind_ret in Ht as [_ [_ [=]%eqitree_inv_Ret]].
    - apply eqit_inv_bind_ret in Hret as [r' [-> [=->]%eqitree_inv_Ret]].
      rewrite interp_ret. by iApply wpi_ret.
    - apply eqitree_inv_bind_tau in Heq as [[t'' [-> Hbind]] | [t'' [_ Hcontr]]].
      * rewrite interp_tau -Hbind. iApply wpi_tau. iNext. by iApply "IH".
      * apply eqitree_inv_Tau_r in Hcontr as [t0 [[=] _]].
    - apply eqitree_inv_bind_vis in Heq as [[t'' [-> Hbind]] | [t'' [_ Hcontr]]].
      * rewrite interp_vis. iApply wpi_bind. iApply "HH".
        iDestruct (bi_mono1_elim with "[] Hwp") as "Hwp".
        + iIntros (Q) "HQ Hwp". iDestruct (bi_mono1_pers_elim with "[] Hwp") as "Hwp".
          ++ iModIntro. iIntros (Q') "HQ'". iApply "Hmons". iApply "HQ'".
          ++ iApply bi_mono1_pers_intro0. by iApply ("HmonΦ" with "[HQ]").
        + iDestruct (bi_mono1_pers_elim with "[] Hwp") as "Hwp".
          ++ iModIntro. iIntros (Q') "HQ'". iApply "Hmons". iApply "HQ'".
          ++ iApply "HmonΦ"; last iApply "Hmons"; last done.
             +++ iIntros (a) "Hwp". iNext. iApply wpi_tau. iApply "IH". by rewrite -!Hbind.
             +++ iIntros (t''') "Hwp". iNext. iMod "Hwp". iModIntro.
                 iApply "IH". by rewrite wpi_opt_always_None map_map.
      * apply eqitree_inv_Vis_r in Hcontr as [t0 [[=] _]].
  Qed.
End translation.
