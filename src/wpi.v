From iris.bi Require Import fixpoint.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Import fancy_updates.
From iris.base_logic.lib Require Import invariants.
From iris.itree Require Import handler.
From iris.itree Require Import itree.
From ITree Require Import ITree.
From ITree Require Import CategoryFunctor.
From ITree Require Import Interp.InterpFacts.
From ITree Require Import Interp.TranslateFacts.
From ITree Require Import Eq.
From ITree Require Import Eqit.
From Paco Require Import paco.
From elpi.apps Require Import locker.
Require Import Coq.Program.Equality.

Section wp_itree.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.

  (** The definition of the weakest precondition, prior to taking the fixpoint. *)
  (* TODO: Uncurry this, and don't use the -n> to iProp *)
  Definition wpiF (H : iHandler Σ E)
    (wpi : discreteO (itree E R) -> (leibnizO R -> iPropO Σ) -> iPropO Σ) :
           discreteO (itree E R) -> (leibnizO R -> iPropO Σ) -> iPropO Σ :=
    λ t Φ,
      (|={∅}=>
        match observe t with
        | RetF r  => Φ r
        | TauF t' => wpi t' Φ
        | VisF e k => H _ e
            (λ a, wpi (k a) Φ)
            (λ a, |={⊤, ∅}=> wpi (k a) (λ _, False))
        end
      )%I.
  Definition wpiF' (H : iHandler Σ E)
    (wpi : discreteO (itree E R) * (leibnizO R -d> iPropO Σ) -> iPropO Σ) :
           discreteO (itree E R) * (leibnizO R -d> iPropO Σ) -> iPropO Σ :=
    λ pair, let (t, Φ) := pair in wpiF H (curry wpi) t Φ.

  Global Instance wpiF_ne n H :
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) (wpiF' H).
  Proof.
    intros wp1 wp2 Hwp [t1 Q1] [t2 Q2] [Ht HQ]. rewrite /wpiF'/wpiF.
    destruct (eqit_cases t1 t2 Ht) as [(r&->&->)|[(t1'&t2'&->&->&Ht')|(A&e&k1&k2&->&->&Hk)]].
    - by f_equiv.
    - f_equiv. by apply Hwp.
    - f_equiv. apply handler_ne.
      * intros a. apply Hwp. split; first apply Hk. done.
      * intros a. f_equiv. apply Hwp. split; first apply Hk. done.
  Qed.

  Lemma wpiF_mono H wp1 wp2:
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ)
    → ∀ t Φ, wpiF H wp1 t Φ -∗ wpiF H wp2 t Φ.
  Proof.
    iIntros "#Hwand" (t Φ) "Hwp". rewrite /wpiF. destruct (observe t).
    - done.
    - by iApply "Hwand".
    - iApply ihandler_mono; last done.
      * iIntros (a) "Hwp". by iApply "Hwand".
      * iModIntro. iIntros (t') "Hwp". by iApply "Hwand".
  Qed.
  Lemma wpiF_mono' H wp1 wp2:
    ⊢ □ (∀ t Φ, wp1 (t, Φ) -∗ wp2 (t, Φ))
    → ∀ t Φ, wpiF' H wp1 (t, Φ) -∗ wpiF' H wp2 (t, Φ).
  Proof.
    rewrite /wpiF'. iApply wpiF_mono.
  Qed.

  Global Instance wp_itree_pre_monotone H :
    BiMonoPred (λ wp_itree, wpiF' H wp_itree).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply wpiF_mono'; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - intros wpi HneΦ n [t Φ] [t' Φ'] [Ht HΦ]. rewrite /wpiF'/wpiF. punfold Ht. inversion Ht.
      * simpl in HΦ. rewrite REL //. repeat f_equiv.
      * do 2 f_equiv. split.
        + pclearbot. apply REL.
        + apply HΦ.
      * f_equiv. apply handler_ne.
        + intros a. f_equiv. pclearbot. split.
          ++ apply REL.
          ++ done.
        + intros a. do 2 f_equiv. pclearbot. apply REL.
      * done.
      * done.
  Qed.

  (* TODO: Rename [wpi] to [wpi_no_mask] or something along those lines. *)
  Definition wpi (H : iHandler Σ E) (t : itree E R) (Φ : R → iProp Σ) : iProp Σ :=
    bi_least_fixpoint (wpiF' H) (t, Φ).

  Lemma wpi_unfold H (t : itree E R) Φ :
    wpi H t Φ ⊣⊢ wpiF H (wpi H) t Φ.
  Proof.
    rewrite /wpi. apply: least_fixpoint_unfold.
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

  Global Instance wpi_ne_emp_mask R t :
    NonExpansive (λ Φ : leibnizO R -d> iPropO Σ, (WPi t @ H {{ Φ }})%I).
  Proof.
    intros n Φ1 Φ2 HΦ. rewrite /wpi. apply least_fixpoint_ne; first solve_proper. by split.
  Qed.
  Global Instance wpi_ne_emp_mask' R Φ :
    NonExpansive (λ t : discreteO (itree E R), (WPi t @ H {{ Φ }})%I).
  Proof.
    intros n t1 t2 Ht. rewrite /wpi. apply least_fixpoint_ne; first solve_proper. by split.
  Qed.

  (* Stepping rules. *)

  Lemma wpi_ret_emp_mask' {R} Φ (r : R):
    (|={∅}=> Φ r) ⊣⊢
    WPi Ret r @ H {{ Φ }}.
  Proof.
    rewrite wpi_unfold //.
  Qed.
  Lemma wpi_ret_emp_mask {R} Φ (r : R):
    Φ r -∗
    WPi Ret r @ H {{ Φ }}.
  Proof.
    iIntros "HΦ". by iApply wpi_ret_emp_mask'.
  Qed.

  Lemma wpi_tau_emp_mask {R} Φ (t : itree E R):
    WPi t @ H {{ Φ }} ⊣⊢
    WPi Tau t @ H {{ Φ }}.
  Proof.
    rewrite !wpi_unfold /wpiF. simpl. f_equiv. rewrite wpi_unfold //.
  Admitted.

  Lemma wpi_vis_emp_mask' {R} Φ A (e : E A) (k : A → itree E R):
    (|={∅}=> H A (subevent A e) (λ a, WPi k a @ H {{ Φ }}) (λ a, |={⊤, ∅}=> WPi k a @ H {{ const False }})) ⊣⊢
    WPi (Vis e k) @ H {{ Φ }}.
  Proof.
    rewrite !wpi_unfold /wpiF. simpl. f_equiv.
    iSplit.
    - iIntros "HH". iApply (ihandler_mono with "[] [] [HH //]").
      * eauto.
      * iModIntro. by iIntros (t) "Hwp".
    - iIntros "HH". iApply (ihandler_mono with "[] [] [HH //]").
      * eauto.
      * iModIntro. by iIntros (t) "Hwp".
  Qed.
  Lemma wpi_vis_emp_mask {R} Φ A (e : E A) (k : A → itree E R):
    H A (subevent A e) (λ a, WPi k a @ H {{ Φ }}) (λ a, |={⊤, ∅}=> WPi k a @ H {{ const False }}) -∗
    WPi (Vis e k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp". by iApply wpi_vis_emp_mask'.
  Qed.

  (* Induction principles for WPi. *)

  Lemma wpi_ind_emp_mask {R} (G : discreteO (itree E R) -d> (leibnizO R -d> iPropO Σ) -n> iPropO Σ):
    NonExpansive2 G →
    (□ ∀ t Φ, wpiF H (λ t' Ψ, G t' Ψ ∧ WPi t' @ H {{ Ψ }}) t Φ -∗ G t Φ) -∗
    ∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (t Φ) "Hwp".
    rewrite {2}/wpi.
    iApply (least_fixpoint_ind _ (uncurry G) with "[] Hwp").
    iIntros "!>" ([??]) "Hwp" => /=. by iApply "HPre".
  Qed.

  Lemma wpi_iter_emp_mask {R} (G : discreteO (itree E R) -d> (leibnizO R -d> iPropO Σ) -n> iPropO Σ):
    NonExpansive2 G →
    (□ ∀ t Φ, wpiF H G t Φ -∗ G t Φ) -∗
    ∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply wpi_ind_emp_mask. iIntros "!>" (t Φ) "Hwp".
    iApply "HPre". iApply (wpiF_mono with "[] Hwp").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.
  Lemma wpi_iter_emp_mask' {R} (G : discreteO (itree E R) -d> (leibnizO R -d> iPropO Σ) -n> iPropO Σ):
    NonExpansive2 G →
    (□ ∀ Φ r, (|={∅}=> Φ r) -∗ G (Ret r) Φ) -∗
    (□ ∀ Φ t, (|={∅}=> G t Φ) -∗ G (Tau t) Φ) -∗
    (□ ∀ Φ A (e : E A) k, (|={∅}=> H _ e (λ a, G (k a) Φ) (λ a, |={⊤, ∅}=> G (k a) (λ _, False)))
       -∗ G (Vis e k) Φ) -∗
    ∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros "%Hne #HRet #HTau #HVis". iApply (wpi_iter_emp_mask G). iModIntro. iIntros (t Φ).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - iIntros "HΦ". iApply "HRet". rewrite /wpiF //.
    - iIntros "Hwp". iApply "HTau". rewrite /wpiF //.
    - iIntros "Hwp". iApply "HVis". rewrite /wpiF //.
  Qed.

  (* [Proper] instances. *)

  Global Instance wpi_proper_eqit_emp_mask R :
    Proper ((eqit (E:=E) (=) false false) ==> (pointwise_relation R (⊣⊢)) ==> (⊣⊢)) (wpi H).
  Proof.
    intros t1 t2 Hbisim Φ1 Φ2 HΦ.
    rewrite /wpi. apply equiv_dist. intros n. apply least_fixpoint_ne; first solve_proper.
    split; simpl.
    - done.
    - intros r. rewrite HΦ //.
  Qed.

  (* TODO: Don't use instances for temporary class definitions. *)
  Global Instance wpi_ext_unidirectional_emp_mask R :
    Proper (eutt (=) ==> (=) ==> (⊢)) (wpi (R:=R) H).
  Proof.
    iIntros (t1 t2 Hbisim Φ Φ' <-).
    unshelve epose
      (G := λne (t1 : discreteO (itree E R)) (Φ : leibnizO R -d> iPropO Σ), (∀ t2, ⌜t1 ≈ t2⌝ → WPi t2 @ H {{ Φ }})%I);
      try apply _; try solve_proper.
    { clear Φ Hbisim t1 t2. intros n t1 t2 Ht. intros Φ. simpl. do 4 f_equiv. split; by rewrite Ht. }
    iAssert (∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ)%I as "Hint".
    - iApply (wpi_iter_emp_mask G).
      * intros ???????. by repeat f_equiv.
      * clear Φ. iModIntro. iIntros (t Φ) "Hwp". iIntros (t') "%Ht". rewrite wpi_unfold /wpiF.
        punfold Ht. unfold eqit_ in Ht. remember (observe t) as ot. remember (observe t') as ot'.
        iInduction Ht as [ | | | | ] "IH" forall (t t' Heqot Heqot').
        + rewrite REL //.
        + pclearbot. by iApply "Hwp".
        + iApply ihandler_mono; last done.
          ++ iIntros (a) "HG". iApply "HG". pclearbot. iPureIntro. apply REL.
          ++ iModIntro. iIntros (a) "HG". iApply "HG". pclearbot. iPureIntro. apply REL.
        + iMod "Hwp".  iSpecialize ("Hwp" $! t'). unshelve iSpecialize ("Hwp" $! _).
          { pfold. rewrite /eqit_ -Heqot' //. }
          rewrite Heqot'. rewrite wpi_unfold/wpiF //.
        + rewrite wpi_unfold/wpiF. iModIntro. by iApply "IH".
    - iIntros "Hwp". rewrite /G. simpl. iSpecialize ("Hint" with "Hwp"). by iApply "Hint".
  Qed.
  Global Instance wpi_proper_emp_mask R :
    Proper (eutt (=) ==> (pointwise_relation R (⊣⊢)) ==> (⊣⊢)) (wpi (E:=E) (R:=R) H).
  Proof.
    intros t1 t2 Hbisim Φ1 Φ2 HΦ.
    iSplit.
    - iIntros "Hwp". rewrite Hbisim HΦ //.
    - iIntros "Hwp". rewrite Hbisim HΦ //.
  Qed.
  Global Instance wpi_proper_emp_mask' R :
    Proper (eqit (=) false false ==> (pointwise_relation R (⊣⊢)) ==> (⊣⊢)) (wpi (E:=E) (R:=R) H).
  Proof.
    intros t1 t2 Hbisim Φ1 Φ2 HΦ.
    iSplit.
    - iIntros "Hwp". rewrite Hbisim HΦ //.
    - iIntros "Hwp". rewrite Hbisim HΦ //.
  Qed.

  (* Structural rules. *)

  Lemma wpi_update_emp_mask {R} Φ (t : itree E R) :
    (|={∅}=> WPi t @ H {{ Φ }}) ⊣⊢
    (WPi t @ H {{ Φ }}).
  Proof.
    iSplit.
    - iIntros "Hwp". rewrite wpi_unfold. by iMod "Hwp".
    - iIntros "Hwp". rewrite wpi_unfold. by iMod "Hwp".
  Qed.

  Lemma wpi_upd_wand_emp_mask {R} (t : itree E R) Φ Ψ:
    (∀ r, (|={∅}=> Φ r) -∗ (|={∅}=> Ψ r)) -∗
    WPi t @ H {{ Φ }} -∗
    WPi t @ H {{ Ψ }}.
  Proof.
    iIntros "Hwand Hwp".
    unshelve epose (G := (λne (t : discreteO (itree E R)) (Φ : leibnizO R -d> iPropO Σ), ∀ Ψ, (∀ r : R, (|={∅}=> Φ r) -∗ (|={∅}=> Ψ r)) -∗ WPi t @ H {{ Ψ }})%I); try apply _; try solve_proper.
    { clear. intros n t1 t2 Ht Φ. simpl. do 3 f_equiv. by rewrite Ht. }
    iAssert (∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { rewrite /G. simpl. iApply ("Hgen" with "Hwp Hwand"). }
    iApply (wpi_iter_emp_mask' G); clear.
    - intros ???????. by repeat f_equiv.
    - iModIntro. iIntros (Φ r) "HΦ". iIntros (Φ') "Hwand". rewrite -wpi_ret_emp_mask'.
      by iApply "Hwand".
    - iModIntro. iIntros (Φ t) "HG". iIntros (Ψ) "Hwand". rewrite -wpi_tau_emp_mask.
      iApply wpi_update_emp_mask. iMod "HG". by iApply "HG".
    - iModIntro. iIntros (Φ A e k) "HG". iIntros (Ψ) "Hwand". rewrite -wpi_vis_emp_mask'.
      iApply (ihandler_mono with "[Hwand]"); last done.
      * iIntros (a) "HG". by iApply "HG".
      * iModIntro. iIntros (a) "HG". iMod "HG". iApply "HG". eauto.
  Qed.
  Lemma wpi_wand_emp_mask {R} (t : itree E R) Φ Ψ:
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @ H {{ Φ }} -∗
    WPi t @ H {{ Ψ }}.
  Proof.
    iIntros "Hwand Hwp". iApply (wpi_upd_wand_emp_mask with "[Hwand]"); last done.
    iIntros (r) "HΦ". by iApply "Hwand".
  Qed.

  Lemma wpi_update_post_emp_mask {R} Φ (t : itree E R) :
    (WPi t @ H {{ v, |={∅}=> Φ v }}) ⊣⊢
    (WPi t @ H {{ Φ }}).
  Proof.
    iSplit.
    - iIntros "Hwp". iApply wpi_upd_wand_emp_mask; last done. iIntros (r) "Hwp". by iMod "Hwp".
    - iIntros "Hwp". iApply wpi_upd_wand_emp_mask; last done. iIntros (r) "Hwp". by iMod "Hwp".
  Qed.

  Lemma wpi_bind_emp_mask {R T} (t : itree E T) (k : T → itree E R) Φ :
    WPi t @ H {{ r, WPi (k r) @ H {{ Φ }} }} -∗
    WPi (ITree.bind t k) @ H {{ Φ }}.
  Proof.
    iIntros "Hwp".
    unshelve epose (G := (λne (t : discreteO (itree E T)) (Φ : leibnizO T -d> iPropO Σ), ∀ (Ψ : R → iProp Σ) k, (∀ x : T, Φ x -∗ WPi (k x) @ H {{ Ψ }}) -∗ WPi (ITree.bind t k) @ H {{ Ψ }})%I); try apply _; try solve_proper.
    { clear. intros n t1 t2 Ht Φ. simpl. do 5 f_equiv. apply wpi_ne_emp_mask'. by apply eqit_bind. }
    iAssert (∀ t Φ, WPi t @ H {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { rewrite /G. simpl. iApply ("Hgen" with "Hwp"). eauto. }
    iApply (wpi_iter_emp_mask' G); clear.
    - intros ???????. by repeat f_equiv.
    - iModIntro. rewrite /G. iIntros (Φ x) "HΦ". iIntros (Ψ k) "Hwp". rewrite bind_ret_l.
      iApply wpi_update_emp_mask. by iApply "Hwp".
    - iModIntro. iIntros (Φ t) "HG". rewrite /G. iIntros (Ψ k) "Hwp".
      rewrite bind_tau -wpi_tau_emp_mask. iApply wpi_update_emp_mask. iMod "HG". by iApply "HG".
    - iModIntro. iIntros (Φ A e k) "HH". rewrite /G. iIntros (Ψ k') "Hwand".
      rewrite bind_vis -wpi_vis_emp_mask'. iMod "HH". iModIntro.
      iApply (ihandler_mono with "[Hwand] [] HH").
      * clear. simpl. iIntros (a) "Hwp". by iApply "Hwp".
      * iModIntro. iIntros (a) "Hwp". iMod "Hwp". iApply "Hwp". iModIntro. by iIntros (x) "Hfalse".
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

Section wp_itree_mask.
  Context {Σ : gFunctors} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.
  Context {H : iHandler Σ E}.

  lock Definition wpi_mask {R} (M : coPset) (t : itree E R) (Φ : R → iProp Σ) : iProp Σ :=
    (|={M, ∅}=> wpi H t%itree (λ v, |={∅, M}=> Φ v))%I.

  (* Properness lemmata. *)

  Global Instance wpi_proper R M :
    Proper (eutt (=) ==> (pointwise_relation R (⊣⊢)) ==> (⊣⊢)) (wpi_mask (R:=R) M).
  Proof.
    intros t1 t2 Ht Φ1 Φ2 HΦ. rewrite /wpi_mask unlock. f_equiv. rewrite Ht. by setoid_rewrite HΦ.
  Qed.
  Global Instance wpi_proper' R M :
    Proper (eqit (=) false false ==> (pointwise_relation R (⊣⊢)) ==> (⊣⊢)) (wpi_mask (R:=R) M).
  Proof.
    intros t1 t2 Ht Φ1 Φ2 HΦ. rewrite /wpi_mask. rewrite Ht. by setoid_rewrite HΦ.
  Qed.
End wp_itree_mask.

Notation "'WPi' t @ H ; M {{ v , Q } }" := (wpi_mask (H := H) M t (λ v, Q))
  (at level 20, t, Q at level 200,
   format "'[hv' 'WPi'  t  '/' @  '[' H ; M ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WPi' t @ H ; M {{ Φ } }" := (WPi t @ H; M {{ v, Φ v }})%I
  (at level 20, t, Φ at level 200, only parsing) : bi_scope.

Section wp_itree_mask.
  Context {Σ : gFunctors} {E : Type → Type} `{!invGS_gen HasNoLc Σ}.
  Context {H : iHandler Σ E}.

  (* Nonexpansiveness lemmata. *)
  Global Instance wpi_proper_dist R M n :
    Proper (eqit (=) false false ==> (pointwise_relation R (dist n)) ==> (dist n)) (wpi_mask (E:=E) (H:=H) (R:=R) M).
  Proof.
    intros t1 t2 Ht Φ1 Φ2 HΦ. rewrite /wpi_mask unlock Ht. f_equiv. apply wpi_ne_emp_mask.
    intros v. by f_equiv.
  Qed.

  (* Induction principles for WPi. *)

  Lemma wpi_ind {R} (G : discreteO (itree E R) -d> (leibnizO R -d> iPropO Σ) -n> iPropO Σ):
    NonExpansive2 G →
    (□ ∀ t Φ, wpiF H (λ t' Ψ, G t' Ψ ∧ WPi t' @ H; ∅ {{ Ψ }}) t Φ -∗ G t Φ) -∗
    ∀ t Φ, WPi t @ H; ∅ {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HG". iIntros (t Φ) "Hwp". rewrite /wpi_mask unlock.
    rewrite wpi_update_emp_mask wpi_update_post_emp_mask.
    iApply wpi_ind_emp_mask; last done. iModIntro. clear. iIntros (t Φ) "Hwp". iApply "HG".
    iApply wpiF_mono; last done. iModIntro. clear. iIntros (t Φ) "Hwp". iSplit.
    - iDestruct "Hwp" as "[$ _]".
    - iDestruct "Hwp" as "[_ Hwp]". rewrite wpi_update_emp_mask wpi_update_post_emp_mask //.
  Qed.

  Lemma wpi_iter {R} (G : discreteO (itree E R) -d> (leibnizO R -d> iPropO Σ) -n> iPropO Σ):
    NonExpansive2 G →
    (□ ∀ t Φ, wpiF H G t Φ -∗ G t Φ) -∗
    ∀ t Φ, WPi t @ H; ∅ {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply wpi_ind. iIntros "!>" (t Φ) "Hwp".
    iApply "HPre". iApply (wpiF_mono with "[] Hwp").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.
  Lemma wpi_iter' {R} (G : discreteO (itree E R) -d> (leibnizO R -d> iPropO Σ) -n> iPropO Σ):
    NonExpansive2 G →
    (□ ∀ Φ r, (|={∅}=> Φ r) -∗ G (Ret r) Φ) -∗
    (□ ∀ Φ t, (|={∅}=> G t Φ) -∗ G (Tau t) Φ) -∗
    (□ ∀ Φ A (e : E A) k, (|={∅}=> H _ e (λ a, G (k a) Φ) (λ a, |={⊤, ∅}=> G (k a) (λ _, False)))
       -∗ G (Vis e k) Φ) -∗
    ∀ t Φ, WPi t @ H; ∅ {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros "%Hne #HRet #HTau #HVis". iApply (wpi_iter G). iModIntro. iIntros (t Φ).
    destruct (itree_match t) as [[r ->]|[[t' ->]|[A [e [k ->]]]]].
    - iIntros "HΦ". iApply "HRet". rewrite /wpiF //.
    - iIntros "Hwp". iApply "HTau". rewrite /wpiF //.
    - iIntros "Hwp". iApply "HVis". rewrite /wpiF //.
  Qed.

  (* Structural rules. *)

  Lemma wpi_wand {R} (t : itree E R) M Φ Ψ :
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @ H; M {{ Φ }} -∗
    WPi t @ H; M {{ Ψ }}.
  Proof.
    iIntros "HΦΨ Hwp". rewrite /wpi_mask unlock. iApply (wpi_wand_emp_mask with "[HΦΨ]").
    - iIntros (r) "Hgoal". by iApply "HΦΨ".
    - done.
  Qed.

  Lemma wpi_bind {R A} (t : itree E A) (k : A → itree E R) M Φ :
    WPi t @ H; M {{ r, WPi (k r) @ H; M {{ Φ }} }} -∗
    WPi (ITree.bind t k) @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite /wpi_mask unlock. iApply wpi_bind_emp_mask. iMod "Hwp".
    iApply wpi_wand_emp_mask; last done.
    iIntros (a) "Hwp". iApply wpi_update_emp_mask. by iMod "Hwp".
  Qed.

  Lemma wpi_update {R} M Φ (t : itree E R) :
    (|={M}=> WPi t @ H; M {{ Φ }}) ⊣⊢
    (WPi t @ H; M {{ Φ }}).
  Proof.
    iSplit.
    - iIntros "Hwp". rewrite /wpi_mask unlock. by iMod "Hwp".
    - iIntros "Hwp". by iModIntro.
  Qed.

  Lemma wpi_update_post {R} M Φ (t : itree E R) :
    (WPi t @ H; M {{ v, |={M}=> Φ v }}) ⊣⊢
    (WPi t @ H; M {{ Φ }}).
  Proof.
    iSplit.
    - iIntros "Hwp". rewrite /wpi_mask unlock. iApply wpi_wand_emp_mask; last done.
      iIntros (r) "HΦ". by iMod "HΦ".
    - iIntros "Hwp". rewrite /wpi_mask unlock. iApply wpi_wand_emp_mask; last done.
      iIntros (r) "HΦ". by iMod "HΦ".
  Qed.

  (* Manipulating masks and invariants. *)

  (* TODO: Rename from "reduce" to something else. *)
  Lemma wpi_reduce_mask {R} M' M (Φ : R → iProp Σ) t :
    (|={M, M'}=> WPi t @ H; M' {{ v, |={M', M}=> Φ v }}) -∗
    WPi t @ H; M {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite /wpi_mask unlock. iMod "Hwp". iMod "Hwp". iModIntro.
    iApply wpi_wand_emp_mask; last done.
    iIntros (r) "Hgoal". iMod "Hgoal". by iMod "Hgoal".
  Qed.

  Lemma wpi_clear_mask {R} M (Φ : R → iProp Σ) t :
    (|={M, ∅}=> WPi t @ H; ∅ {{ v, |={∅, M}=> Φ v }}) ⊣⊢
    WPi t @ H; M {{ Φ }}.
  Proof.
    iSplit.
    - iIntros "Hwp". by iApply wpi_reduce_mask.
    - iIntros "Hwp". rewrite /wpi_mask unlock. iMod "Hwp". iModIntro. iApply wpi_wand_emp_mask; last done.
      by iIntros (r) "HΦ".
  Qed.
  Lemma wpi_clear_mask_false {R} M (t : itree E R) :
    (|={M, ∅}=> WPi t @ H; ∅ {{ _, False }}) -∗
    WPi t @ H; M {{ _, False }}.
  Proof.
    iIntros "Hwp". iApply wpi_clear_mask. iMod "Hwp". iModIntro. iApply wpi_wand; last done.
    by iIntros (r) "Hfalse".
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
    iIntros (Hsubset) "Hwp Hinv". rewrite /wpi_mask unlock.
    iMod (own_inv_acc _ with "Hinv") as "[HP Hclose]"; first done.
    iSpecialize ("Hwp" with "HP").
    iMod "Hwp". iModIntro. iApply (wpi_wand_emp_mask with "[Hclose] [Hwp //]").
    iIntros (r) "HP". iMod "HP" as "[HP HΦ]". by iMod ("Hclose" with "HP").
  Qed.

  (* Stepping rules. *)

  Lemma wpi_ret' {R} M Φ (r : R):
    (|={M}=> Φ r) ⊣⊢
    WPi Ret r @ H; M {{ Φ }}.
  Proof.
    rewrite /wpi_mask unlock -wpi_ret_emp_mask'.
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

  Lemma wpi_tau {R} M Φ (t : itree E R):
    (WPi t @ H; M {{ v, Φ v }}) ⊣⊢
    WPi Tau t @ H; M {{ Φ }}.
  Proof.
    rewrite /wpi_mask unlock -wpi_tau_emp_mask //.
  Qed.

  Lemma wpi_vis' {R} M Φ A (e : E A) (k : A → itree E R) :
    (|={M, ∅}=> H A (subevent A e) (λ a, WPi k a @ H; ∅ {{ v, |={∅, M}=> Φ v }}) (λ a, WPi k a @ H; ⊤ {{ _, False }})) ⊣⊢
    WPi (Vis e k) @ H; M {{ Φ }}.
  Proof.
    rewrite /wpi_mask unlock -wpi_vis_emp_mask'.
    iSplit.
    - iIntros "HH". iMod "HH". iModIntro. iModIntro.
      iApply (ihandler_mono with "[] [] [HH //]").
      * iIntros (a) "Hwp". iApply wpi_update_emp_mask. iMod "Hwp". iModIntro.
        by iApply wpi_update_post_emp_mask.
      * iModIntro. iIntros (t) "Hwp". iApply wpi_update_post_emp_mask.
        iApply wpi_wand_emp_mask; last done. iIntros (r) "Hfalse". by iMod "Hfalse".
    - iIntros "HH". do 2 iMod "HH". iModIntro.
      iApply (ihandler_mono with "[] [] [HH //]").
      * iIntros (a) "Hwp". by iApply wpi_update_post_emp_mask.
      * iModIntro. iIntros (t) "Hwp". iApply wpi_update_post_emp_mask.
        iApply wpi_wand_emp_mask; last done. by iIntros (r) "Hfalse".
  Qed.
  Lemma wpi_vis {R} M Φ A (e : E A) (k : A → itree E R):
    (|={M, ∅}=> H A e (λ a, WPi k a @ H; ∅ {{ v, |={∅, M}=> Φ v }}) (λ a, WPi k a @ H; ⊤ {{ const False }})) -∗
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

  (** The following lemma allows you to relate weakest preconditions across
  [iHandler]s. Specifically, if you have a function [f] that interprets each
  event [E1 A] as an [itree E2 A], that is, a way to "translate" from events
  [E1] to [E2], then you may want to relate [WPI t @ H1 {{ Φ }}] to [WPI
  interp f t @ H1 {{ Φ }}] for itrees [t]. The following statement gives you
  sufficient conditions for when one implies the other. *)
  Lemma wpi_translation_emp_mask {R} (t : itree E1 R) Φ :
    □ (∀ A (e : E1 A) (k : A → itree E1 R) Q,
         H1 A (subevent A e)
           (λ a, WPi interp f (k a) @ H2; ∅ {{ Q }})
           (λ a, |={⊤, ∅}=> WPi interp f (k a) @ H2; ∅ {{ λ _, False }}) -∗
         WPi ITree.bind (f A e) (λ a, interp f (k a)) @ H2; ∅ {{ Q }}
      ) -∗
    WPi t @ H1; ∅ {{ Φ }} -∗ WPi (interp f t) @ H2; ∅ {{ Φ }}.
  Proof.
    iIntros "#HH Hwp".
    unshelve epose (G := (λne (t : discreteO (itree E1 R)) (Φ : leibnizO R -d> iPropO Σ), WPi (interp f t) @ H2; ∅ {{ Φ }})%I); try apply _; try solve_proper.
    iApply (wpi_iter' G); first solve_proper; clear.
    - iModIntro. iIntros (Φ r) "Hwp". rewrite /G. simpl. rewrite interp_ret -!wpi_ret' //.
    - iModIntro. iIntros (Φ r) "Hwp". rewrite /G. simpl.
      rewrite interp_tau -!wpi_tau wpi_update //.
    - iModIntro. iIntros (Φ' A e k) "Hwp". rewrite /G. simpl. rewrite interp_vis.
      rewrite bind_tau_r. iApply wpi_update. by iApply "HH".
    - done.
  Qed.

  Lemma wpi_translation {R} (t : itree E1 R) M Φ :
    □ (∀ A (e : E1 A) (k : A → itree E1 R) Q,
         H1 A (subevent A e)
           (λ a, WPi interp f (k a) @ H2; ∅ {{ Q }})
           (λ a, WPi interp f (k a) @ H2; ⊤ {{ λ _, False }}) -∗
         WPi ITree.bind (f A e) (λ a, interp f (k a)) @ H2; ∅ {{ Q }}
      ) -∗
    WPi t @ H1; M {{ Φ }} -∗ WPi (interp f t) @ H2; M {{ Φ }}.
  Proof.
    iIntros "#Hwand Hwp". iApply wpi_clear_mask.
    iApply wpi_translation_emp_mask; last rewrite -wpi_clear_mask //.
    iModIntro. iIntros (A e k Q) "HH".
    iApply wpi_update. iApply wpi_update_post.
    iApply wpi_wand; first shelve.
    iApply "Hwand". iApply ihandler_mono; last done.
    - iIntros (a) "Hwp". rewrite -wpi_update_post //.
    - iModIntro. iIntros (a) "Hwp". iApply wpi_clear_mask. iMod "Hwp". iApply wpi_wand; last done.
      by iIntros (r) "?".
  Unshelve.
    by iIntros (a) "Hwp".
  Qed.

  (** A special case of above translation lemma which has a nicer statement at the
  expense of its weaker hypothesis typically not holding for events that spawn
  new threads. *)
  Lemma wpi_translation_seq {R} (t : itree E1 R) M Φ :
    □ (∀ A (e : E1 A) ψ,
         H1 A (subevent A e)
           (λ a, ψ a)
           (λ _, True) -∗
         WPi (f A e) @ H2; ∅ {{ v, ψ v }}
      ) -∗
    WPi t @ H1; M {{ Φ }} -∗ WPi (interp f t) @ H2; M {{ Φ }}.
  Proof.
    iIntros "#Hwand Hwp". iApply wpi_translation; last done.
    iModIntro. iIntros (A e k Q) "HH". iApply wpi_bind. iApply "Hwand".
    iApply ihandler_mono; last done.
    - by iIntros (a) "?".
    - iModIntro. by iIntros (a) "?".
  Qed.
End translation.

Section inH.
  Context {Σ : gFunctors} `{!invGS_gen HasNoLc Σ}.
  Context {E1 E2 : Type → Type}.
  Context {H1 : iHandler Σ E1} {H2 : iHandler Σ E2}.
  Context `{f : E1 -< E2} `{inH1H2 : inH (f := f) Σ E1 E2 H1 H2}.

  Lemma wpi_inH_emp_mask {R} (t : itree E1 R) Φ :
    WPi t @ H1; ∅ {{ Φ }} ⊣⊢
    WPi translate (λ A e', subevent A e') t @ H2; ∅ {{ Φ }}.
  Proof.
    iSplit.
    - iIntros "Hwp". rewrite translate_to_interp. iApply (wpi_translation (H1 := H1)).
        * iModIntro. iIntros (A e k Q) "HH". rewrite bind_trigger. iApply wpi_vis. iModIntro.
          iApply is_inH. iApply ihandler_mono; last done.
          + iIntros (a) "Hwp". by iApply wpi_update_post.
          + iModIntro. by iIntros (a) "Hwp".
        * done.
    - unshelve epose (G := (λne (t : discreteO (itree E2 R)) (Φ : leibnizO R -d> iPropO Σ), ∀ t', ⌜translate (λ A e', subevent A e') t' ≅ t⌝ → WPi t' @ H1; ∅ {{ Φ }})%I); try apply _; try solve_proper.
      iAssert (∀ t Φ, WPi t @ H2; ∅ {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
      { rewrite /G. simpl. iIntros "Hwp". by iApply ("Hgen" with "Hwp"). }
      iApply (wpi_iter' G); first solve_proper.
      * clear. iModIntro. iIntros (Φ r) "HΦ". iIntros (t Ht). iApply wpi_update.
        apply translate_Ret_inv in Ht as ->. by iApply wpi_ret.
      * clear. iModIntro. iIntros (Φ t) "HG". iIntros (t' Ht). apply translate_Tau_inv in Ht as (t1'&->&Ht).
        rewrite -wpi_tau. iApply wpi_update. iMod "HG". by iApply "HG".
      * clear Φ. iModIntro. iIntros (Φ A e k) "HH". iIntros (t' Ht).
        apply translate_Vis_inv in Ht as (e'&k'&->&->&Hk). iApply wpi_vis.
        iApply is_inH. iApply ihandler_mono; last done.
        + iIntros (a) "HG". iApply wpi_update_post. by iApply "HG".
        + iModIntro. iIntros (a) "HG". iApply wpi_clear_mask_false. by iApply "HG".
  Qed.

  Lemma wpi_inH {R} (t : itree E1 R) M Φ :
    WPi t @ H1; M {{ Φ }} ⊣⊢
    WPi translate (λ A e', subevent A e') t @ H2; M {{ Φ }}.
  Proof.
    rewrite -!(wpi_clear_mask M). f_equiv. apply wpi_inH_emp_mask.
  Qed.
End inH.
