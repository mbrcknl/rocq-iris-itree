From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import itree wpi trace handler.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From ITree Require Import ITree Eqit.

Variant laterE : Type → Type :=
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

Variant later_modality : Set :=
  | Identity
  | Later.

Definition lat {Σ} (m : later_modality) (P : iProp Σ) : iProp Σ :=
  match m with
  | Identity => P
  | Later => ▷ P
  end.

Section lat.
  Lemma lat_mono {Σ} m (Φ Ψ : iProp Σ) :
    (Φ -∗ Ψ) -∗
    lat m Φ -∗ lat m Ψ.
  Proof.
    iIntros "Hwand HΦ". destruct m; by iApply "Hwand".
  Qed.

  Lemma lat_intro {Σ} m (Φ : iProp Σ) :
    Φ -∗
    lat m Φ.
  Proof.
    iIntros "HΦ". by destruct m.
  Qed.

  Lemma lat_sep {Σ} m (Φ Ψ : iProp Σ) :
    lat m Φ -∗
    lat m Ψ -∗
    lat m (Φ ∗ Ψ).
  Proof.
    iIntros "HΦ HΨ". destruct m; iFrame.
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
End handler.

Section wpi_later.
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

End wpi_later.

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

Definition later_ifn {R E} (n : option nat) (t : itree (laterE +' E) R) : itree E (R + later_exhausted) :=
  ITree.iter (λ '(n, t), later_ifn_loop n t) (n, t).

Lemma later_ifn_unfold R E n (t : itree (laterE +' E) R) :
  later_ifn n t ≈ r ← later_ifn_loop n t;
   match r with
   | inl nt => later_ifn nt.1 nt.2
   | inr r => Ret r
   end.
Proof. rewrite /later_ifn unfold_iter. f_equiv => -[[??]|//]. by rewrite tau_eutt. Qed.

Section adequacy.
  Context {R : Type} {E : Type → Type}.
  Context `{!invGS Σ} {H : iHandler Σ E}.

  Theorem later_adequacy_empty (t : itree (laterE +' E) R) lat Φ n `{!Sequential H}:
    (lat = Later ↔ is_Some n) →
    WPi t @ laterH lat ⊕ H; ∅ {{ Φ }} -∗
    £ (default 0 n) -∗
    WPi later_ifn n t @ H; ∅ {{ r,
      match r with
      | inl r => Φ r
      | inr LaterExhausted => ⌜lat = Later⌝
      end
    }}.
  Proof.
    move => Hlat. iIntros "Hwp". iRevert (n Hlat).
    iRevert (t Φ) "Hwp". iApply wpi_iter'; first solve_proper.
    - iIntros "!>" (Φ t) "Hwp". iIntros (n Hlat) "Hlc".
      rewrite later_ifn_unfold /later_ifn_loop/=. wpi_norm. by iApply wpi_ret'.
    - iIntros "!>" (Φ t) "Hwp". iIntros (n Hlat) "Hlc".
      iEval (rewrite later_ifn_unfold /later_ifn_loop/=). wpi_norm/=.
      iApply wpi_update. iMod "Hwp". iModIntro. by iApply "Hwp".
    - iIntros "!>" (Φ A [[]|e] k) "HH"; iIntros (n Hlat) "Hlc".
      + iEval (rewrite later_ifn_unfold /later_ifn_loop/=).
        case_bool_decide; wpi_norm/=.
        * iApply wpi_ret'. iModIntro. iPureIntro. naive_solver.
        * iApply wpi_update. iMod "HH". destruct n; simplify_eq/=.
          -- destruct lat; [naive_solver|] => /=. destruct n => //.
             iDestruct "Hlc" as "[? ?]". iApply (lc_fupd_elim_later with "[$]").
             iModIntro. iApply "HH".
             { iPureIntro. rewrite /is_Some. naive_solver. }
             have -> : (S n - 1) = n by lia. iFrame.
          -- destruct lat; [|unfold is_Some in *; naive_solver] => /=.
             iModIntro. by iApply "HH".
      + iEval (rewrite later_ifn_unfold /later_ifn_loop/=).
        rewrite /ITree.map. wpi_norm/=.
        iApply wpi_bind. iApply wpi_trigger. iMod "HH". iModIntro.
        iDestruct (is_seq with "HH") as "HH".
        iApply (ihandler_mono with "[Hlc]"); last done. 2: by iIntros "!>" (??).
        iIntros (a) "Hwp".
        iModIntro. by iApply "Hwp".
  Qed.

  (* TODO: can we get this? *)
  Theorem later_adequacy (t : itree (laterE +' E) R) lat Φ n M `{!Sequential H} :
    (lat = Later ↔ is_Some n) →
    WPi t @ laterH lat ⊕ H; M {{ Φ }} -∗
    £ (default 0 n) -∗
    WPi later_ifn n t @ H; M {{ r,
      match r with
      | inl r => Φ r
      | inr LaterExhausted => ⌜lat = Later⌝
      end
    }}.
  Proof.
    iIntros (?) "Hwp Hlc".
    rewrite -wpi_clear_mask. iEval (rewrite -wpi_clear_mask).
    iMod "Hwp". iModIntro.
    iDestruct (later_adequacy_empty with "Hwp Hlc") as "Hwp"; [done|].
    iApply wpi_wand; last done. iIntros (r). destruct r.
    - eauto.
    - (* Where do we get the mask from? *)
  Abort.
End adequacy.
