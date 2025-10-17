From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From elpi.apps Require Import locker.
From iris Require Import prelude.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import ghost_map invariants.
From iris.bi Require Import weakestpre.

From iris.itree Require Import wpi choice ub heap handler itree.
From iris.itree.threadpool Require Import handler.
From iris.itree.examplelang Require Import lang.

Class exampleHGpreS (Σ : gFunctors) := ExampleHGpreS {
  exampleH_heapHG :> heapHGpreS Σ val;
}.
Global Existing Instances exampleH_heapHG.
Class exampleHGS (Σ : gFunctors) := ExampleHGS {
  exampleH_heapHGS :> heapHGS Σ val;
}.
Global Existing Instances exampleH_heapHGS.

Section handler.
  Context {Σ} `{!invGS_gen hlc Σ} `{!exampleHGS Σ}.

  Definition exampleH : iHandler Σ exampleE :=
    threadpoolH ⊕ ubH ⊕ heapH val ⊕ demonicH.

  Lemma wpi_yield_if_not_val e Φ :
    Φ tt -∗
    WPi yield_if_not_val e @ exampleH; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /yield_if_not_val.
    case_match; try by iApply @wpi_yield.
    by iApply wpi_ret.
  Qed.
End handler.

(** Weakest precondition abstraction for ExampleLang expressions. *)
lock Definition wp_example `{!invGS_gen hlc Σ} `{!exampleHGS Σ} :
  Wp (iProp Σ) expr val stuckness := λ _ E e Φ,
    (WPi compile_expr e @ exampleH; E {{ Φ }})%I.
Global Existing Instance wp_example.

Section wp.
  Context `{!invGS_gen hlc Σ} `{!exampleHGS Σ}.

  Lemma wp_unfold e E Φ :
    WP e @ E {{ Φ }} ⊣⊢
    WPi compile_expr e @ exampleH; E {{ Φ }}.
  Proof. by rewrite unlock. Qed.

  Lemma wp_atomic E1 E2 e Φ :
    (|={E1,E2}=> WP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    setoid_rewrite <- wpi_clear_mask. iMod "Hwp".
    iApply wpi_wand; last done. iIntros (r) "HΦ". by iMod "HΦ".
  Qed.

  Lemma wp_wand E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) -∗
    WP e @ E {{ Φ }} -∗ WP e @ E {{ Ψ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    by iApply wpi_wand.
  Qed.

  Lemma wp_frame P E e Φ :
    P -∗
    WP e @ E {{ Φ }} -∗ WP e @ E {{ v, P ∗ Φ v }}.
  Proof.
    iIntros "HP Hwp". iApply (wp_wand with "[HP]"); last eauto.
    iIntros (v) "HΦ". iFrame.
  Qed.

  Lemma wp_val E v Φ :
    Φ v -∗
    WP Val v @ E {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. wpi_norm/=.
    by iApply wpi_ret.
  Qed.

  Lemma wp_bind_plus_l e1 e2 Φ :
    WP e1 @ ⊤ {{ v1, WP (Plus (Val v1) e2) @ ⊤ {{ Φ }} }} -∗
    WP Plus e1 e2 @ ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. rewrite rec_as_interp.
    iApply wpi_wand; last done.
    iIntros (r) "Hwp". iApply wpi_bind. iApply wpi_yield_if_not_val.
    rewrite !wp_unfold. rewrite /compile_expr rec_as_interp. by wpi_norm/= in "Hwp".
  Qed.

  Lemma wp_bind_plus_r v1 e2 Φ :
    WP e2 @ ⊤ {{ v2, WP (Plus (Val v1) (Val v2)) @ ⊤ {{ Φ }} }} -∗
    WP Plus (Val v1) e2 @ ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. rewrite rec_as_interp.
    iApply wpi_wand; last done.
    iIntros (r) "Hwp". iApply wpi_bind. iApply wpi_yield_if_not_val.
    rewrite !wp_unfold. rewrite /compile_expr rec_as_interp. by wpi_norm/= in "Hwp".
  Qed.

  Lemma wp_plus E n m Φ :
    Φ (LitV (LitInt (n + m))) -∗
    WP Plus (Val (LitV (LitInt n))) (Val (LitV (LitInt m))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite wp_unfold.
    rewrite /compile_expr. wpi_norm/=. by iApply wpi_ret.
  Qed.

  Lemma wp_app x_ v e Φ :
    WP subst' x_ v  e @ ⊤ {{ Φ }} -∗
    WP App (Val (LamV x_ e)) (Val v) @ ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply wpi_yield_if_not_val.
    rewrite interp_recursive_call //.
  Qed.

  Lemma wp_if_true e1 e2 (n : Z) Φ :
    n ≠ 0 →
    WP e1 @ ⊤ {{ Φ }} -∗
    WP If (Val (LitV (LitInt n))) e1 e2 @ ⊤ {{ Φ }}.
  Proof.
    iIntros (Hneq) "Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. wpi_norm/=. rewrite decide_True //.
    wpi_norm/=. iApply wpi_bind. iApply wpi_yield_if_not_val.
    rewrite rec_as_interp //.
  Qed.

  Lemma wp_if_false e1 e2 Φ :
    WP e2 @ ⊤ {{ Φ }} -∗
    WP If (Val (LitV (LitInt 0))) e1 e2 @ ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. wpi_norm/=.
    wpi_norm/=. iApply wpi_bind. iApply wpi_yield_if_not_val.
    rewrite rec_as_interp //.
  Qed.

  Lemma wp_ref E v Φ :
    ↑heapH_inv_name ⊆ E →
    (∀ l,
       l ↦ v -∗
       Φ (LitV (LitLoc l)))
    -∗
    WP Ref (Val v) @ E {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hwand".
    rewrite wp_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. wpi_norm. iApply @wpi_alloc; first done.
    iIntros (l) "Hpointsto". iApply wpi_ret.
    by iApply "Hwand".
  Qed.

  Lemma wp_load E l v dq Φ :
    ↑heapH_inv_name ⊆ E →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ v) -∗
    WP Load (Val $ LitV $ LitLoc l) @ E {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hmapsto Hwand".
    rewrite wp_unfold /compile_expr. wpi_norm/=.
    by iApply (@wpi_load_or_ub with "Hmapsto").
  Qed.

  Lemma wp_store E l v v' Φ :
    ↑heapH_inv_name ⊆ E →
    l ↦ v -∗
    (l ↦ v' -∗ Φ v) -∗
    WP Store (Val $ LitV $ LitLoc l) (Val v') @ E {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hmapsto Hwand".
    rewrite wp_unfold /compile_expr. wpi_norm/=.
    by iApply (@wpi_store_or_ub with "Hmapsto").
  Qed.

  Lemma wp_pick_int E Φ :
    (∀ n, Φ (LitV (LitInt n))) -∗
    WP PickInt @ E {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_demonic.
    iIntros (n). by iApply wpi_ret.
  Qed.

  Lemma wp_spawn E e Φ :
    Φ (LitV (LitInt 0))  -∗
    WP e @ ⊤ {{ _, True }} -∗
    WP Spawn e @ E {{ Φ }}.
  Proof.
    iIntros "HΦ Hwp". rewrite !wp_unfold.
    rewrite /compile_expr. (* TODO: Make this work: Set Typeclasses Debug Verbosity 2. wpi_norm/=. *)
    wpi_norm/=. iApply wpi_bind. iApply (@wpi_spawn with "[HΦ]").
    - by iApply wpi_ret.
    - wpi_norm/=. iApply wpi_bind. rewrite rec_as_interp. iApply wpi_wand; last done.
      iIntros (r) "_". iApply wpi_bind. iApply wpi_yield_if_not_val. by iApply wpi_ret.
  Qed.
End wp.
