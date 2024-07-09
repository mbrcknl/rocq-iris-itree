From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree.threadpool Require Import handler.
From iris.prelude Require Import prelude.
From iris.base_logic Require Import ghost_map invariants.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From elpi.apps Require Import locker.

From iris.itree Require Import wpi choice ub heap handler itree later.
From iris.itree.heaplang Require Export definition lang.

Class heaplangHGpreS (Σ : gFunctors) := HeapLangHGpreS {
  heaplangH_heapHG :> heapHGpreS Σ val;
}.
Local Existing Instances heaplangH_heapHG.
Class heaplangHGS (Σ : gFunctors) := HeapLangHGS {
  heaplangH_heapHGS :> heapHGS Σ val;
}.
Local Existing Instances heaplangH_heapHGS.

Section handler.
  Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  (** The handler for [heaplangE]. *)
  Definition heaplangH m : iHandler Σ heaplangE :=
    threadpoolH ⊕ ubH ⊕ heapH val ⊕ demonicH ⊕ laterH m.

  Lemma wpi_yield_if_not_val m e Φ :
    Φ tt -∗
    WPi yield_if_not_val e @ heaplangH m; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /yield_if_not_val. case_match.
    - by iApply wpi_ret.
    - by iApply @wpi_yield.
  Qed.

  Lemma wpi_compile_expr_yield m e Φ :
    WPi compile_expr e @ heaplangH m; ⊤ {{ Φ }} -∗
    WPi compile_expr_yield e @ heaplangH m; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite /compile_expr_yield. iApply wpi_bind. iApply wpi_wand; last done.
    iIntros (r) "HΦ". iApply wpi_bind. iApply wpi_yield_if_not_val. by iApply wpi_ret.
  Qed.

  Lemma wpi_step_ret m M r Φ :
    lat m (Φ r) -∗
    WPi step_ret r @ heaplangH m; M {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_bind. iApply @wpi_later. iApply lat_mono; last done.
    iIntros "HΦ". by iApply wpi_ret.
  Qed.
End handler.

(** Weakest precondition abstraction for heaplang expressions. *)
lock Definition wp_heaplang `{!invGS_gen hlc Σ} `{!heaplangHGS Σ} :
  Wp (iProp Σ) expr val later_modality := λ m M e Φ,
    (WPi compile_expr e @ heaplangH m; M {{ Φ }})%I.
Global Existing Instance wp_heaplang.

Section wp.
  Context `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  Lemma wp_heaplang_unfold e m M Φ :
    WP e @ m; M {{ Φ }} ⊣⊢
    WPi compile_expr e @ heaplangH m; M {{ Φ }}.
  Proof. by rewrite unlock. Qed.

  (** The total WP implies the partial WP. *)
  Lemma wp_later_weaken e M Φ :
    WP e @ Identity; M {{ Φ }} -∗
    WP e @ Later; M {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold.
    iApply (wpi_wandH (H1 := heaplangH Identity) (H2 := heaplangH Later)).
    by iApply "Hwp".
  Qed.

  (** Bind lemma for [WP].

  Note that this is qualitatively different from the bind lemma familiar from
  typical Iris in that it requires mask [⊤]. One perspective is that this is
  the price we pay for being able to open invariants around any block (no
  atomicity condition). This would be unsound were it not for the bind lemma
  being restricted to the [⊤] mask. Namely, there is no way to show
  [WP e @ m ; M {{ Φ }}] for [M ≠ ⊤] when [e] is not atomic. Another
  perspective is that we need [⊤] mask to account for the [yield] in the
  "semantic bind lemma" [compile_expr_bind]. *)
  Lemma wp_bind_K m K e Φ :
    WP e @ m; ⊤ {{ v,
      WP fill K (Val v) @ m; ⊤ {{ Φ }}
    }} -∗
    WP fill K e @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold.
    destruct (decide (length K = 0)).
    - destruct K => //=. iApply wpi_update_post. iApply wpi_wand; last done.
      iIntros (r) "Hwp". rewrite wp_heaplang_unfold compile_expr_val -wpi_ret'.
      by iApply "Hwp".
    - rewrite compile_expr_bind //. 2: lia. iApply wpi_bind.
      iApply wpi_compile_expr_yield.
      iApply wpi_wand; last done. iIntros (r) "Hwp".
      rewrite wp_heaplang_unfold. by iApply "Hwp".
  Qed.

  (** Rule for changing the mask.

  Contrary to [wp_atomic] in upstream Iris, this rule curiously has no
  atomicity assumption. The burden of this assumption is shifted to the bind
  lemma above, which on the other hand is weaker than its commensurate lemma in
  upstream Iris. See the comment above. *)
  Lemma wp_atomic m E1 E2 e Φ :
    (|={E1,E2}=> WP e @ m; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ m; E1 {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold.
    setoid_rewrite <- wpi_clear_mask. iMod "Hwp".
    iApply wpi_wand; last done. iIntros (r) "HΦ". by iMod "HΦ".
  Qed.

  (* Proof rules for various operations: *)

  Lemma wp_App m f_ x_ v e Φ :
    lat m (WP (subst' x_ v  (subst' f_ (RecV f_ x_ e) e)) @ m; ⊤ {{ Φ }}) -∗
    WP (App (Val (RecV f_ x_ e)) (Val v)) @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "Hwp".
    iModIntro. iApply wpi_bind. iApply wpi_yield_if_not_val.
    rewrite interp_recursive_call //.
  Qed.

  Lemma subst'_val x e v :
    subst' x e (Val v) = Val v.
  Proof.
    rewrite /subst'. by case_match.
  Qed.

  Lemma wp_App_const m M f_ x_ v w Φ :
    lat m (Φ w) -∗
    WP (App (Val (RecV f_ x_ (Val w))) (Val v)) @ m; M {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "Hwp".
    iModIntro. iApply wpi_bind. rewrite !subst'_val. iApply wpi_ret.
    rewrite interp_recursive_call rec_as_interp /= interp_ret. by iApply wpi_ret.
  Qed.

  Lemma wp_Fork m e Φ :
    lat m (Φ (LitV LitUnit)) -∗
    (* TODO: I think this postcondition is unecessarily strong *)
    WP e @ m; ⊤ {{ v, ⌜v = LitV LitUnit⌝ }} -∗
    WP Fork e @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ Hwp". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=.
    rewrite bind_trigger. iApply @wpi_fork. iSplitL "HΦ".
    - wpi_norm. by iApply wpi_step_ret.
    - wpi_norm. rewrite rec_as_interp. iApply wpi_bind.
      iApply wpi_wand; last done. iIntros (r ->).
      iApply wpi_bind. iApply wpi_yield_if_not_val.
      simpl_itree. wpi_norm. rewrite bind_trigger. by iApply @wpi_kill.
  Qed.

  (* TODO: adapt the following lemmas to use WP instead of WPi *)
  Lemma wp_AllocN m M v n Φ :
    (0 < n)%Z →
    ↑heapH_inv_name ⊆ M →
    lat m (∀ l,
       ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v) -∗
       Φ (LitV (LitLoc l))
    ) -∗
    WP AllocN (Val (LitV (LitInt n))) (Val v) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hpos Hmask) "Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite assert_True //. wpi_norm.
    iApply wpi_bind. iApply @wpi_allocN_nondet; first done.
    iIntros (l) "Hpointsto". iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done.
    iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Load m M l v dq Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦{dq} v -∗
    lat m (l ↦{dq} v -∗ Φ v) -∗
    WP Load (Val $ LitV $ LitLoc l) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /load_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_load with "Hpointsto"); first done. iIntros "Hpointsto".
    wpi_norm/=. iApply wpi_step_ret. iApply (lat_mono with "[Hpointsto]"); last done.
    iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Store m M l v v' Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦ v -∗
    lat m (∀ r, ⌜r = LitV (LitUnit)⌝ -∗ l ↦ v' -∗ Φ r) -∗
    WP Store (Val $ LitV $ LitLoc l) (Val v') @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite !wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /store_or_ub/store'_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_store with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=. iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Free m M l v Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦ v -∗
    lat m (Φ (LitV LitUnit)) -∗
    WP Free (Val $ LitV $ LitLoc l) @ m; M {{ Φ }}.
  (* Very slight variant of the proof of [wpi_Store]: *)
  Proof.
    iIntros (Hmask) "Hpointsto HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /store'_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_store' with "Hpointsto"); first done.
    iIntros "_". wpi_norm/=. by iApply wpi_step_ret.
  Qed.

  Lemma wp_Xchg m M l v v' Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦ v -∗
    lat m (l ↦ v' -∗ Φ v) -∗
    WP Xchg (Val $ LitV (LitLoc l)) (Val v') @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /store_or_ub/store'_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_store with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=. iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_CmpXchg_fail m M l dq v' v1 v2 Φ :
    ↑heapH_inv_name ⊆ M →
    v' ≠ v1 →
    vals_compare_safe v' v1 →
    l ↦{dq} v' -∗
    lat m (l ↦{dq} v' -∗ Φ (PairV v' (LitV $ LitBool false))) -∗
    WP CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask Hneq Hcmp) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold  /compile_expr. wpi_norm/=.
    rewrite /load_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_load with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=.
    rewrite /assert /= decide_True // decide_False //. wpi_norm/=.
    iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_CmpXchg_suc m M l v' v1 v2 Φ :
    ↑heapH_inv_name ⊆ M →
    v' = v1 →
    vals_compare_safe v' v1 →
    l ↦ v' -∗
    lat m (l ↦ v2 -∗ Φ (PairV v' (LitV $ LitBool true))) -∗
    WP CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask Hneq Hcmp) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /load_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_load with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=.
    rewrite /assert /= decide_True // decide_True //. wpi_norm.
    rewrite /store_or_ub/store'_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_store with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=. iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_FAA m M l i1 i2 Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦ LitV (LitInt i1) -∗
    lat m (l ↦ LitV (LitInt (i1 + i2)) -∗ Φ (LitV (LitInt i1))) -∗
    WP FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /load_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_load with "Hpointsto"); first done.
    iIntros "Hpointsto".
    rewrite /store_or_ub/store'_or_ub. wpi_norm/=.
    wpi_norm/=. iApply wpi_bind. iApply (@wpi_store with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=. iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.
End wp.
