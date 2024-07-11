From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree.threadpool Require Import handler.
From iris.prelude Require Import prelude.
From iris.base_logic Require Import ghost_map invariants.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From elpi.apps Require Import locker.

From iris.itree Require Import wpi choice ub heap handler itree step.
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
    threadpoolH ⊕ ubH ⊕ heapH val ⊕ demonicH ⊕ stepH m.

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

  Lemma wpi_step_ret m E r Φ :
    lat m (Φ r) -∗
    WPi step_ret r @ heaplangH m; E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wpi_bind. iApply @wpi_step. iApply lat_mono; last done.
    iIntros "HΦ". by iApply wpi_ret.
  Qed.
End handler.

(** Weakest precondition abstraction for heaplang expressions. *)
lock Definition wp_heaplang `{!invGS_gen hlc Σ} `{!heaplangHGS Σ} :
  Wp (iProp Σ) expr val later_modality := λ m E e Φ,
    (WPi compile_expr e @ heaplangH m; E {{ Φ }})%I.
Global Existing Instance wp_heaplang.

Section wp.
  Context `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  Lemma wp_heaplang_unfold e m E Φ :
    WP e @ m; E {{ Φ }} ⊣⊢
    WPi compile_expr e @ heaplangH m; E {{ Φ }}.
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

  (** Wand rule for [WP]. *)
  Lemma wp_wand m E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) -∗
    WP e @ m; E {{ Φ }} -∗ WP e @ m; E {{ Ψ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold.
    by iApply wpi_wand.
  Qed.

  (** Proof rules for pure operations: *)

  Lemma wp_UnOp m E op v v' Φ :
    un_op_eval op v = Some v' →
    lat m (Φ v') -∗
    WP (UnOp op (Val v)) @ m; E {{ Φ }}.
  Proof.
    iIntros (Heq) "HΦ". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=. rewrite Heq. wpi_norm/=.
    by iApply wpi_step_ret.
  Qed.

  Lemma wp_BinOp m E op v1 v2 v' Φ :
    bin_op_eval op v1 v2 = Some v' →
    lat m (Φ v') -∗
    WP (BinOp op (Val v1) (Val v2)) @ m; E {{ Φ }}.
  Proof.
    iIntros (Heq) "HΦ". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=. rewrite Heq. wpi_norm/=.
    by iApply wpi_step_ret.
  Qed.

  Lemma wp_IfTrue m e1 e2 Φ :
    lat m (WP e1 @ m; ⊤ {{ Φ }}) -∗
    WP If (Val (LitV (LitBool true))) e1 e2 @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=. iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done.
    iIntros "Hwp". iApply wpi_bind. iApply wpi_yield_if_not_val.
    iModIntro. rewrite rec_as_interp //.
  Qed.

  Lemma wp_IfFalse m e1 e2 Φ :
    lat m (WP e2 @ m; ⊤ {{ Φ }}) -∗
    WP If (Val (LitV (LitBool false))) e1 e2 @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=. iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done.
    iIntros "Hwp". iApply wpi_bind. iApply wpi_yield_if_not_val.
    iModIntro. rewrite rec_as_interp //.
  Qed.

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

  Lemma wp_App_const m E f_ x_ v w Φ :
    lat m (Φ w) -∗
    WP (App (Val (RecV f_ x_ (Val w))) (Val v)) @ m; E {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold.
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "Hwp".
    iModIntro. iApply wpi_bind. rewrite !subst'_val. iApply wpi_ret.
    rewrite interp_recursive_call rec_as_interp /= interp_ret. by iApply wpi_ret.
  Qed.

  Lemma wp_Rec m E f x erec Φ :
    lat m $ Φ (RecV f x erec) -∗
    WP Rec f x erec @ m; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He".
    iApply wpi_ret. done.
  Qed.

  Lemma wp_Pair m E v1 v2 Φ :
    lat m $ Φ (PairV v1 v2) -∗
    WP Pair (Val v1) (Val v2) @ m; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He".
    iApply wpi_ret. done.
  Qed.

  Lemma wp_Fst m E v1 v2 Φ :
    lat m $ Φ v1 -∗
    WP Fst (Val $ PairV v1 v2) @ m; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He".
    iApply wpi_ret. done.
  Qed.

  Lemma wp_Snd m E v1 v2 Φ :
    lat m $ Φ v2 -∗
    WP Snd (Val $ PairV v1 v2) @ m; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He".
    iApply wpi_ret. done.
  Qed.

  Lemma wp_InjL m E v Φ :
    lat m $ Φ (InjLV v) -∗
    WP InjL $ Val v @ m; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He".
    iApply wpi_ret. done.
  Qed.

  Lemma wp_InjR m E v Φ :
    lat m $ Φ (InjRV v) -∗
    WP InjR $ Val v @ m; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He".
    iApply wpi_ret. done.
  Qed.

  Lemma wp_CaseL m v e1 e2 Φ :
    lat m $ WP App e1 (Val v) @ m; ⊤ {{ Φ }} -∗
    WP Case (Val $ InjLV v) e1 e2 @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite !wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He". iModIntro.
    iApply wpi_bind. iApply @wpi_yield.
    rewrite interp_recursive_call. done.
  Qed.

  Lemma wp_CaseR m v e1 e2 Φ :
    lat m $ WP App e2 (Val v) @ m; ⊤ {{ Φ }} -∗
    WP Case (Val $ InjRV v) e1 e2 @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite !wp_heaplang_unfold /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "He". iModIntro.
    iApply wpi_bind. iApply @wpi_yield.
    rewrite interp_recursive_call. done.
  Qed.

  (** Proof rule for Fork *)

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

  (** Proof rule for heap operations *)

  (* TODO: adapt the following lemmas to use WP instead of WPi *)
  Lemma wp_AllocN m E v n Φ :
    (0 < n)%Z →
    ↑heapH_inv_name ⊆ E →
    lat m (∀ l,
       ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v) -∗
       Φ (LitV (LitLoc l))
    ) -∗
    WP AllocN (Val (LitV (LitInt n))) (Val v) @ m; E {{ Φ }}.
  Proof.
    iIntros (Hpos Hmask) "Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite assert_True //. wpi_norm.
    iApply wpi_bind. iApply @wpi_allocN_nondet; first done.
    iIntros (l) "Hpointsto". iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done.
    iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Load m E l v dq Φ :
    ↑heapH_inv_name ⊆ E →
    l ↦{dq} v -∗
    lat m (l ↦{dq} v -∗ Φ v) -∗
    WP Load (Val $ LitV $ LitLoc l) @ m; E {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /load_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_load with "Hpointsto"); first done. iIntros "Hpointsto".
    wpi_norm/=. iApply wpi_step_ret. iApply (lat_mono with "[Hpointsto]"); last done.
    iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Store m E l v v' Φ :
    ↑heapH_inv_name ⊆ E →
    l ↦ v -∗
    lat m (∀ r, ⌜r = LitV (LitUnit)⌝ -∗ l ↦ v' -∗ Φ r) -∗
    WP Store (Val $ LitV $ LitLoc l) (Val v') @ m; E {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite !wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /store_or_ub/store'_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_store with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=. iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Free m E l v Φ :
    ↑heapH_inv_name ⊆ E →
    l ↦ v -∗
    lat m (Φ (LitV LitUnit)) -∗
    WP Free (Val $ LitV $ LitLoc l) @ m; E {{ Φ }}.
  (* Very slight variant of the proof of [wpi_Store]: *)
  Proof.
    iIntros (Hmask) "Hpointsto HΦ".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /store'_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_store' with "Hpointsto"); first done.
    iIntros "_". wpi_norm/=. by iApply wpi_step_ret.
  Qed.

  Lemma wp_Xchg m E l v v' Φ :
    ↑heapH_inv_name ⊆ E →
    l ↦ v -∗
    lat m (l ↦ v' -∗ Φ v) -∗
    WP Xchg (Val $ LitV (LitLoc l)) (Val v') @ m; E {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. wpi_norm/=.
    rewrite /store_or_ub/store'_or_ub. wpi_norm/=.
    iApply wpi_bind. iApply (@wpi_store with "Hpointsto"); first done.
    iIntros "Hpointsto". wpi_norm/=. iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_CmpXchg_fail m E l dq v' v1 v2 Φ :
    ↑heapH_inv_name ⊆ E →
    v' ≠ v1 →
    vals_compare_safe v' v1 →
    l ↦{dq} v' -∗
    lat m (l ↦{dq} v' -∗ Φ (PairV v' (LitV $ LitBool false))) -∗
    WP CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ m; E {{ Φ }}.
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

  Lemma wp_CmpXchg_suc m E l v' v1 v2 Φ :
    ↑heapH_inv_name ⊆ E →
    v' = v1 →
    vals_compare_safe v' v1 →
    l ↦ v' -∗
    lat m (l ↦ v2 -∗ Φ (PairV v' (LitV $ LitBool true))) -∗
    WP CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ m; E {{ Φ }}.
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

  Lemma wp_FAA m E l i1 i2 Φ :
    ↑heapH_inv_name ⊆ E →
    l ↦ LitV (LitInt i1) -∗
    lat m (l ↦ LitV (LitInt (i1 + i2)) -∗ Φ (LitV (LitInt i1))) -∗
    WP FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ m; E {{ Φ }}.
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

(** Pure reductions *)

(** Mirrors Iris' [PureExec]: a witness of a head reduction from
[e1] to [e2].

TODO: It would probably be better to state this on the level
of itrees, e.g.
[φ → compile_expr e1 ≈ (step.step;; compile_expr e2)].
That would factor out a lot of common parts from the proofs below.
The issue is that this does not hold e.g. for beta reduction
due to a different number of yields on both sides. *)
Class PureExec (φ : Prop) (e1 e2 : expr) :=
  pure_exec `{!invGS_gen hlc Σ} `{!heaplangHGS Σ} m Φ :
    φ → lat m (WP e2 @ m; ⊤ {{ Φ }}) ⊢ WP e1 @ m; ⊤ {{ Φ }}.

(* Unfortunately, this lemma does not hold.
We would need the inverse of [wp_bind_K] to make it hold. *)
Lemma wp_bind_pure `{!invGS_gen hlc Σ} `{!heaplangHGS Σ} φ e1 e2 m Φ K :
  PureExec φ e1 e2 →
  φ → lat m (WP fill K e2 @ m; ⊤ {{ Φ }}) ⊢ WP fill K e1 @ m; ⊤ {{ Φ }}.
Proof.
 iIntros (Hexec Hφ).
Abort.

(** * Instances of the [PureExec] class *)
(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.


Global Instance pure_recc f x (erec : expr) :
  PureExec True (Rec f x erec) (Val $ RecV f x erec).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.
Global Instance pure_pairc (v1 v2 : val) :
  PureExec True (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.
Global Instance pure_injlc (v : val) :
  PureExec True (InjL $ Val v) (Val $ InjLV v).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.
Global Instance pure_injrc (v : val) :
  PureExec True (InjR $ Val v) (Val $ InjRV v).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.

Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof.
  unfold AsRecV in *.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  subst v1. wpi_norm/=.
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update.
  iApply lat_mono; last done. iIntros "He".
  iApply wpi_bind. iApply wpi_yield_if_not_val.
  rewrite interp_recursive_call. wpi_norm/=. done.
Qed.

Global Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') (UnOp op (Val v)) (Val v').
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. rewrite Hφ. wpi_norm/=.
  iApply wpi_ret. iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.

Global Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. rewrite Hφ. wpi_norm/=.
  iApply wpi_ret. iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.
(* Lower-cost instance for [EqOp]. *)
Global Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2)
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros ???? m Φ Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. eapply pure_binop. done. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

Global Instance pure_if_true e1 e2 :
  PureExec True (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update.
  iApply lat_mono; last done. iIntros "He".
  iApply wpi_bind. iApply wpi_yield_if_not_val. done.
Qed.
Global Instance pure_if_false e1 e2 :
  PureExec True (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update.
  iApply lat_mono; last done. iIntros "He".
  iApply wpi_bind. iApply wpi_yield_if_not_val. done.
Qed.

Global Instance pure_fst v1 v2 :
  PureExec True (Fst (Val $ PairV v1 v2)) (Val v1).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.
Global Instance pure_snd v1 v2 :
  PureExec True (Snd (Val $ PairV v1 v2)) (Val v2).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update. done.
Qed.

Global Instance pure_case_inl v e1 e2 :
  PureExec True (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update.
  iApply lat_mono; last done. iIntros "He".
  iApply wpi_bind. iApply @wpi_yield.
  rewrite interp_recursive_call. wpi_norm/=. done.
Qed.
Global Instance pure_case_inr v e1 e2 :
  PureExec True (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof.
  iIntros (???? m Φ Hφ) "He".
  rewrite !wp_heaplang_unfold.
  rewrite /compile_expr.
  wpi_norm/=. wpi_norm/= in "He".
  iApply wpi_bind. iApply @wpi_step. rewrite wpi_update.
  iApply lat_mono; last done. iIntros "He".
  iApply wpi_bind. iApply @wpi_yield.
  rewrite interp_recursive_call. wpi_norm/=. done.
Qed.
