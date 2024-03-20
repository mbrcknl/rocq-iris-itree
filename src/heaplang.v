From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi threadpool choice ub state handler.
From iris.prelude Require Import prelude.
From iris Require Import ghost_map.
From iris Require Import invariants.
From iris.heap_lang Require Export lang locations.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.

Notation "m ≫= f" := (ITree.bind f m) (at level 60, right associativity) : itree_scope.
Notation "x ← y ; z" := (ITree.bind y (fun x : _ => z))
  (at level 20, y at level 100, z at level 200,
  format "x  ←  y ;  '/' z") : itree_scope.
Notation "' x ← y ; z" := (ITree.bind y (fun x_ : _ => match x_ with x => z end))
  (at level 20, x pattern, y at level 100, z at level 200,
  format "' x  ←  y ;  '/' z") : itree_scope.
Notation "x ;; z" := (ITree.bind x (fun _ => z))
  (at level 100, z at level 200, right associativity) : itree_scope.

Definition heaplangE : Type → Type := threadpoolE +' demonicE +' stateE state +' ubE.

Fixpoint compile_expr' (e : expr) : itree (callE expr val +' heaplangE) val :=
  match e with
  | Val v => Ret v
  | Rec f x e => Ret (RecV f x e)
  | App e1 e2 =>
      x ← compile_expr' e2;
      f ← compile_expr' e1;
      trigger EYield;;
      match f with
      | RecV f_ x_ e => call (subst' f_ f (subst' x_ x e))
      | _ => ub
      end
  | UnOp op e =>
      v ← compile_expr' e;
      trigger EYield;;
      match un_op_eval op v with
      | Some v => Ret v
      | None => ub
      end
  | BinOp op e1 e2 =>
      v1 ← compile_expr' e2;
      v2 ← compile_expr' e1;
      trigger EYield;;
      match bin_op_eval op v1 v2 with
      | Some v => Ret v
      | None => ub
      end
  | If e0 e1 e2 =>
      v0 ← compile_expr' e0;
      trigger EYield;;
      match v0 with
      | LitV (LitBool b) => if b then compile_expr' e1 else compile_expr' e2
      | _ => ub
      end
  | Pair e1 e2 =>
      v1 ← compile_expr' e2;
      v2 ← compile_expr' e1;
      trigger EYield;;
      Ret (PairV v1 v2)
  | Fst e =>
      v ← compile_expr' e;
      trigger EYield;;
      match v with
      | PairV x _ => Ret x
      | _ => ub
      end
  | Snd e =>
      v ← compile_expr' e;
      trigger EYield;;
      match v with
      | PairV _ y => Ret y
      | _ => ub
      end
  | InjL e =>
      v ← compile_expr' e;
      trigger EYield;;
      Ret (InjLV v)
  | InjR e =>
      v ← compile_expr' e;
      trigger EYield;;
      Ret (InjRV v)
  | Case e0 e1 e2 =>
      v0 ← compile_expr' e0;
      trigger EYield;;
      match v0 with
      | InjLV v => call (App e1 (Val v))
      | InjRV v => call (App e2 (Val v))
      | _ => ub
      end
  | Fork e =>
      trigger EYield;;
      thread ← trigger EFork;
      match thread with
      | CurrentThread => Ret (LitV LitUnit)
      | NewThread =>
          v ← compile_expr' e;
          match v with
          | LitV LitUnit =>
              x ← trigger EKillThread : itree _ Empty_set;
              match x with end
          | _ => ub
          end
      end
  | AllocN ne e =>
      v ← compile_expr' e;
      n ← compile_expr' ne;
      trigger EYield;;
      match n with
      | LitV (LitInt n) =>
          σ ← trigger EGetState;
          (* See comment about deallocated cells in [iris_heap_lang/lang.v]. *)
          (* TODO: There should be a proof obligation for this being nonempty. *)
          l ← trigger (EDemonic {l : loc | ∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ.(heap) !! (l +ₗ i) = None)});
          trigger (ESetState (state_init_heap (`l) n v σ));;
          Ret (LitV (LitLoc (`l)))
      | _ => ub
      end
  | Free e =>
      l ← compile_expr' e;
      trigger EYield;;
      match l with
      | LitV (LitLoc l) =>
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (Some _) =>
              trigger (ESetState (state_upd_heap (<[l:=None]>) σ));;
              Ret (LitV LitUnit)
          | _ => ub
          end
      | _ => ub
      end
  | Load e =>
      l ← compile_expr' e;
      trigger EYield;;
      (* TODO: Notation for partial match. *)
      match l with
      | LitV (LitLoc l) =>
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (Some v) =>
              Ret v
          | _ => ub
          end
      | _ => ub
      end
  | Store e1 e2 =>
      v ← compile_expr' e2;
      l ← compile_expr' e1;
      trigger EYield;;
      match l with
      | LitV (LitLoc l) =>
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (Some w) =>
              trigger (ESetState (state_upd_heap <[l:=Some v]> σ));;
              Ret (LitV LitUnit)
          | _ => ub
          end
      | _ => ub
      end
  | Xchg e1 e2 =>
      v ← compile_expr' e2;
      l ← compile_expr' e1;
      trigger EYield;;
      match l with
      | LitV (LitLoc l) =>
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (Some w) =>
              trigger (ESetState (state_upd_heap <[l:=Some v]> σ));;
              Ret w
          | _ => ub
          end
      | _ => ub
      end
  | CmpXchg e1 e2 e3 =>
      v2 ← compile_expr' e3;
      v1 ← compile_expr' e2;
      l ← compile_expr' e1;
      trigger EYield;;
      match l with
      | LitV (LitLoc l) =>
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (Some w) =>
              (* Asserts that equality coincides with the equality of the language. *)
              (* TODO: Define [assert] function. *)
              assert (vals_compare_safe v1 w) ;;
              if decide (v1 = w) then
                trigger (ESetState (state_upd_heap <[l:=Some v2]> σ));;
                Ret (PairV w (LitV (LitBool true)))
              else Ret (PairV w (LitV (LitBool false)))
          | _ => ub
          end
      | _ => ub
      end
  | FAA e1 e2 =>
      v ← compile_expr' e2;
      l ← compile_expr' e1;
      trigger EYield;;
      match (v, l) with
      | (LitV (LitInt v), LitV (LitLoc l)) =>
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (Some (LitV (LitInt n))) =>
              trigger (ESetState (state_upd_heap <[l:=Some (LitV (LitInt (n + v)))]> σ));;
              Ret (LitV (LitInt n))
          | _ => ub
          end
      | _ => ub
      end
  | _ => ub
  end%itree.

Definition compile_expr : expr → itree heaplangE val := rec compile_expr'.

Definition supported_subset_ectx (Ki : ectx_item) : Prop :=
  match Ki with
  | ResolveLCtx _ _ _ => False
  | ResolveMCtx _ _ => False
  | ResolveRCtx _ _ => False
  | _ => True
  end.

Lemma compile_expr_bind (Ki : ectx_item) (e : expr) :
  supported_subset_ectx Ki →
  compile_expr (fill_item Ki e) ≈
  v ← compile_expr e ; compile_expr (fill_item Ki (Val v)).
Proof.
  intros Hsubset. destruct Ki; simpl; rewrite /compile_expr rec_as_interp /=.
  all:solve
    [ rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp; f_equiv;
      intros v; rewrite rec_as_interp /=; f_equiv; rewrite !bind_ret_l //
    | rewrite interp_bind rec_as_interp; f_equiv;
      intros v; rewrite rec_as_interp /=; f_equiv; rewrite !bind_ret_l //
    | rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp interp_ret;
      rewrite bind_ret_l interp_bind; f_equiv;
      intros v; rewrite rec_as_interp /=; f_equiv; rewrite !bind_ret_l //
    | contradiction
    ].
Qed.

Class heaplangHGS (Σ : gFunctors) := HeapLangHGS {
  heaplangH_ghost_varG :> ghost_mapG Σ loc (option val);
  heaplangH_heap_name : gname;
  heaplangH_inv_name : namespace;
}.

Definition pointsto `{!heaplangHGS Σ} (l : loc) (v : val) (dq : dfrac) : iProp Σ :=
  l ↪[ heaplangH_heap_name ]{dq} (Some v).

Global Notation "l ↦ v" := (pointsto l v (DfracOwn 1))
  (at level 20, format "l  ↦  v") : bi_scope.
Global Notation "l ↦{ dq } v" := (pointsto l v dq)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.

Section heaplangH.
  Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  Instance stateInterp_heaplang : stateInterp Σ state := λ σ,
    ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap).

  Definition heaplangH : iHandler Σ heaplangE := threadpoolH ⊕ demonicH ⊕ stateH state ⊕ ubH.

  Definition heap_inv : iProp Σ :=
    inv heaplangH_inv_name (∃ σ, ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap)).

  (*
  (* TODO: Create abstraction for WPi for heaplang. This should handle the invariant. *)

  Definition wp_heaplang (e : expr) (M : coPset) (Φ : val → iProp Σ) : iProp Σ :=
    heap_inv -∗
    WPi compile_expr e @ heaplangH; M {{ Φ }}.

  From iris.bi Require Import weakestpre.
  Global Instance wp_heaplang_wp `{!invGS_gen hlc Σ} :
    Wp (iProp Σ) expr val () := λ _ M e Φ, wp_heaplang e M Φ.
 *)

  Lemma wpi_Fork e Φ :
    Φ (LitV LitUnit) -∗
    WPi compile_expr e @ heaplangH; ⊤ {{ v, ⌜v = LitV LitUnit⌝ }} -∗
    WPi compile_expr (Fork e) @ heaplangH; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ Hwp". rewrite /compile_expr !rec_as_interp /=.
    iApply wpi_interp_bind. iApply @wpi_yield.
    rewrite interp_bind. setoid_rewrite interp_trigger. simpl.
    rewrite bind_trigger. iApply @wpi_fork. iSplitL "HΦ".
    - rewrite interp_ret. by iApply wpi_ret.
    - rewrite interp_bind. iApply wpi_bind.
      iApply wpi_wand; last done. iIntros (r ->). rewrite interp_bind. iApply wpi_bind.
      setoid_rewrite interp_trigger. simpl. iApply @wpi_kill. done.
  Qed.

  Lemma big_sep_map_list_heap_array l n m v :
    ([∗ map] k↦v0 ∈ heap_array (l +ₗ Z.of_nat m) (replicate n v), k ↪[heaplangH_heap_name] v0) -∗
    [∗ list] i ∈ seq m n, (l +ₗ Z.of_nat i) ↦ v.
  Proof.
    iIntros "Hsep".
    iInduction n as [|n'] "IH" forall (m).
    - done.
    - simpl. 
      iDestruct (big_sepM_union with "Hsep") as "[Hfirst Hsep]".
      { symmetry. apply heap_array_map_disjoint. intros i Hnz Hlt. rewrite lookup_singleton_None.
        rewrite Loc.eq_spec. simpl. lia. }
      rewrite big_sepM_singleton. iFrame.
      iApply "IH".
      replace (l +ₗ S m) with (l +ₗ m +ₗ 1); last first. { rewrite Loc.add_assoc. f_equiv. lia. }
      done.
  Qed.

  Lemma wpi_AllocN v n :
    (0 < n)%Z →
    heap_inv -∗
    WPi compile_expr (AllocN (Val (LitV (LitInt n))) (Val v)) @ heaplangH; ⊤
      {{ l', ∃ l, ⌜l' = LitV (LitLoc l)⌝ ∧ [∗ list] i ∈ seq 0 (Z.to_nat n),
          (l +ₗ (i : nat)) ↦ v }}.
  Proof.
    intros Hpos. iIntros "#Hinv".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iApply wpi_interp_bind. simpl. iApply @wpi_demonic. iIntros (l). iApply wpi_ret.
    iApply wpi_interp_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_insert_big (heap_array (`l) (replicate (Z.to_nat n) v)) with "Hauth") as "Hauth".
    { apply heap_array_map_disjoint. destruct l as [l Hl]. intros i Hnz Hlt.
      rewrite replicate_length in Hlt. apply Hl; first done. lia. }
    iMod "Hauth" as "[Hauth Hfrag]". iDestruct "Hauth" as "[Hauth Hauth']". iFrame.
    iApply wpi_ret. rewrite interp_ret. iApply wpi_ret.
    iModIntro. iSplitL "Hauth". { by iExists (state_init_heap (`l) n v σ). }
    iExists (`l). iSplit; first done. iApply big_sep_map_list_heap_array. rewrite Loc.add_0 //.
  Qed.

  Lemma wpi_Load l v dq :
    l ↦{dq} v -∗
    WPi compile_expr (Load (Val $ LitV $ LitLoc l)) @ heaplangH; ⊤
      {{ v', ⌜v' = v⌝ ∧ l ↦{dq} v }}.
  Proof.
    iIntros "Hpointsto".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (s) "Hauth".
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %Hlu.
    iFrame. iApply wpi_ret. rewrite Hlu. rewrite interp_ret. iApply wpi_ret. eauto.
  Qed.

  Lemma wpi_Store l v v' :
    heap_inv -∗
    l ↦ v -∗
    WPi compile_expr (Store (Val $ LitV $ LitLoc l) (Val v')) @ heaplangH; ⊤
      {{ r, ⌜r = LitV (LitUnit)⌝ ∧ l ↦ v' }}.
  Proof.
    iIntros "#Hinv Hpointsto".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    iApply wpi_interp_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some v') with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. rewrite interp_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some v']>) σ). }
    eauto.
  Qed.

  Lemma wpi_Free l v :
    heap_inv -∗
    l ↦ v -∗
    WPi compile_expr (Free (Val $ LitV $ LitLoc l)) @ heaplangH; ⊤
      {{ r, ⌜r = LitV (LitUnit)⌝ }}.
  (* Very slight variant of the proof of [wpi_Store]: *)
  Proof.
    iIntros "#Hinv Hpointsto".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    iApply wpi_interp_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update None with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. rewrite interp_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=None]>) σ). }
    eauto.
  Qed.

  Lemma wp_Xchg l v v' :
    heap_inv -∗
    l ↦ v -∗
    WPi compile_expr (Xchg (Val $ LitV (LitLoc l)) (Val v')) @ heaplangH; ⊤
      {{ r, ⌜r = v⌝ ∧ l ↦ v' }}.
  Proof.
    iIntros "#Hinv Hpointsto".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    iApply wpi_interp_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some v') with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. rewrite interp_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some v']>) σ). }
    eauto.
  Qed.

  Lemma wpi_CmpXchg_fail l dq v' v1 v2 :
    v' ≠ v1 →
    vals_compare_safe v' v1 →
    heap_inv -∗
    l ↦{dq} v' -∗
    WPi compile_expr (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) @ heaplangH; ⊤
      {{ r, ⌜r = PairV v' (LitV $ LitBool false)⌝ ∧ l ↦{dq} v' }}.
  Proof.
    iIntros (Hneq Hcmp) "#Hinv Hpointsto".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    rewrite interp_bind /assert. rewrite decide_True // decide_False //.
    rewrite interp_ret bind_ret_l interp_ret. iApply wpi_ret.
    iSplitL "Hauth"; first eauto.
    eauto.
  Qed.

  Lemma wpi_CmpXchg_suc l v' v1 v2 :
    v' = v1 →
    vals_compare_safe v' v1 →
    heap_inv -∗
    l ↦ v' -∗
    WPi compile_expr (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) @ heaplangH; ⊤
      {{ r, ⌜r = PairV v' (LitV $ LitBool true)⌝ ∧ l ↦ v2 }}.
  Proof.
    iIntros (Heq Hcmp) "#Hinv Hpointsto".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    rewrite interp_bind /assert. rewrite decide_True // decide_True //.
    rewrite interp_ret bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some v2) with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. rewrite interp_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some v2]>) σ). }
    eauto.
  Qed.

  Lemma wpi_FAA l i1 i2 :
    heap_inv -∗
    l ↦ LitV (LitInt i1) -∗
    WPi compile_expr (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) @ heaplangH; ⊤
      {{ r, ⌜r = LitV (LitInt i1)⌝ ∧ l ↦ LitV (LitInt (i1 + i2)) }}.
  Proof.
    iIntros "#Hinv Hpointsto".
    rewrite /compile_expr rec_as_interp /= !bind_ret_l.
    iApply wpi_interp_bind. iApply @wpi_yield.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_interp_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    iApply wpi_interp_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some (LitV (LitInt (i1 + i2)))) with "Hauth Hpointsto")
      as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. rewrite interp_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some (LitV (LitInt (i1 + i2)))]>) σ). }
    eauto.
  Qed.
End heaplangH.
