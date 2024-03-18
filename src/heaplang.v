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
  | CmpXchg le e1 e2 =>
      v2 ← compile_expr' e2;
      v1 ← compile_expr' e1;
      l ← compile_expr' le;
      trigger EYield;;
      match l with
      | LitV (LitLoc l) =>
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (Some w) =>
              (* Asserts that equality coincides with the equality of the language. *)
              trigger (EDemonic (vals_compare_safe v1 w));;
              if decide (v1 = w) then
                trigger (ESetState (state_upd_heap <[l:=Some v2]> σ));;
                Ret w
              else Ret w
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
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp interp_ret.
    rewrite bind_ret_l interp_bind. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind interp_ret bind_ret_l interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - rewrite interp_bind rec_as_interp. f_equiv.
    intros v. rewrite rec_as_interp /=. f_equiv. rewrite !bind_ret_l //.
  - contradiction.
  - contradiction.
  - contradiction.
Qed.

Class heaplangHGS (Σ : gFunctors) := HeapLangHGS {
  heaplangH_ghost_varG :> ghost_mapG Σ loc (option val);
  heaplangH_heap_name : gname;
  heaplangH_inv_name : namespace;
}.

Definition pointsto `{!heaplangHGS Σ} (l : loc) (v : val) : iProp Σ :=
  l ↪[ heaplangH_heap_name ] (Some v).

Global Notation "l ↦ v" := (pointsto l v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section heaplangH.
  Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  Instance stateInterp_heaplang : stateInterp Σ state := λ σ,
    (ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap) ∧
    inv heaplangH_inv_name (∃ σ, ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap)))%I.

  Definition heaplangH : iHandler Σ heaplangE := threadpoolH ⊕ demonicH ⊕ stateH state ⊕ ubH.

  Lemma wpi_Fork e Φ :
    Φ (LitV LitUnit) -∗
    WPi compile_expr e @ heaplangH; ⊤ {{ v, ⌜v = LitV LitUnit⌝ }} -∗
    WPi compile_expr (Fork e) @ heaplangH; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ Hwp". rewrite /compile_expr !rec_as_interp /=.
    iApply wpi_interp_bind. iApply (wpi_yield (H := heaplangH)).
    rewrite interp_bind. setoid_rewrite interp_trigger. simpl.
    rewrite bind_trigger. iApply (wpi_fork (H := heaplangH)). iSplitL "HΦ".
    - rewrite interp_ret. by iApply wpi_ret.
    - rewrite interp_bind. iApply wpi_bind.
      iApply wpi_wand; last done. iIntros (r ->). rewrite interp_bind. iApply wpi_bind.
      setoid_rewrite interp_trigger. simpl. iApply (wpi_kill (H := heaplangH)).
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
    (0 < n)%Z → ⊢
    WPi compile_expr (AllocN (Val (LitV (LitInt n))) (Val v)) @ heaplangH; ⊤
    {{ l', ∃ l, ⌜l' = LitV (LitLoc l)⌝ ∧ [∗ list] i ∈ seq 0 (Z.to_nat n),
        (l +ₗ (i : nat)) ↦ v }}.
  Proof.
    intros Hpos. iIntros.
    rewrite /compile_expr rec_as_interp /=.
    rewrite !bind_ret_l.
    iApply wpi_interp_bind. iApply (wpi_yield (H := heaplangH)).
    iApply wpi_clear_mask.
    iApply wpi_interp_bind.
    iApply (wpi_get (H := heaplangH)).
    iApply fupd_mask_intro. { apply namespaces.coPset_empty_subseteq. } iIntros "Hfupd".
    iIntros (σ) "[Hauth #Hinv]".
    iDestruct (inv_acc_timeless ⊤ _ _ with "Hinv") as "Hσ"; first done.
    iMod "Hfupd" as "_".
    iMod "Hσ" as "[[%σ' Hauth'] Hclose]".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iFrame. iFrame "Hinv". 
    iApply wpi_ret.
    iApply fupd_mask_intro. { apply namespaces.coPset_empty_subseteq. } iIntros "Hfupd".
    iApply wpi_interp_bind. simpl. iApply (wpi_demonic (H := heaplangH)). iIntros (l).
    iApply wpi_ret. iApply wpi_interp_bind. iApply (wpi_set (H := heaplangH)).
    iIntros (σ'') "[Hauth' _]". iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_insert_big (heap_array (`l) (replicate (Z.to_nat n) v)) with "Hauth") as "Hauth".
    { apply heap_array_map_disjoint. destruct l as [l Hl]. intros i Hnz Hlt.
      rewrite replicate_length in Hlt. apply Hl; first done. lia. }
    iMod "Hauth" as "[Hauth Hfrag]".
    iDestruct "Hauth" as "[Hauth Hauth']".
    iFrame. iFrame "Hinv".
    iApply wpi_ret. rewrite interp_ret. iApply wpi_ret.
    iModIntro. iMod "Hfupd" as "_". iMod ("Hclose" with "[Hauth]").
    { by iExists (state_init_heap (`l) n v σ). }
    iModIntro. iExists (`l). iSplit; first done.
    iApply big_sep_map_list_heap_array. rewrite Loc.add_0 //.
  Qed.
End heaplangH.
