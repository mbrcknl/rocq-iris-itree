From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi threadpool choice ub state handler.
From iris.prelude Require Import prelude.
From iris Require Import gen_heap.
From iris.heap_lang Require Export lang.
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
      match f with
      | RecV f_ x_ e => call (subst' f_ f (subst' x_ x e))
      | _ => ub
      end
  | UnOp op e =>
      v ← compile_expr' e;
      match un_op_eval op v with
      | Some v => Ret v
      | None => ub
      end
  | BinOp op e1 e2 =>
      v1 ← compile_expr' e2;
      v2 ← compile_expr' e1;
      match bin_op_eval op v1 v2 with
      | Some v => Ret v
      | None => ub
      end
  | If e0 e1 e2 =>
      v0 ← compile_expr' e0;
      match v0 with
      | LitV (LitBool b) => if b then compile_expr' e1 else compile_expr' e2
      | _ => ub
      end
  | Pair e1 e2 =>
      v1 ← compile_expr' e2;
      v2 ← compile_expr' e1;
      Ret (PairV v1 v2)
  | Fst e =>
      v ← compile_expr' e;
      match v with
      | PairV x _ => Ret x
      | _ => ub
      end
  | Snd e =>
      v ← compile_expr' e;
      match v with
      | PairV _ y => Ret y
      | _ => ub
      end
  | InjL e =>
      v ← compile_expr' e;
      Ret (InjLV v)
  | InjR e =>
      v ← compile_expr' e;
      Ret (InjRV v)
  | Case e0 e1 e2 =>
      v0 ← compile_expr' e0;
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
      match n with
      | LitV (LitInt n) =>
          trigger EYield;;
          σ ← trigger EGetState;
          (* See comment about deallocated cells in [iris_heap_lang/lang.v]. *)
          l ← trigger (EDemonic {l : loc | ∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ.(heap) !! (l +ₗ i) = None)});
          trigger (ESetState (state_init_heap (proj1_sig l) n v σ));;
          Ret (LitV LitUnit)
      | _ => ub
      end
  | Free e =>
      l ← compile_expr' e;
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
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
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
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
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
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
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
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
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
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
      match (v, l) with
      | (LitV (LitInt v), LitV (LitLoc l)) =>
          trigger EYield;;
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

Class heaplangHPreG (Σ : gFunctors) := HeapLangHPreG {
  heaplangH_pre_ghost_varG :> gen_heapGpreS loc (option val) Σ;
}.
Class heaplangHGS (Σ : gFunctors) := HeapLangHGS {
  heaplangH_ghost_varGS :> gen_heapGS loc (option val) Σ;
}.
Definition heaplangHΣ : gFunctors :=
  gen_heapΣ loc (option val).
Global Instance subG_heaplangHΣ Σ :
  subG heaplangHΣ Σ → heaplangHPreG Σ.
Proof. solve_inG. Qed.

Global Notation "l ↦ v" := (pointsto l (DfracOwn 1) (Some v))
  (at level 20, format "l  ↦  v") : bi_scope.

Section gen_heap.
  Context `{Countable L, hG : !gen_heapGS L V Σ}.

  From stdpp Require Export namespaces.
  From iris.algebra Require Import reservation_map agree frac.
  From iris.algebra Require Export dfrac.
  From iris.bi.lib Require Import fractional.
  From iris.proofmode Require Import proofmode.
  From iris.base_logic.lib Require Export own.
  From iris.base_logic.lib Require Import ghost_map.
  From iris.prelude Require Import options.

  Definition gen_heap_interp_half (σ : gmap L V) : iProp Σ := ∃ m : gmap L gname,
    (* The [⊆] is used to avoid assigning ghost information to the locations in
    the initial heap (see [gen_heap_init]). *)
    ⌜ dom m ⊆ dom σ ⌝ ∗
    ghost_map_auth (gen_heap_name hG) (1/2) σ ∗
    ghost_map_auth (gen_meta_name hG) (1/2) m.
End gen_heap.

Section heaplangH.
  Context {Σ} `{!stateHGS Σ state} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  Instance stateInterp_heaplang : stateInterp Σ state := λ σ,
    gen_heap_interp σ.(heap).

  Definition heaplangH : iHandler Σ heaplangE := threadpoolH ⊕ demonicH ⊕ stateH state ⊕ ubH.

  Lemma wpi_Fork e Φ :
    Φ (LitV LitUnit) -∗
    WPi compile_expr e @ heaplangH; ⊤ {{ v, ⌜v = LitV LitUnit⌝ }} -∗
    WPi compile_expr (Fork e) @ heaplangH; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ Hwp". iEval (rewrite /compile_expr rec_as_interp /=).
    iApply wpi_interp_bind. iApply (wpi_yield (H := heaplangH)).
    rewrite interp_bind. setoid_rewrite interp_trigger. simpl.
    rewrite bind_trigger. iApply (wpi_fork (H := heaplangH)). iSplitL "HΦ".
    - rewrite interp_ret. by iApply wpi_ret.
    - iApply wpi_interp_bind.
      iApply wpi_wand; last done. iIntros (r ->). rewrite interp_bind. iApply wpi_bind.
      setoid_rewrite interp_trigger. simpl. iApply (wpi_kill (H := heaplangH)).
  Qed.

  Lemma wpi_AllocN ev v en n :
    (0 < n)%Z →
    WPi compile_expr en @ heaplangH; ⊤ {{ n', ⌜n' = LitV (LitInt n)⌝ }} -∗
    WPi compile_expr ev @ heaplangH; ⊤ {{ v', ⌜v' = v⌝ }} -∗
    WPi compile_expr (AllocN en ev) @ heaplangH; ⊤
    {{ l', ∃ l, ⌜l' = LitV (LitLoc l)⌝ ∧ [∗ list] i ∈ seq 0 (Z.to_nat n),
        (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}.
  Proof.
    iIntros (Hpos) "Hn Hv".
    iEval (rewrite /compile_expr rec_as_interp).
    iApply wpi_interp_bind. iApply (wpi_wand with "[Hn] Hv"). iIntros (r ->).
    iApply wpi_interp_bind. iApply (wpi_wand with "[] Hn"). iIntros (r ->).
    iApply wpi_interp_bind. iApply (wpi_yield (H := heaplangH)).
    iApply wpi_interp_bind. iApply (wpi_get (H := heaplangH)). iIntros (s) "$ !>". iApply wpi_ret.
    iApply wpi_interp_bind. iApply (wpi_demonic (H := heaplangH)). iIntros (l). iApply wpi_ret.
    iApply wpi_interp_bind. iApply (wpi_set (H := heaplangH)). iIntros (s') "Hstate".
  Abort.
End heaplangH.
