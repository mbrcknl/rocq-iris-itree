From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi choice ub state handler itree.
From iris.itree.threadpool Require Import handler.
From iris.prelude Require Import prelude.
From iris Require Import ghost_map.
From iris Require Import invariants.
From iris.heap_lang Require Export lang locations.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.

Notation "m ≫= f" := (ITree.bind f m) (at level 60, right associativity) : itree_scope.
Notation "x ← y ; z" := (ITree.bind y (fun x : _ => z)%itree)
  (at level 20, y at level 100, z at level 200,
  format "x  ←  y ;  '/' z") : itree_scope.
Notation "' x ← y ; z" := (ITree.bind y (fun x_ : _ => match x_ with x => z end)%itree)
  (at level 20, x pattern, y at level 100, z at level 200,
  format "' x  ←  y ;  '/' z") : itree_scope.
Notation "x ;; z" := (ITree.bind x (fun _ => z)%itree)
  (at level 100, z at level 200, right associativity) : itree_scope.

Definition heaplangE : Type → Type := threadpoolE +' demonicE +' stateE state +' ubE.

Definition yield_if_not_val (e : expr) {E} `{threadpoolE -< E} : itree E () :=
  match to_val e with
  | Some _ => Ret ()
  | None => trigger EYield
  end.
Arguments yield_if_not_val !_ / _.

Definition some_or_ub {E R} `{!ubE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => ub end)%itree.
Notation "x ?" := (some_or_ub x) (at level 10, format "x ?") : itree_scope.
Definition some_some_or_ub {E R} `{!ubE -< E} (o : option (option R)) : itree E R :=
  (match o with | Some (Some x) => Ret x | _ => ub end)%itree.
Notation "x ??" := (some_some_or_ub x) (at level 10, format "x ??") : itree_scope.

Definition val_to_RecV (v : val) : option (binder * binder * expr) :=
  match v with
  | RecV f_ x_ e => Some (f_, x_, e)
  | _ => None
  end.
Definition val_to_int (v : val) : option Z :=
  match v with
  | LitV (LitInt n) => Some n
  | _ => None
  end.
Definition val_to_loc (v : val) : option loc :=
  match v with
  | LitV (LitLoc l) => Some l
  | _ => None
  end.
Definition val_to_pair (v : val) : option (val * val) :=
  match v with
  | PairV v1 v2 => Some (v1, v2)
  | _ => None
  end.
Definition val_to_bool (v : val) : option bool :=
  match v with
  | LitV (LitBool b) => Some b
  | _ => None
  end.
Definition val_to_sum (v : val) : option (val + val) :=
  match v with
  | InjLV v => Some (inl v)
  | InjRV v => Some (inr v)
  | _ => None
  end.

Lemma Decision_range' P n :
  (∀ i, Decision (P i)) →
  Decision (∀ i, (0 ≤ i)%Z → (i < Z.of_nat n)%Z → P i).
Proof.
  intros HPdec.
  induction n.
  - left. intros i Hlower Hupper. lia.
  - destruct (decide (P n)) as [Heq|Hneq].
    * destruct (decide (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → P i)) as [HP|HP].
      + left. intros i Hlower Hupper.
        destruct (decide (i = n)) as [->|Hi]; first done.
        apply HP; lia.
      + right. intros HP'.
        apply HP. intros i Hlower Hupper.
        destruct (decide (i = n)) as [->|Hi]; first done.
        apply HP'; lia.
    * right. intros HP. apply Hneq. apply HP; lia.
Qed.
Lemma Decision_range P n :
  (∀ i, Decision (P i)) →
  Decision (∀ i, (0 ≤ i)%Z → (i < n)%Z → P i).
Proof.
  intros HP.
  destruct (decide (n < 0)%Z) as [Hleq|Hleq].
  * left. intros i Hlower Hupper. lia.
  * replace n with (Z.of_nat (Z.to_nat n)); first by apply Decision_range'.
    lia.
Qed.
Instance free_locations_dec n l σ :
  Decision (∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ.(heap) !! (l +ₗ i) = None)).
Proof. apply Decision_range. apply _. Qed.
Definition free_locations n σ : Set :=
  {l : loc | bool_decide (∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ.(heap) !! (l +ₗ i) = None))}.
Instance free_locations_Inhabited n σ :
  Inhabited (free_locations n σ).
Proof.
  constructor. apply exist with (x := Loc.fresh (dom σ.(heap))).
  apply bool_decide_pack.
  intros i Hlower Hupper.
  apply not_elem_of_dom. by apply Loc.fresh_fresh.
Qed.
Instance free_locations_EqDecision n σ :
  EqDecision (free_locations n σ).
Proof.
  intros l1 l2.
  destruct (decide (`l1 = `l2)) as [Heq|Hneq].
  - apply dsig_eq in Heq. by left.
  - right. intros Heq. apply Hneq. by apply dsig_eq.
Qed.

Fixpoint compile_expr' (e : expr) : itree (callE expr val +' heaplangE) val :=
  let compile_expr_yield e := (v ← compile_expr' e ; yield_if_not_val e ;; Ret v)%itree in
  match e with
  | Val v => Ret v
  | Rec f x e => Ret (RecV f x e)
  | App e1 e2 =>
      x ← compile_expr_yield e2;
      f ← compile_expr_yield e1;
      '(f_, x_, e) ← (val_to_RecV f)?;
      let body := subst' x_ x  (subst' f_ f e) in
      yield_if_not_val body;;
      call body
  | UnOp op e =>
      v ← compile_expr_yield e;
      (un_op_eval op v)?
  | BinOp op e1 e2 =>
      v2 ← compile_expr_yield e2;
      v1 ← compile_expr_yield e1;
      (bin_op_eval op v1 v2)?
  | If e0 e1 e2 =>
      v0 ← compile_expr_yield e0;
      b ← (val_to_bool v0)?;
      if b then
        (* if true then e1 else e2 ~> e1 (must yield here!) ~> ... *)
        yield_if_not_val e1;;
        compile_expr' e1
      else
        yield_if_not_val e2;;
        compile_expr' e2
  | Pair e1 e2 =>
      v1 ← compile_expr_yield e2;
      v2 ← compile_expr_yield e1;
      Ret (PairV v1 v2)
  | Fst e =>
      v ← compile_expr_yield e;
      '(x, _) ← (val_to_pair v)?;
      Ret x
  | Snd e =>
      v ← compile_expr_yield e;
      '(_, y) ← (val_to_pair v)?;
      Ret y
  | InjL e =>
      v ← compile_expr_yield e;
      Ret (InjLV v)
  | InjR e =>
      v ← compile_expr_yield e;
      Ret (InjRV v)
  | Case e0 e1 e2 =>
      v0' ← compile_expr_yield e0;
      v0 ← (val_to_sum v0')?;
      match v0 with
      | inl v =>
          trigger EYield;;
          call (App e1 (Val v))
      | inr v =>
          trigger EYield;;
          call (App e2 (Val v))
      end
  | Fork e =>
      thread ← trigger EFork;
      match thread with
      | CurrentThread => Ret (LitV LitUnit)
      | NewThread =>
          v ← compile_expr_yield e;
          kill_thread
      end
  | AllocN ne e =>
      v ← compile_expr_yield e;
      n' ← compile_expr_yield ne;
      n ← (val_to_int n')?;
      assert (0 < n)%Z;;
      σ ← trigger EGetState;
      (* See comment about deallocated cells in [iris_heap_lang/lang.v]. *)
      (* TODO: There should be a proof obligation for this being nonempty. *)
      l ← trigger (EDemonic (free_locations n σ));
      trigger (ESetState (state_init_heap (`l) n v σ));;
      Ret (LitV (LitLoc (`l)))
  | Free e =>
      l' ← compile_expr_yield e;
      l ← (val_to_loc l')?;
      σ ← trigger EGetState;
      (σ.(heap) !! l)??;;
      trigger (ESetState (state_upd_heap (<[l:=None]>) σ));;
      Ret (LitV LitUnit)
  | Load e =>
      l' ← compile_expr_yield e;
      l ← (val_to_loc l')?;
      σ ← trigger EGetState;
      (σ.(heap) !! l)??
  | Store e1 e2 =>
      v ← compile_expr_yield e2;
      l' ← compile_expr_yield e1;
      l ← (val_to_loc l')?;
      σ ← trigger EGetState;
      w ← (σ.(heap) !! l)??;
      trigger (ESetState (state_upd_heap <[l:=Some v]> σ));;
      Ret (LitV LitUnit)
  | Xchg e1 e2 =>
      v ← compile_expr_yield e2;
      l' ← compile_expr_yield e1;
      l ← (val_to_loc l')?;
      σ ← trigger EGetState;
      w ← (σ.(heap) !! l)??;
      trigger (ESetState (state_upd_heap <[l:=Some v]> σ));;
      Ret w
  | CmpXchg e1 e2 e3 =>
      v2 ← compile_expr_yield e3;
      v1 ← compile_expr_yield e2;
      l' ← compile_expr_yield e1;
      l ← (val_to_loc l')?;
      σ ← trigger EGetState;
      w ← (σ.(heap) !! l)??;
      (* Asserts that equality coincides with the equality of the language. *)
      assert (vals_compare_safe v1 w) ;;
      if decide (v1 = w) then
        trigger (ESetState (state_upd_heap <[l:=Some v2]> σ));;
        Ret (PairV w (LitV (LitBool true)))
      else Ret (PairV w (LitV (LitBool false)))
  | FAA e1 e2 =>
      v' ← compile_expr_yield e2;
      l' ← compile_expr_yield e1;
      v ← (val_to_int v')?;
      l ← (val_to_loc l')?;
      σ ← trigger EGetState;
      w ← (σ.(heap) !! l)??;
      n ← (val_to_int w)?;
      trigger (ESetState (state_upd_heap <[l:=Some (LitV (LitInt (n + v)))]> σ));;
      Ret (LitV (LitInt n))
  | _ => ub
  end%itree.

Definition compile_expr : expr → itree heaplangE val := rec compile_expr'.

Lemma compile_expr_val (v : val) :
  compile_expr (Val v) ≈ Ret v.
Proof. rewrite /compile_expr. by simpl_itree. Qed.

Definition supported_subset_ectx (Ki : ectx_item) : Prop :=
  match Ki with
  | ResolveLCtx _ _ _ => False
  | ResolveMCtx _ _ => False
  | ResolveRCtx _ _ => False
  | _ => True
  end.

Lemma interp_yield e :
  interp (recursive compile_expr') (yield_if_not_val e) ≈ yield_if_not_val e.
Proof.
  rewrite /yield_if_not_val. destruct (to_val e); by simpl_itree.
Qed.

Lemma compile_expr_bind_item (Ki : ectx_item) (e : expr) :
  supported_subset_ectx Ki →
  compile_expr (fill_item Ki e) ≈
    v ← compile_expr e;
    yield_if_not_val e;;
    compile_expr (fill_item Ki (Val v)).
Admitted. (* Admitted for performance reasons: *)
(* Proof.
  intros Hsubset. destruct Ki; simpl; rewrite /compile_expr; try contradiction;
  simpl_itree; f_equiv; intros v; f_equiv; apply interp_yield.
Qed. *)

Lemma split_last {A} (xs : list A) :
  length xs > 0 →
  ∃ x xs', xs = xs' ++ [x].
Proof.
  intros Hlen.
  induction xs as [|y ys IH]. { simpl in Hlen. lia. }
  destruct (length ys) as [|n] eqn:Hlen'.
  - apply nil_length_inv in Hlen' as ->. by exists y, [].
  - assert (S n > 0) as HS; first lia.
    destruct (IH HS) as (x&xs'&->). by exists x, (y :: xs').
Qed.

Lemma list_singleton {A} (xs : list A) :
  length xs = 1 →
  ∃ x, xs = [x].
Proof.
  intros Hlen.
  destruct xs as [|x xs']; first done.
  exists x. simpl in Hlen. injection Hlen as Hlen.
  by apply nil_length_inv in Hlen as ->.
Qed.

Lemma fill_item_not_val Ki e :
  yield_if_not_val (fill_item Ki e) ≈ (trigger EYield : itree heaplangE ()).
Proof.
  rewrite /yield_if_not_val. by destruct Ki.
Qed.
Lemma fill_not_val K e :
  length K > 0 →
  yield_if_not_val (fill K e) ≈ (trigger EYield : itree heaplangE ()).
Proof.
  intros Hlen.
  unshelve epose (split_last K _) as Hsplit; first lia. destruct Hsplit as (Ki&K'&->).
  rewrite fill_app /= fill_item_not_val //.
Qed.

Lemma compile_expr_bind_ind K e l :
  Forall supported_subset_ectx K →
  length K = l →
  l > 0 →
  compile_expr (fill K e) ≈
    v ← compile_expr e;
    yield_if_not_val e;;
    compile_expr (fill K (Val v)).
Proof.
  revert K. induction l as [|n IH]; intros K Hsubset Hlen Hne.
  { apply nil_length_inv in Hlen. lia. }
  destruct n as [|n'].
  { apply list_singleton in Hlen as [x ->]. simpl. rewrite compile_expr_bind_item //.
    by rewrite Forall_singleton in Hsubset. }
  unshelve epose (split_last K _) as Hsplit; first lia. destruct Hsplit as (Ki&K'&->).
  apply Forall_app in Hsubset as [HsubsetK' HsubsetKi].
  rewrite Forall_singleton in HsubsetKi. rewrite app_length /= in Hlen.
  rewrite fill_app /=. rewrite compile_expr_bind_item //; first rewrite IH //; try lia.
  rewrite bind_bind. f_equiv. intros v. rewrite fill_app /=.
  rewrite bind_bind. f_equiv. intros _.
  rewrite compile_expr_bind_item //. f_equiv. intros v'. rewrite !fill_not_val //.
  - replace (length K' + 1) with (S (length K')) in Hlen by lia. injection Hlen as Hlen.
    rewrite Hlen. lia.
  - replace (length K' + 1) with (S (length K')) in Hlen by lia. injection Hlen as Hlen.
    rewrite Hlen. lia.
Qed.
Lemma compile_expr_bind K e :
  Forall supported_subset_ectx K →
  length K > 0 →
  compile_expr (fill K e) ≈
    v ← compile_expr e;
    yield_if_not_val e;;
    compile_expr (fill K (Val v)).
Proof.
  intros Hsubset Hne. by apply compile_expr_bind_ind with (l := length K).
Qed.

Lemma compile_expr_bind' K e :
  Forall supported_subset_ectx K →
  compile_expr (fill K e) ≈
    v ← compile_expr e;
    if (decide (length K = 0)) then
      Ret v
    else
      yield_if_not_val e;;
      compile_expr (fill K (Val v)).
Proof.
  intros Hsubset.
  destruct (decide _) as [Heq|Hneq].
  - apply nil_length_inv in Heq as ->.
    by simpl_itree.
  - apply compile_expr_bind; first done. lia.
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

  Global Instance stateInterp_heaplang : stateInterp Σ state := λ σ,
    ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap).

  Definition heaplangH : iHandler Σ heaplangE := threadpoolH ⊕ demonicH ⊕ stateH state ⊕ ubH.

  Definition heap_inv : iProp Σ :=
    inv heaplangH_inv_name (∃ σ, ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap)).

  Lemma wpi_yield_if_not_val e Φ :
    Φ () -∗
    WPi (yield_if_not_val e) @ heaplangH; ⊤ {{ Φ }}.
  Proof.
    rewrite /yield_if_not_val. destruct (to_val e).
    * iApply wpi_ret.
    * iIntros "HΦ". by iApply @wpi_yield.
  Qed.

  (*
  (* TODO: Create abstraction for WPi for heaplang. This should handle the invariant. *)

  Definition wp_heaplang (e : expr) (M : coPset) (Φ : val → iProp Σ) : iProp Σ :=
    heap_inv -∗
    WPi compile_expr e @ heaplangH; M {{ Φ }}.

  From iris.bi Require Import weakestpre.
  Global Instance wp_heaplang_wp `{!invGS_gen hlc Σ} :
    Wp (iProp Σ) expr val () := λ _ M e Φ, wp_heaplang e M Φ.
 *)
  Lemma wpi_bind_K K e Φ :
    Forall supported_subset_ectx K →
    length K > 0 →
    WPi compile_expr e @ heaplangH; ⊤ {{ v,
      WPi compile_expr (fill K (Val v)) @ heaplangH; ⊤ {{ Φ }}
    }} -∗
    WPi compile_expr (fill K e) @ heaplangH; ⊤ {{ Φ }}.
  Proof.
    iIntros (Hs Hlen) "Hwp". rewrite compile_expr_bind //. iApply wpi_bind.
    iApply wpi_wand; last done. iIntros (r) "Hwp".
    iApply wpi_bind. rewrite /yield_if_not_val. destruct e.
    1:by iApply wpi_ret.
    all:by iApply @wpi_yield.
  Qed.

  Lemma wpi_Fork e Φ :
    Φ (LitV LitUnit) -∗
    WPi compile_expr e @ heaplangH; ⊤ {{ v, ⌜v = LitV LitUnit⌝ }} -∗
    WPi compile_expr (Fork e) @ heaplangH; ⊤ {{ Φ }}.
  Proof.
    iIntros "HΦ Hwp". rewrite /compile_expr. simpl_itree.
    rewrite bind_trigger. iApply @wpi_fork. iSplitL "HΦ".
    - simpl_itree. by iApply wpi_ret.
    - simpl_itree. iApply wpi_bind.
      iApply wpi_wand; last done. iIntros (r ->).
      rewrite /yield_if_not_val. destruct (to_val _) eqn:Hval.
      * rewrite /kill_thread. simpl_itree. rewrite bind_trigger. by iApply @wpi_kill.
      * rewrite /kill_thread. simpl_itree. iApply wpi_bind. iApply @wpi_yield.
        iApply wpi_bind. by iApply @wpi_kill.
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

  Lemma wpi_AllocN M v n :
    (0 < n)%Z →
    ↑heaplangH_inv_name ⊆ M →
    heap_inv -∗
    WPi compile_expr (AllocN (Val (LitV (LitInt n))) (Val v)) @ heaplangH; M
      {{ l', ∃ l, ⌜l' = LitV (LitLoc l)⌝ ∧ [∗ list] i ∈ seq 0 (Z.to_nat n),
          (l +ₗ (i : nat)) ↦ v }}.
  Proof.
    intros Hpos. iIntros (Hmask) "#Hinv".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    rewrite /assert /= decide_True //. simpl_itree.
    iApply wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iApply wpi_bind. simpl. iApply @wpi_demonic. iIntros (l). iApply wpi_ret.
    iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_insert_big (heap_array (`l) (replicate (Z.to_nat n) v)) with "Hauth") as "Hauth".
    { apply heap_array_map_disjoint. destruct l as [l Hl]. intros i Hnz Hlt.
      rewrite replicate_length in Hlt.
      pose (bool_decide_unpack _ Hl) as Hl'. apply Hl'; first done. lia.
    }
    iMod "Hauth" as "[Hauth Hfrag]". iDestruct "Hauth" as "[Hauth Hauth']". iFrame.
    iApply wpi_ret. iApply wpi_ret.
    iModIntro. iSplitL "Hauth". { by iExists (state_init_heap (`l) n v σ). }
    iExists (`l). iSplit; first done. iApply big_sep_map_list_heap_array. rewrite Loc.add_0 //.
  Qed.

  Lemma wpi_Load M l v dq :
    ↑heaplangH_inv_name ⊆ M →
    l ↦{dq} v -∗
    WPi compile_expr (Load (Val $ LitV $ LitLoc l)) @ heaplangH; M
      {{ v', ⌜v' = v⌝ ∧ l ↦{dq} v }}.
  Proof.
    iIntros (Hmask) "Hpointsto".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_bind. iApply @wpi_get.
    iIntros (s) "Hauth".
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %Hlu.
    iFrame. iApply wpi_ret. rewrite Hlu. simpl_itree. iApply wpi_ret. eauto.
  Qed.

  Lemma wpi_Store M l v v' :
    ↑heaplangH_inv_name ⊆ M →
    heap_inv -∗
    l ↦ v -∗
    WPi compile_expr (Store (Val $ LitV $ LitLoc l) (Val v')) @ heaplangH; M
      {{ r, ⌜r = LitV (LitUnit)⌝ ∧ l ↦ v' }}.
  Proof.
    iIntros (Hmask) "#Hinv Hpointsto".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    simpl_itree. iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some v') with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some v']>) σ). }
    eauto.
  Qed.

  Lemma wpi_Free M l v :
    ↑heaplangH_inv_name ⊆ M →
    heap_inv -∗
    l ↦ v -∗
    WPi compile_expr (Free (Val $ LitV $ LitLoc l)) @ heaplangH; M
      {{ r, ⌜r = LitV (LitUnit)⌝ }}.
  (* Very slight variant of the proof of [wpi_Store]: *)
  Proof.
    iIntros (Hmask) "#Hinv Hpointsto".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    simpl_itree. iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update None with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=None]>) σ). }
    eauto.
  Qed.

  Lemma wp_Xchg M l v v' :
    ↑heaplangH_inv_name ⊆ M →
    heap_inv -∗
    l ↦ v -∗
    WPi compile_expr (Xchg (Val $ LitV (LitLoc l)) (Val v')) @ heaplangH; M
      {{ r, ⌜r = v⌝ ∧ l ↦ v' }}.
  Proof.
    iIntros (Hmask) "#Hinv Hpointsto".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    simpl_itree. iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some v') with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some v']>) σ). }
    eauto.
  Qed.

  Lemma wpi_CmpXchg_fail M l dq v' v1 v2 :
    ↑heaplangH_inv_name ⊆ M →
    v' ≠ v1 →
    vals_compare_safe v' v1 →
    heap_inv -∗
    l ↦{dq} v' -∗
    WPi compile_expr (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) @ heaplangH; M
      {{ r, ⌜r = PairV v' (LitV $ LitBool false)⌝ ∧ l ↦{dq} v' }}.
  Proof.
    iIntros (Hmask Hneq Hcmp) "#Hinv Hpointsto".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    simpl_itree. rewrite /assert /= decide_True // decide_False //. simpl_itree.
    iApply wpi_ret. iSplitL "Hauth"; first eauto. eauto.
  Qed.

  Lemma wpi_CmpXchg_suc M l v' v1 v2 :
    ↑heaplangH_inv_name ⊆ M →
    v' = v1 →
    vals_compare_safe v' v1 →
    heap_inv -∗
    l ↦ v' -∗
    WPi compile_expr (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) @ heaplangH; M
      {{ r, ⌜r = PairV v' (LitV $ LitBool true)⌝ ∧ l ↦ v2 }}.
  Proof.
    iIntros (Hmask Heq Hcmp) "#Hinv Hpointsto".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    simpl_itree. rewrite /assert /= decide_True // decide_True //. simpl_itree.
    iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some v2) with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some v2]>) σ). }
    eauto.
  Qed.

  Lemma wpi_FAA M l i1 i2 :
    ↑heaplangH_inv_name ⊆ M →
    heap_inv -∗
    l ↦ LitV (LitInt i1) -∗
    WPi compile_expr (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) @ heaplangH; M
      {{ r, ⌜r = LitV (LitInt i1)⌝ ∧ l ↦ LitV (LitInt (i1 + i2)) }}.
  Proof.
    iIntros (Hmask) "#Hinv Hpointsto".
    rewrite /compile_expr. simpl_itree.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    simpl_itree. iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update (Some (LitV (LitInt (i1 + i2)))) with "Hauth Hpointsto")
      as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=Some (LitV (LitInt (i1 + i2)))]>) σ). }
    eauto.
  Qed.
End heaplangH.
