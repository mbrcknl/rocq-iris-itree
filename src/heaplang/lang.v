From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi choice ub state handler itree later.
From iris.itree.threadpool Require Import handler.
From iris.prelude Require Import prelude.
From iris Require Import ghost_map.
From iris Require Import invariants.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From elpi.apps Require Import locker.
From iris.heap_lang Require Export lang locations.

Definition sequential_heaplangE : Type → Type := ubE +' stateE state +' demonicE +' laterE.
(** The event type for heaplang. *)
Definition heaplangE : Type → Type := threadpoolE +' sequential_heaplangE.
Global Hint Transparent sequential_heaplangE : itree_auto.
Global Hint Transparent heaplangE : itree_auto.

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

(** [yield] precisely if an expression is not a value.

This appears many times in the below specification of the semantics of
heaplang. The reason is explained later by example. *)
Definition yield_if_not_val (e : expr) {E} `{threadpoolE -< E} `{laterE -< E} : itree E () :=
  match to_val e with
  | Some _ => Ret ()
  | None => yield
  end.
Arguments yield_if_not_val !_ / _.

Lemma fill_item_not_val Ki e :
  yield_if_not_val (fill_item Ki e) ≈ (yield : itree heaplangE ()).
Proof.
  rewrite /yield_if_not_val. by destruct Ki.
Qed.
Lemma fill_not_val K e :
  length K > 0 →
  yield_if_not_val (fill K e) ≈ (yield : itree heaplangE ()).
Proof.
  intros Hlen.
  unshelve epose (split_last K _) as Hsplit; first lia. destruct Hsplit as (Ki&K'&->).
  rewrite fill_app /= fill_item_not_val //.
Qed.

(* TODO: Remove these duplicate definitions (already in [ub.v] but without [do]) *)
Definition some_or_ub {E R} `{!ubE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => ub end)%itree.
Notation "x ?" := (do $ some_or_ub x) (at level 10, format "x ?") : itree_scope.
Definition some_some_or_ub {E R} `{!ubE -< E} (o : option (option R)) : itree E R :=
  (match o with | Some (Some x) => Ret x | _ => ub end)%itree.
Notation "x ??" := (do $ some_some_or_ub x) (at level 10, format "x ??") : itree_scope.

(** Cast a value to [RecV]. *)
Definition val_to_RecV (v : val) : option (binder * binder * expr) :=
  match v with
  | RecV f_ x_ e => Some (f_, x_, e)
  | _ => None
  end.
(** Cast a value to [LitInt]. *)
Definition val_to_int (v : val) : option Z :=
  match v with
  | LitV (LitInt n) => Some n
  | _ => None
  end.
(** Cast a value to [LitLoc]. *)
Definition val_to_loc (v : val) : option loc :=
  match v with
  | LitV (LitLoc l) => Some l
  | _ => None
  end.
(** Cast a value to [PairV]. *)
Definition val_to_pair (v : val) : option (val * val) :=
  match v with
  | PairV v1 v2 => Some (v1, v2)
  | _ => None
  end.
(** Cast a value to [LitBool]. *)
Definition val_to_bool (v : val) : option bool :=
  match v with
  | LitV (LitBool b) => Some b
  | _ => None
  end.
(** Cast a value to [InjLV]/[InjRV]. *)
Definition val_to_sum (v : val) : option (val + val) :=
  match v with
  | InjLV v => Some (inl v)
  | InjRV v => Some (inr v)
  | _ => None
  end.

Section free_locations.
  (** Version of [Decision_range] using [Z] inequalities instead of [nat]
  inequalities. *)
  Lemma Decision_range_Z P n :
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
  (** If [P i] is decidable for all [i], then whether it holds in a finite range
  is also decidable. *)
  Lemma Decision_range P n :
    (∀ i, Decision (P i)) →
    Decision (∀ i, (0 ≤ i)%Z → (i < n)%Z → P i).
  Proof.
    intros HP.
    destruct (decide (n < 0)%Z) as [Hleq|Hleq].
    * left. intros i Hlower Hupper. lia.
    * replace n with (Z.of_nat (Z.to_nat n)); first by apply Decision_range_Z.
      lia.
  Qed.

  (** Whether a range of the heap is free is decidable. *)
  Instance free_locations_dec n l σ :
    Decision (∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ.(heap) !! (l +ₗ i) = None)).
  Proof. apply Decision_range. apply _. Qed.
  (** Available locations in heap [σ] for allocating a block of [n] adjacent
  memory cells. *)
  Definition free_locations n σ : Set :=
    {l : loc | bool_decide (∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ.(heap) !! (l +ₗ i) = None))}.
  Global Hint Transparent free_locations : itree_auto.
  (** The heap always has more space. *)
  Global Instance free_locations_Inhabited n σ :
    Inhabited (free_locations n σ).
  Proof.
    constructor. apply exist with (x := Loc.fresh (dom σ.(heap))).
    apply bool_decide_pack.
    intros i Hlower Hupper.
    apply not_elem_of_dom. by apply Loc.fresh_fresh.
  Defined.
  Instance free_locations_EqDecision n σ :
    EqDecision (free_locations n σ).
  Proof.
    intros l1 l2.
    destruct (decide (`l1 = `l2)) as [Heq|Hneq].
    - apply dsig_eq in Heq. by left.
    - right. intros Heq. apply Hneq. by apply dsig_eq.
  Qed.
End free_locations.

Section semantics.
  (* We first define some abstractions for manipulating memory that we can
  reuse in the definition of the semantics of heaplang ([compile_expr]). In
  turn, we also get to reuse reasoning principles about these abstractions. *)

  (** Store [x] at memory cell [l] and return the old value. It exhibits UB if
  the memory cell at [l] is currently free. If [x = None], [l] gets
  deallocated. It does not [yield] nor [step]. *)
  Definition store' `{!stateE state -< E} `{ubE -< E} (l : loc) (x : option val) : itree E val :=
    σ ← trigger EGetState;
    v ← some_some_or_ub (σ.(heap) !! l);
    trigger (ESetState (state_upd_heap (<[l:=x]>) σ));;
    Ret v.
  (** Store [x] at memory cell [l] and return the old value. It exhibits UB if
  the memory cell at [l] is currently free. It does not [yield] nor [step]. *)
  Definition store `{!stateE state -< E} `{ubE -< E} (l : loc) (x : val) : itree E val :=
    store' l (Some x).
  (** Load memory cell [l]. It exhibits UB if the memory cell is free. It does
  not [yield] nor [step]. *)
  Definition load `{!stateE state -< E} `{ubE -< E} (l : loc) : itree E val :=
    σ ← trigger EGetState;
    some_some_or_ub (σ.(heap) !! l).

  (** Do a step and then return [v]. This is used to ensure that the
  postcondition is asserted under a later modality. *)
  Definition step_ret {E} `{laterE -< E} (v : val) : itree E val :=
    later.step ;; Ret v.

  (** The semantic interpretation of [e], before rectifying the recursive
  calls.

  If [e] is not a value, this will exhibit a [step] at the very end of
  the computation, but not a [yield]. This means that if [e] is an atomic
  expression, [compile_expr' e] will not contain any [yield]s. *)
  Fixpoint compile_expr' (e : expr) : itree (callE expr val +' heaplangE) val :=
    (* FIXME: Get rid of these [do]s in favor of [ITreeToTranslate] magic. *)
    (* We redefine a bunch of things we need to lift them from
    [itree heaplangE val] to [itree (callE expr val +' heaplangE) val] using
    [do]. This helps with automation, which can cancel out [interp (rec f)] and
    [do]. *)
    let yield := do yield in
    let yield_if_not_val e := do (yield_if_not_val e) in
    let step := do later.step in
    let store' l x := do (store' l x) in
    let store l x := do (store l x) in
    let load l := do (load l) in
    let ub := do ub in
    let assert P `{Decision P} := do (assert P) in
    let step_ret v := do (step_ret v) in
    (* Assuming [e] is not a value, [compile_expr_yield e] differs from
    [compile_expr' e] in that, before returning the output, it not only does a
    [step] but also a [yield]. This is often appropriate for sequencing
    computations: [v ← compile_expr_yield e; compile_expr' (f v)] evaluates
    [e] to [v], then yields if it did any work, and then continues by
    evaluating [f v], whereas [v ← compile_expr' e; compile_expr' (f v)] would
    not have a [yield], only a [step], in between evaluating [e] and
    evaluating [f v]. *)
    let compile_expr_yield e := (v ← compile_expr' e ; yield_if_not_val e ;; Ret v)%itree in
    (* The general pattern for the placement of [step] and [yield] can be
    loosely explained as follows. In order to prove the results in
    [heaplang/opsem_adequacy.v], we decide to model the semantics as closely to
    the operational semantics as possible (this is a design decision: one could
    still have a meaningful semantics that is defined in another way).
    Whenever we do something corresponding to an opsem step [e ~> e'], there
    should be a [step] to mark that "progress has been made". Moreover, there
    should be a [yield] but only in so far that [e'] is not a value. To
    understand why, consider evaluating some [e] which steps to a value in
    one step [e ~> v]. In that case, [e] is an atomic expression, and
    hence it should not do a [yield] (otherwise, when establishing its [WPi], one
    would need to reestablish the invariants). In summary, [yield]s belong
    where an opsem step has been taken but the computation has not finished
    yet. See [App e1 e2] case for more. *)
    match e with
    (* If [e] is a value, the computation is already over and no yield or step
    is necessary. This is the only place [Ret] appears. In every other case
    (when work has to be done), [step_ret] is used so that a [step] is done
    before returning. *)
    | Val v => Ret v
    (* [Rec f x e ~> RecV f x e] is a single step ending in a value, so we only
    need to do a [step], not a [yield]. *)
    | Rec f x e => step_ret (RecV f x e)
    | App e1 e2 =>
        (* [App e1 e2 ~>* App e1 v]. *)
        v ← compile_expr_yield e2;
        (* [App e1 x ~>* App f x] (for [f] a value). *)
        f ← compile_expr_yield e1;
        (* Let us explain further the use of [compile_expr_yield] in the two
        operations above, using the intuition provided earlier. We are
        modeling the opsem steps [App e1 e2 ~>* App e1 x ~>* App f x]. We
        need [yield] and [step] inbetween each step. [compile_expr_yield e2]
        ends in a [step] and [yield] if at least one opsem step was taken in
        [App e1 e2 ~>* App e1 x], which is the desired behavior. If we used
        just [compile_expr' e2] instead, we would lack the [yield] after the
        last step of [App e1 e2 ~>* App e1 x]. *)
        (* f = λ x, e *)
        '(f_, x_, e) ← (val_to_RecV f)?;
        (* [App f v ~> e[v/x]]. *)
        let body := subst' x_ v  (subst' f_ f e) in
        (* If [e[v/x]] is a value, we are done and so we simply need to [step]
        and return it (remember we don't end on a yield; see comment above
        [compile_expr']). If not, we need to [step], [yield] (to mark the opsem
        step [App f v ~> e[v/x]]), and evaluate it. *)
        step;;
        yield_if_not_val body;;
        call body
    | UnOp op e =>
        v ← compile_expr_yield e;
        v' ← (un_op_eval op v)?;
        step_ret v'
    | BinOp op e1 e2 =>
        v2 ← compile_expr_yield e2;
        v1 ← compile_expr_yield e1;
        v ← (bin_op_eval op v1 v2)?;
        step_ret v
    | If e0 e1 e2 =>
        (* [If e0 e1 e2 ~>* If v0 e1 e2]. *)
        v0 ← compile_expr_yield e0;
        b ← (val_to_bool v0)?;
        if b then
          (* [If true e1 e2 ~> e1]. The [step] and [yield_if_not_val] here
          follows the exact same reasoning as the comments for the [App e1 e2]
          case. *)
          step;;
          yield_if_not_val e1;;
          compile_expr' e1
        else
          (* [If false e1 e2 ~> e2]. *)
          step;;
          yield_if_not_val e2;;
          compile_expr' e2
    | Pair e1 e2 =>
        v2 ← compile_expr_yield e2;
        v1 ← compile_expr_yield e1;
        step_ret (PairV v1 v2)
    | Fst e =>
        v ← compile_expr_yield e;
        '(x, _) ← (val_to_pair v)?;
        step_ret x
    | Snd e =>
        v ← compile_expr_yield e;
        '(_, y) ← (val_to_pair v)?;
        step_ret y
    | InjL e =>
        v ← compile_expr_yield e;
        step_ret (InjLV v)
    | InjR e =>
        v ← compile_expr_yield e;
        step_ret (InjRV v)
    | Case e0 e1 e2 =>
        (* [Case e0 e1 e2 ~> Case v0 e1 e2]. *)
        v0' ← compile_expr_yield e0;
        v0 ← (val_to_sum v0')?;
        match v0 with
        | inl v =>
            (* [Case (inl v) e1 e2 ~> App e1 v]. The [step] and [yield] here
            follows the exact same reasoning as the comments for the [App e1 e2]
            case. We write [yield] instead of the equivalent
            [yield_if_not_value (App e1 (Val v))]. *)
            step ;;
            yield ;;
            call (App e1 (Val v))
        | inr v =>
            (* [Case (inr v) e1 e2 ~> App e2 v]. *)
            step ;;
            yield ;;
            call (App e2 (Val v))
        end
    | Fork e =>
        thread ← trigger EFork;
        match thread with
        | CurrentThread => step_ret (LitV LitUnit)
        | NewThread =>
            (* We use [compile_expr_yield] here instead of [compile_expr]
            (which would be morally the same), because it makes some things in
            [heaplang/opsem_adequacy.v] easier (technical explanation: in the
            simulated trace, we never execute [kill_thread], instead we just
            yield and never yield back to the thread that reached a value,
            which is closer to how completed threads are modeled in the opsem). *)
            v ← compile_expr_yield e;
            kill_thread
        end
    | AllocN ne e =>
        (* Evaluate the arguments. *)
        v ← compile_expr_yield e;
        n' ← compile_expr_yield ne;
        n ← (val_to_int n')?;
        (* Allocating 0 cells is UB. *)
        assert (0 < n)%Z;;
        (* Read the entire heap. *)
        σ ← trigger EGetState;
        (* Demonically pick a free segment of the heap. *)
        l ← trigger (EDemonic (free_locations n σ));
        (* Write the evaluated value [v] to every memory cell in that segment. *)
        trigger (ESetState (state_init_heap (`l) n v σ));;
        step_ret (LitV (LitLoc (`l)))
    | Free e =>
        l' ← compile_expr_yield e;
        l ← (val_to_loc l')?;
        store' l None;;
        step_ret (LitV LitUnit)
    | Load e =>
        l' ← compile_expr_yield e;
        l ← (val_to_loc l')?;
        v ← load l;
        step_ret v
    | Store e1 e2 =>
        v ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        l ← (val_to_loc l')?;
        store l v;;
        step_ret (LitV LitUnit)
    | Xchg e1 e2 =>
        v ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        l ← (val_to_loc l')?;
        v' ← store l v;
        step_ret v'
    | CmpXchg e1 e2 e3 =>
        v2 ← compile_expr_yield e3;
        v1 ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        l ← (val_to_loc l')?;
        w ← load l;
        (* Asserts that equality coincides with the equality of the language. *)
        assert (vals_compare_safe v1 w);;
        if decide (v1 = w) then
          store l v2;;
          step_ret (PairV w (LitV (LitBool true)))
        else step_ret (PairV w (LitV (LitBool false)))
    | FAA e1 e2 =>
        v' ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        v ← (val_to_int v')?;
        l ← (val_to_loc l')?;
        w ← load l;
        n ← (val_to_int w)?;
        store l (LitV (LitInt (n + v)));;
        step_ret (LitV (LitInt n))
    | _ => ub
    end%itree.

  (** The semantic interpretation of [e].

  If [e] is not a value, this will exhibit a [step] at the very end of
  the computation, but not a [yield]. This means that if [e] is an atomic
  expression, [compile_expr' e] will not contain any [yield]s. *)
  Definition compile_expr : expr → itree heaplangE val := rec compile_expr'.

  (** A version of [compile_expr] that produces an ITree that ends with a
  [step] and a [yield] (instead of just a [step]) if [e] is not a value. *)
  Definition compile_expr_yield (e : expr) : itree heaplangE val :=
    v ← compile_expr e ; yield_if_not_val e ;; Ret v.
  Arguments compile_expr_yield !_.

  (** An ITree that evaluates an expression and then terminates the current
  thread. *)
  Definition compile_expr_kill {R} (e : expr) : itree heaplangE R :=
    (* For technical reasons explained in the comments of the [Fork] case in
    [compile_expr'], we use [compile_expr_yield] instead of [compile_expr]. *)
    compile_expr_yield e ;; kill_thread.
  Arguments compile_expr_kill !_.

  Lemma compile_expr_val (v : val) :
    compile_expr (Val v) ≈ Ret v.
  Proof. rewrite /compile_expr/compile_expr'. by eutt_norm. Qed.

  Definition supported_subset_ectx (Ki : ectx_item) : Prop :=
    match Ki with
    | ResolveLCtx _ _ _ => False
    | ResolveMCtx _ _ => False
    | ResolveRCtx _ _ => False
    | _ => True
    end.

  (** Intermediate statement for proving [compile_expr_bind]. *)
  Lemma compile_expr_bind_item (Ki : ectx_item) (e : expr) :
    supported_subset_ectx Ki →
    compile_expr (fill_item Ki e) ≈
      v ← compile_expr_yield e;
      compile_expr (fill_item Ki (Val v)).
  Proof.
    intros Hsubset. destruct Ki; simpl; rewrite /compile_expr_yield/compile_expr;
    try contradiction; eutt_norm; simpl; by eutt_norm.
  Qed.
  (** Intermediate statement for proving [compile_expr_bind]. *)
  Lemma compile_expr_bind_ind K e l :
    Forall supported_subset_ectx K →
    length K = l →
    l > 0 →
    compile_expr (fill K e) ≈
      v ← compile_expr_yield e;
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
    rewrite fill_app /= compile_expr_bind_item // /compile_expr_yield IH // /compile_expr_yield; try lia.
    eutt_norm.
    f_equiv. intros v. rewrite fill_app /=. f_equiv. intros _.
    rewrite compile_expr_bind_item // /compile_expr_yield. eutt_norm. f_equiv. intros v'.
    rewrite !fill_not_val //.
    - replace (length K' + 1) with (S (length K')) in Hlen by lia. injection Hlen as Hlen.
      rewrite Hlen. lia.
    - replace (length K' + 1) with (S (length K')) in Hlen by lia. injection Hlen as Hlen.
      rewrite Hlen. lia.
  Qed.
  (** A semantic bind lemma. This breaks the computation of [K[e]] into a
  computation of [e] to a value [v] and then a computation of [K[v]]. *)
  Lemma compile_expr_bind K e :
    Forall supported_subset_ectx K →
    (* The lemma would not hold with the empty context [K = []], because there
    would be a [yield] too much on the right side of the [≈]. *)
    length K > 0 →
    compile_expr (fill K e) ≈
      (* Here appears [compile_expr_yield] (as opposed to merely
      [compile_expr]) because the computations of [e] and [K[v]] are
      separated by a [yield] (except for when [e = v]). *)
      v ← compile_expr_yield e;
      compile_expr (fill K (Val v)).
  Proof.
    intros Hsubset Hne. by apply compile_expr_bind_ind with (l := length K).
  Qed.

  (** A version of [compile_expr_bind] that also works for the empty context. *)
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
      by eutt_norm.
    - rewrite compile_expr_bind // /compile_expr_yield; last by lia. by eutt_norm.
  Qed.
End semantics.

Class heaplangHGpreS (Σ : gFunctors) := HeapLangHGpreS {
  heaplangH_ghost_varG :> ghost_mapG Σ loc (option val);
}.
Local Existing Instances heaplangH_ghost_varG.
Class heaplangHGS (Σ : gFunctors) := HeapLangHGS {
  heaplangH_inG : heaplangHGpreS Σ;
  heaplangH_heap_name : gname;
  heaplangH_inv_name : namespace;
}.
Local Existing Instances heaplangH_inG.

Definition pointsto `{!heaplangHGS Σ} (l : loc) (v : val) (dq : dfrac) : iProp Σ :=
  l ↪[ heaplangH_heap_name ]{dq} (Some v).

Global Notation "l ↦ v" := (pointsto l v (DfracOwn 1))
  (at level 20, format "l  ↦  v") : bi_scope.
Global Notation "l ↦{ dq } v" := (pointsto l v dq)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.

Section handler.
  Context {Σ} `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  (** The state interpretation for heaplang. It tracks the current heap [σ].
  It only owns a half fraction of it. *)
  Global Instance stateInterp_heaplang : stateInterp Σ state := λ σ,
    ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap).
  (** The other half is stored in an invariant so that we can know that another
  thread won't change it while we have control. *)
  Definition heap_inv : iProp Σ :=
    inv heaplangH_inv_name (∃ σ, ghost_map_auth heaplangH_heap_name (1 / 2) σ.(heap)).

  (** The handler for [heaplangE]. *)
  Definition heaplangH m : iHandler Σ heaplangE :=
    threadpoolH ⊕ ubH ⊕ stateH state ⊕ demonicH ⊕ laterH m.

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

  (** Specification for [load]. One of the useful things about our theory is
  that we get to reuse this specification when proving specifications of the
  various operations that use the [load] abstraction in their definition. *)
  Lemma wpi_load m M l v dq Φ :
    ↑heaplangH_inv_name ⊆ M →
    l ↦{dq} v -∗
    (∀ v', ⌜v' = v⌝ -∗ l ↦{dq} v -∗ Φ v') -∗
    WPi load l @ heaplangH m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (s) "Hauth".
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %Hlu.
    iFrame. iApply wpi_ret. rewrite Hlu. iModIntro. wpi_norm. iApply wpi_ret. by iApply "Hwand".
  Qed.

  Lemma wpi_store' m M l v v' Φ :
    ↑heaplangH_inv_name ⊆ M →
    heap_inv -∗
    l ↦ v -∗
    (∀ r, ⌜r = v⌝ -∗ match v' with Some v' => l ↦ v' | None => True end -∗ Φ r) -∗
    WPi store' l v' @ heaplangH m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "#Hinv Hpointsto Hwand".
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    iApply @wpi_bind. iApply @wpi_get.
    iIntros (σ) "Hauth' !>".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame. iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %->.
    wpi_norm/=. iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "Hauth'".
    rewrite /state_interp/stateInterp_heaplang.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update v' with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame. iApply wpi_ret. iApply wpi_ret. iModIntro.
    iSplitL "Hauth". { by iExists (state_upd_heap (<[l:=v']>) σ). }
    iApply "Hwand"; first done. destruct v'; eauto.
  Qed.

  Lemma wpi_store m M l v v' Φ :
    ↑heaplangH_inv_name ⊆ M →
    heap_inv -∗
    l ↦ v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi store l v' @ heaplangH m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "#Hinv Hpointsto Hwand".
    iApply (wpi_store' with "Hinv Hpointsto"); first done.
    iIntros (r ->) "Hpointsto". by iApply "Hwand".
  Qed.
End handler.

(** Weakest precondition abstraction for heaplang expressions. *)
lock Definition wp_heaplang `{!invGS_gen hlc Σ} `{!heaplangHGS Σ} :
  Wp (iProp Σ) expr val later_modality := λ m M e Φ,
    (heap_inv -∗ WPi compile_expr e @ heaplangH m; M {{ Φ }})%I.
Global Existing Instance wp_heaplang.

Section wp.
  Context `{!invGS_gen hlc Σ} `{!heaplangHGS Σ}.

  Lemma wp_heaplang_unfold e m M Φ :
    WP e @ m; M {{ Φ }} ⊣⊢
    (heap_inv -∗ WPi compile_expr e @ heaplangH m; M {{ Φ }}).
  Proof. by rewrite unlock. Qed.

  (** The total WP implies the partial WP. *)
  Lemma wp_later_weaken e M Φ :
    WP e @ Identity; M {{ Φ }} -∗
    WP e @ Later; M {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold. iIntros "#Hinv".
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
    Forall supported_subset_ectx K →
    WP e @ m; ⊤ {{ v,
      WP fill K (Val v) @ m; ⊤ {{ Φ }}
    }} -∗
    WP fill K e @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros (Hs) "Hwp". rewrite !wp_heaplang_unfold.
    iIntros "#Hinv". iSpecialize ("Hwp" with "Hinv").
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
    iIntros "Hwp". rewrite !wp_heaplang_unfold. iIntros "#Hinv".
    setoid_rewrite <- wpi_clear_mask. iMod "Hwp". iMod ("Hwp" with "Hinv") as "Hwp".
    iApply wpi_wand; last done. iIntros (r) "HΦ". by iMod "HΦ".
  Qed.

  (* Proof rules for various operations: *)

  Lemma wp_App m f_ x_ v e Φ :
    lat m (WP (subst' x_ v  (subst' f_ (RecV f_ x_ e) e)) @ m; ⊤ {{ Φ }}) -∗
    WP (App (Val (RecV f_ x_ e)) (Val v)) @ m; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite !wp_heaplang_unfold. iIntros "#Hinv".
    rewrite /compile_expr. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_step.
    iApply lat_mono; last done. iIntros "Hwp". iDestruct ("Hwp" with "Hinv") as "Hwp".
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
    iIntros "Hwp". rewrite !wp_heaplang_unfold. iIntros "#Hinv".
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
    iIntros "HΦ Hwp". rewrite !wp_heaplang_unfold. iIntros "#Hinv".
    iSpecialize ("Hwp" with "Hinv").
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
    ↑heaplangH_inv_name ⊆ M →
    lat m (∀ l,
       ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v) -∗
       Φ (LitV (LitLoc l))
    ) -∗
    WP AllocN (Val (LitV (LitInt n))) (Val v) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hpos Hmask) "Hwand".
    rewrite wp_heaplang_unfold /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_open_invariant_timeless; eauto; first apply _. iIntros "[%σ' Hauth]".
    rewrite assert_True //. wpi_norm.
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
    iApply wpi_ret. iApply wpi_step_ret. iModIntro.
    iApply (lat_mono with "[Hauth Hfrag]"); last done. iIntros "Hpost".
    iSplitL "Hauth". { by iExists (state_init_heap (`l) n v σ). }
    iApply "Hpost". iApply big_sep_map_list_heap_array. rewrite Loc.add_0 //.
  Qed.

  Lemma wp_Load m M l v dq Φ :
    ↑heaplangH_inv_name ⊆ M →
    l ↦{dq} v -∗
    lat m (l ↦{dq} v -∗ Φ v) -∗
    WP Load (Val $ LitV $ LitLoc l) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_bind. iApply (wpi_load with "Hpointsto"); first done. iIntros (v' ->) "Hpointsto".
    iApply wpi_step_ret. iApply (lat_mono with "[Hpointsto]"); last done.
    iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Store m M l v v' Φ :
    ↑heaplangH_inv_name ⊆ M →
    l ↦ v -∗
    lat m (∀ r, ⌜r = LitV (LitUnit)⌝ -∗ l ↦ v' -∗ Φ r) -∗
    WP Store (Val $ LitV $ LitLoc l) (Val v') @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite !wp_heaplang_unfold /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_bind. iApply (wpi_store with "Hinv Hpointsto"); first done.
    iIntros "Hpointsto". iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_Free m M l v Φ :
    ↑heaplangH_inv_name ⊆ M →
    l ↦ v -∗
    lat m (Φ (LitV LitUnit)) -∗
    WP Free (Val $ LitV $ LitLoc l) @ m; M {{ Φ }}.
  (* Very slight variant of the proof of [wpi_Store]: *)
  Proof.
    iIntros (Hmask) "Hpointsto HΦ".
    rewrite wp_heaplang_unfold /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_bind. iApply (wpi_store' with "Hinv Hpointsto"); first done.
    iIntros (r) "_ _". by iApply wpi_step_ret.
  Qed.

  Lemma wp_Xchg m M l v v' Φ :
    ↑heaplangH_inv_name ⊆ M →
    l ↦ v -∗
    lat m (l ↦ v' -∗ Φ v) -∗
    WP Xchg (Val $ LitV (LitLoc l)) (Val v') @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_bind. iApply (wpi_store with "Hinv Hpointsto"); first done.
    iIntros "Hpointsto". iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_CmpXchg_fail m M l dq v' v1 v2 Φ :
    ↑heaplangH_inv_name ⊆ M →
    v' ≠ v1 →
    vals_compare_safe v' v1 →
    l ↦{dq} v' -∗
    lat m (l ↦{dq} v' -∗ Φ (PairV v' (LitV $ LitBool false))) -∗
    WP CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask Hneq Hcmp) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold  /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_bind. iApply (wpi_load with "Hpointsto"); first done.
    iIntros (r ->) "Hpointsto".
    rewrite /assert /= decide_True // decide_False //. wpi_norm/=.
    iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_CmpXchg_suc m M l v' v1 v2 Φ :
    ↑heaplangH_inv_name ⊆ M →
    v' = v1 →
    vals_compare_safe v' v1 →
    l ↦ v' -∗
    lat m (l ↦ v2 -∗ Φ (PairV v' (LitV $ LitBool true))) -∗
    WP CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask Hneq Hcmp) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_bind. iApply (wpi_load with "Hpointsto"); first done.
    iIntros (r ->) "Hpointsto".
    rewrite /assert /= decide_True // decide_True //. wpi_norm.
    iApply wpi_bind. iApply (wpi_store with "Hinv Hpointsto"); first done.
    iIntros "Hpointsto". iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.

  Lemma wp_FAA m M l i1 i2 Φ :
    ↑heaplangH_inv_name ⊆ M →
    l ↦ LitV (LitInt i1) -∗
    lat m (l ↦ LitV (LitInt (i1 + i2)) -∗ Φ (LitV (LitInt i1))) -∗
    WP FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ m; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    rewrite wp_heaplang_unfold /compile_expr. iIntros "#Hinv". wpi_norm/=.
    iApply wpi_bind. iApply (wpi_load with "Hpointsto"); first done.
    iIntros (r ->) "Hpointsto".
    wpi_norm/=. iApply wpi_bind. iApply (wpi_store with "Hinv Hpointsto"); first done.
    iIntros "Hpointsto". iApply wpi_step_ret.
    iApply (lat_mono with "[Hpointsto]"); last done. iIntros "Hwand". by iApply "Hwand".
  Qed.
End wp.

Section soundness.
  (** Lemma for initializing the ghost state for [WP]. *)
  Lemma heaplangH_init `{!invGS_gen hlc Σ} `{!heaplangHGpreS Σ} σ :
    ⊢ |={∅}=> ∃ _ : heaplangHGS Σ, heap_inv ∗ state_interp σ ∗ [∗ map] k↦v ∈ σ.(heap), k ↪[heaplangH_heap_name] v.
  Proof.
    iDestruct (ghost_map_alloc (K := loc) (V := option val) (σ.(heap))) as "Hgmap".
    iMod "Hgmap" as "[%γ [[Hauth' Hauth] Hfrag]]".
    iDestruct (inv_alloc (nroot .@ "heaplangH") (∅) ((∃ σ, ghost_map_auth γ (1 / 2) σ.(heap))%I)) as "Hinv".
    iSpecialize ("Hinv" with "[Hauth]"). { iNext. by iExists σ. }
    iMod "Hinv". iModIntro.
    iExists (HeapLangHGS Σ _ γ (nroot .@ "heaplangH")).
    iFrame.
  Qed.

  (** Lemma useful for extract a proposition in classical logic [P] from a
  proof inside the program logic. *)
  Lemma heaplang_soundness n σ `{!invGpreS Σ} `{!heaplangHGpreS Σ} P:
    (∀ {HG : invGS Σ} {HS : heaplangHGS Σ},
      ⊢ heap_inv -∗ state_interp σ -∗ £ n ={⊤,∅}=∗ |={∅}▷=>^n ⌜P⌝) →
    P.
  Proof.
    move => Hwp.
    eapply uPred.pure_soundness.
    eapply (step_fupdN_soundness_lc _ n n) => ?/=.
    iIntros "Hlc". iMod (fupd_mask_subseteq ∅) as "Hm"; [done|].
    iMod heaplangH_init as (?) "[? [??]]".
    iMod "Hm". iApply (Hwp with "[$] [$] [$]").
  Qed.
End soundness.
