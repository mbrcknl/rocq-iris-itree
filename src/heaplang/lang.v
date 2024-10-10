From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi choice ub heap handler itree step.
From iris.itree.threadpool Require Import handler.
From iris.prelude Require Import prelude.
From elpi.apps Require Import locker.
From iris.itree.heaplang Require Export definition.

Definition sequential_heaplangE : Type → Type := ubE +' heapE val +' demonicE +' stepE.
(** The event type for heaplang. *)
Definition heaplangE : Type → Type := threadpoolE +' sequential_heaplangE.
Global Hint Transparent sequential_heaplangE : itree_auto.
Global Hint Transparent heaplangE : itree_auto.

Notation heaplang_heap := (heap.heap val).

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
Definition yield_if_not_val (e : expr) {E} `{threadpoolE -< E} : itree E () :=
  match to_val e with
  | Some _ => Ret ()
  | None => yield
  end.
Arguments yield_if_not_val !_ / _.

Lemma yield_if_not_val_to_translate {E1 E2} (HE1 : threadpoolE -< E1) (HE2 : threadpoolE -< E2) (Hin : E1 -< E2) e :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (yield_if_not_val e) Hin (yield_if_not_val e).
Proof.
  move => ?. rewrite /yield_if_not_val. destruct (to_val e).
  - apply Ret_to_translate.
  - by apply yield_to_translate.
Qed.
Global Hint Resolve yield_if_not_val_to_translate : itree_auto.

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
Notation "x ?" := (do $ some_or_ub x) (at level 10, format "x ?") : itree_scope.

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

(** Do a step and then return [v]. This is used to ensure that the
postcondition is asserted under a later modality. *)
Definition step_ret {E} `{stepE -< E} (v : val) : itree E val :=
  step.step ;; Ret v.

Lemma step_ret_to_translate {E1 E2} (HE1 : stepE -< E1) (HE2 : stepE -< E2) (Hin : E1 -< E2) v :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (step_ret v) Hin (step_ret v).
Proof.
  move => ?. rewrite /step_ret. apply bind_to_translate.
  - by apply step_to_translate.
  - intros _. apply Ret_to_translate.
Qed.
Global Hint Resolve step_ret_to_translate : itree_auto.

Section semantics.
  (* We first define some abstractions for manipulating memory that we can
  reuse in the definition of the semantics of heaplang ([compile_expr]). In
  turn, we also get to reuse reasoning principles about these abstractions. *)

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
    let yield_if_not_val e := do (yield_if_not_val e) in
    let store'_or_ub l x := do (store'_or_ub l x) in
    let store_or_ub l x := do (store_or_ub l x) in
    let load_or_ub l := do (load_or_ub l) in
    let allocN_nondet n v := do (allocN_nondet n v) in
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
        let body := subst' x_ v (subst' f_ f e) in
        (* If [e[v/x]] is a value, we are done and so we simply need to [step]
        and return it (remember we don't end on a yield; see comment above
        [compile_expr']). If not, we need to [step], [yield] (to mark the opsem
        step [App f v ~> e[v/x]]), and evaluate it. *)
        step.step;;
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
          step.step;;
          yield_if_not_val e1;;
          compile_expr' e1
        else
          (* [If false e1 e2 ~> e2]. *)
          step.step;;
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
            step.step ;;
            yield ;;
            call (App e1 (Val v))
        | inr v =>
            (* [Case (inr v) e1 e2 ~> App e2 v]. *)
            step.step ;;
            yield ;;
            call (App e2 (Val v))
        end
    | Fork e =>
        spawn (compile_expr_yield e ;; Ret ()) ;;
        step_ret (LitV LitUnit)
    | AllocN ne e =>
        (* Evaluate the arguments. *)
        v ← compile_expr_yield e;
        n' ← compile_expr_yield ne;
        n ← (val_to_int n')?;
        (* Allocating 0 cells is UB. *)
        assert (0 < n)%Z;;
        (* Read the entire heap. *)
        l ← allocN_nondet (Z.to_nat n) v;
        step_ret (LitV (LitLoc l))
    | Free e =>
        l' ← compile_expr_yield e;
        l ← (val_to_loc l')?;
        store'_or_ub l None;;
        step_ret (LitV LitUnit)
    | Load e =>
        l' ← compile_expr_yield e;
        l ← (val_to_loc l')?;
        v ← load_or_ub l;
        step_ret v
    | Store e1 e2 =>
        v ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        l ← (val_to_loc l')?;
        store_or_ub l v;;
        step_ret (LitV LitUnit)
    | Xchg e1 e2 =>
        v ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        l ← (val_to_loc l')?;
        v' ← store_or_ub l v;
        step_ret v'
    | CmpXchg e1 e2 e3 =>
        v2 ← compile_expr_yield e3;
        v1 ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        l ← (val_to_loc l')?;
        w ← load_or_ub l;
        (* Asserts that equality coincides with the equality of the language. *)
        assert (vals_compare_safe v1 w);;
        if decide (v1 = w) then
          store_or_ub l v2;;
          step_ret (PairV w (LitV (LitBool true)))
        else step_ret (PairV w (LitV (LitBool false)))
    | FAA e1 e2 =>
        v' ← compile_expr_yield e2;
        l' ← compile_expr_yield e1;
        v ← (val_to_int v')?;
        l ← (val_to_loc l')?;
        w ← load_or_ub l;
        n ← (val_to_int w)?;
        store_or_ub l (LitV (LitInt (n + v)));;
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

  (** Intermediate statement for proving [compile_expr_bind]. *)
  Lemma compile_expr_bind_item (Ki : ectx_item) (e : expr) :
    compile_expr (fill_item Ki e) ≈
      v ← compile_expr_yield e;
      compile_expr (fill_item Ki (Val v)).
  Proof.
    destruct Ki; simpl; rewrite /compile_expr_yield/compile_expr;
    try contradiction; eutt_norm; simpl; by eutt_norm.
  Qed.
  (** Intermediate statement for proving [compile_expr_bind]. *)
  Lemma compile_expr_bind_ind K e l :
    length K = l →
    l > 0 →
    compile_expr (fill K e) ≈
      v ← compile_expr_yield e;
      compile_expr (fill K (Val v)).
  Proof.
    revert K. induction l as [|n IH]; intros K Hlen Hne.
    { apply nil_length_inv in Hlen. lia. }
    destruct n as [|n'].
    { apply list_singleton in Hlen as [x ->]. simpl. rewrite compile_expr_bind_item //. }
    unshelve epose (split_last K _) as Hsplit; first lia. destruct Hsplit as (Ki&K'&->).
    rewrite app_length /= in Hlen.
    rewrite Nat.add_comm in Hlen.
    injection Hlen as Hlen.
    rewrite fill_app /= compile_expr_bind_item // /compile_expr_yield IH // /compile_expr_yield; try lia.
    eutt_norm.
    f_equiv. intros v. rewrite fill_app /=. f_equiv. intros _.
    rewrite compile_expr_bind_item // /compile_expr_yield. eutt_norm. f_equiv. intros v'.
    rewrite !fill_not_val // Hlen; lia.
  Qed.
  (** A semantic bind lemma. This breaks the computation of [K[e]] into a
  computation of [e] to a value [v] and then a computation of [K[v]]. *)
  Lemma compile_expr_bind K e :
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
    intros Hne. by apply compile_expr_bind_ind with (l := length K).
  Qed.

  (** A version of [compile_expr_bind] that also works for the empty context. *)
  Lemma compile_expr_bind' K e :
    compile_expr (fill K e) ≈
      v ← compile_expr e;
      if (decide (length K = 0)) then
        Ret v
      else
        yield_if_not_val e;;
        compile_expr (fill K (Val v)).
  Proof.
    destruct (decide _) as [Heq|Hneq].
    - apply nil_length_inv in Heq as ->.
      by eutt_norm.
    - rewrite compile_expr_bind // /compile_expr_yield; last by lia. by eutt_norm.
  Qed.
End semantics.
