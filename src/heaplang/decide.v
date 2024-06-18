From iris.prelude Require Import prelude.
From iris.heap_lang Require Export lang locations.
From iris.itree.heaplang Require Import lang.

Lemma of_to_val_iff e v:
  to_val e = Some v ↔ Val v = e.
Proof. split; [apply of_to_val| by move => <-]. Qed.

Fixpoint expr_depth (e : expr) : nat :=
  match e with
  | Val v => 0
  | Var _ | Rec _ _ _ | NewProph => 1
  | Fst e | Snd e | InjL e | InjR e | Free e
  | Load e | Fork e | UnOp _ e => S (expr_depth e)
  | App e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2
  | Xchg e1 e2 | FAA e1 e2 | BinOp _ e1 e2 => S (expr_depth e1 `max` expr_depth e2)
  | Case e1 e2 e3 | CmpXchg e1 e2 e3 | Resolve e1 e2 e3
  | If e1 e2 e3 => S (expr_depth e1 `max` expr_depth e2 `max` expr_depth e3)
  end.

Lemma expr_depth_fill_item Ki e:
  expr_depth e < expr_depth (fill_item Ki e).
Proof. elim: Ki => //=; lia. Qed.


Fixpoint split_expr_ectx_item (e : expr) : option (ectx_item * expr) :=
  match e with
  | App e1 e2 =>
      match to_val e1, to_val e2 with
      | Some _, Some _ => None
      | _, Some v2 => Some (AppLCtx v2, e1)
      | _, _ => Some (AppRCtx e1, e2)
      end
  | UnOp op e => if to_val e is Some _ then None else  Some (UnOpCtx op, e)
  | BinOp op e1 e2 =>
      match to_val e1, to_val e2 with
      | Some _, Some _ => None
      | _, Some v2 => Some (BinOpLCtx op v2, e1)
      | _, _ => Some (BinOpRCtx op e1, e2)
      end
  | If e1 e2 e3 => if to_val e1 is Some _ then None else Some (IfCtx e2 e3, e1)
  | Pair e1 e2 =>
      match to_val e1, to_val e2 with
      | Some _, Some _ => None
      | _, Some v2 => Some (PairLCtx v2, e1)
      | _, _ => Some (PairRCtx e1, e2)
      end
  | Fst e => if to_val e is Some _ then None else  Some (FstCtx, e)
  | Snd e => if to_val e is Some _ then None else  Some (SndCtx, e)
  | InjL e => if to_val e is Some _ then None else  Some (InjLCtx, e)
  | InjR e => if to_val e is Some _ then None else  Some (InjRCtx, e)
  | Case e1 e2 e3 => if to_val e1 is Some _ then None else Some (CaseCtx e2 e3, e1)
  | AllocN e1 e2 =>
      match to_val e1, to_val e2 with
      | Some _, Some _ => None
      | _, Some v2 => Some (AllocNLCtx v2, e1)
      | _, _ => Some (AllocNRCtx e1, e2)
      end
  | Free e => if to_val e is Some _ then None else  Some (FreeCtx, e)
  | Load e => if to_val e is Some _ then None else  Some (LoadCtx, e)
  | Store e1 e2 =>
      match to_val e1, to_val e2 with
      | Some _, Some _ => None
      | _, Some v2 => Some (StoreLCtx v2, e1)
      | _, _ => Some (StoreRCtx e1, e2)
      end
  | CmpXchg e1 e2 e3 =>
      match to_val e1, to_val e2, to_val e3 with
      | Some _, Some _, Some _ => None
      | _, Some v2, Some v3 => Some (CmpXchgLCtx v2 v3, e1)
      | _, _, Some v3 => Some (CmpXchgMCtx e1 v3, e2)
      | _, _, _ => Some (CmpXchgRCtx e1 e2, e3)
      end
  | Xchg e1 e2 =>
      match to_val e1, to_val e2 with
      | Some _, Some _ => None
      | _, Some v2 => Some (XchgLCtx v2, e1)
      | _, _ => Some (XchgRCtx e1, e2)
      end
  | FAA e1 e2 =>
      match to_val e1, to_val e2 with
      | Some _, Some _ => None
      | _, Some v2 => Some (FaaLCtx v2, e1)
      | _, _ => Some (FaaRCtx e1, e2)
      end
  | Resolve e1 e2 e3 =>
      match to_val e1, to_val e2, to_val e3 with
      | Some _, Some _, Some _ => None
      | _, Some v2, Some v3 =>
          prod_map (λ Ki, ResolveLCtx Ki v2 v3) id <$> split_expr_ectx_item e1
      | _, _, Some v3 => Some (ResolveMCtx e1 v3, e2)
      | _, _, _ => Some (ResolveRCtx e1 e2, e3)
      end
  | _ => None
  end.


Lemma split_expr_ectx_item_correct1 e Ki e' :
  to_val e' = None →
  split_expr_ectx_item e = Some (Ki, e') ↔ e = fill_item Ki e'.
Proof.
  move: Ki e'.
  induction e => Ki e' //= He; split => //; move: He.
  all: repeat (case_match eqn: Hx; revert Hx); destruct Ki => //=.
  all: rewrite ?of_to_val_iff ?fmap_Some.
  (* The previous proof script carefully makes sure that only the
  induction hypothesis are cleared by the clear. We need to clear them
  as otherwise naive_solver diverges. *)
  all: try (clear; naive_solver).
  - move => ? ? ? ? [[? ?] [? ?]]. simplify_eq/=.
    f_equal. by apply IHe1.
  - move => ? ? ? ? ?. simplify_eq/=. by destruct Ki.
  - move => ? ? ? ? ?. simplify_eq/=. eexists (_, _). split; [|done].
    by apply IHe1.
Qed.

Lemma split_expr_ectx_item_correct2 e Ki e' :
  split_expr_ectx_item e = Some (Ki, e') → to_val e' = None.
Proof.
  elim: e Ki e' => //= *; repeat case_match => //; simplify_eq/= => //.
  revert select (_ <$> _ = Some _) => /fmap_Some[[? ?] [? ?]].
  naive_solver.
Qed.

Lemma split_expr_ectx_item_correct e Ki e' :
  split_expr_ectx_item e = Some (Ki, e') ↔ e = fill_item Ki e' ∧ to_val e' = None.
Proof.
  split => He. 2: rewrite split_expr_ectx_item_correct1; naive_solver.
  rewrite -split_expr_ectx_item_correct1.
  - split; [done|]. by apply: split_expr_ectx_item_correct2.
  - by apply: split_expr_ectx_item_correct2.
Qed.

Lemma split_expr_ectx_item_sub_redexes e :
  split_expr_ectx_item e = None → sub_redexes_are_values e.
Proof.
  rewrite -eq_None_ne_Some => He.
  apply ectxi_language_sub_redexes_are_values => /= Ki e' ?.
  move: (He (Ki, e')).
  setoid_rewrite split_expr_ectx_item_correct.
  destruct (to_val e'); naive_solver.
Qed.

Fixpoint split_expr_ectx (n : nat) (e : expr) : list ectx_item * expr :=
  match n with
  | S n =>
      match split_expr_ectx_item e with
      | Some (Ki, e) => prod_map (λ x, x ++ [Ki]) id (split_expr_ectx n e)
      | _ => ([], e)
      end
  | _ => ([], e)
  end.

Lemma split_expr_ectx_correct n e:
  e = fill (split_expr_ectx n e).1 (split_expr_ectx n e).2.
Proof.
  elim: n e => //=.
  move => n IH e. case_match eqn:HK; [|done].
  destruct p. rewrite split_expr_ectx_item_correct in HK => /=.
  rewrite fill_app /=.
  destruct HK. by rewrite -IH.
Qed.

Lemma split_expr_ectx_not_val n e :
  to_val e = None → to_val (split_expr_ectx n e).2 = None.
Proof.
  elim: n e => //= n IH e. case_match eqn:HK => //.
  destruct p => /=. move => ?. apply IH.
  by move: HK => /split_expr_ectx_item_correct[? ?].
Qed.

Lemma split_expr_ectx_sub n e:
  expr_depth e ≤ n →
  sub_redexes_are_values (split_expr_ectx n e).2.
Proof.
  elim: n e.
  - move => ? ?. apply ectxi_language_sub_redexes_are_values => /= Ki e' ?.
    subst. pose proof (expr_depth_fill_item Ki e'). lia.
  - move => n IH e /= Hd. case_match eqn:HK.
    + destruct p as [Ki e']. move: HK => /split_expr_ectx_item_correct [? ?].
      simplify_eq/=. apply IH. pose proof (expr_depth_fill_item Ki e'). lia.
    + by apply split_expr_ectx_item_sub_redexes.
Qed.

Local Unset Program Cases.
Global Program Instance base_reducible_dec (e : expr) (σ : state) : Decision (base_reducible e σ) :=
  match e with
  | Rec f x e => left _
  | App (Val (RecV f x e)) (Val v2) => left _
  | Pair (Val v1) (Val v2) => left _
  | UnOp op (Val v) => cast_if (decide (is_Some (un_op_eval op v)))
  | BinOp op (Val v1) (Val v2) => cast_if (decide (is_Some (bin_op_eval op v1 v2)))
  | If (Val (LitV (LitBool _))) e1 e2 => left _
  | Fst (Val (PairV _ _)) => left _
  | Snd (Val (PairV _ _)) => left _
  | InjL (Val _) => left _
  | InjR (Val _) => left _
  | Case (Val (InjLV _)) e1 e2 => left _
  | Case (Val (InjRV _)) e1 e2 => left _
  | AllocN (Val (LitV (LitInt n))) (Val _) => cast_if (decide (0 < n)%Z)
  | Free (Val (LitV (LitLoc l))) => cast_if (decide (is_Some (σ.(heap) !! l ≫= id)))
  | Load (Val (LitV (LitLoc l))) => cast_if (decide (is_Some (σ.(heap) !! l ≫= id)))
  | Store (Val (LitV (LitLoc l))) (Val _) => cast_if (decide (is_Some (σ.(heap) !! l ≫= id)))
  | Xchg (Val (LitV (LitLoc l))) (Val _) => cast_if (decide (is_Some (σ.(heap) !! l ≫= id)))
  | CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2) =>
      cast_if (decide (is_Some (x ← σ.(heap) !! l; vl ← x;
                                if decide (vals_compare_safe vl v1) then
                                  Some tt else None)))
  | FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt _))) => cast_if (decide (is_Some ((σ.(heap) !! l ≫= id) ≫= val_to_int)))
  | Fork e => left _
  (* | NewProph => left _ *)
  (* | Resolve e0 e1 e2 => left _ *)
  | _ => right _
  end.
Solve Obligations with (try (move => /= *; (by repeat econstructor || move => [?[?[?[? Hs]]]]; inv Hs))).
Next Obligation. move => ? ? ? ? ? [? ?]. by repeat econstructor. Qed.
Next Obligation. move => /= *. move => [?[?[?[? Hs]]]]. inv Hs. naive_solver. Qed.
Next Obligation. move => ? ? ? ? ? ? ? [? ?]. by repeat econstructor. Qed.
Next Obligation. move => /= *. move => [?[?[?[? Hs]]]]. inv Hs. naive_solver. Qed.
Next Obligation. move => /= ? ? ? ? ? ? ? []; repeat econstructor. Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? ?. do 4 econstructor. by apply: alloc_fresh.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? [? /bind_Some[? [? ?]]]. simplify_eq/=.
  by repeat econstructor.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? Hr [?[?[?[? Hs]]]]. inv Hs. simplify_option_eq.
  by apply Hr.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? [? /bind_Some[? [? ?]]]. simplify_eq/=.
  by repeat econstructor.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? Hr [?[?[?[? Hs]]]]. inv Hs. simplify_option_eq.
  by apply Hr.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? [? /bind_Some[? [? ?]]]. simplify_eq/=.
  by repeat econstructor.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? Hr [?[?[?[? Hs]]]]. inv Hs. simplify_option_eq.
  by apply Hr.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? ? ? [? /bind_Some[? [? /bind_Some [? [? ?]]]]].
  case_decide => //. simplify_eq/=.
  repeat (econstructor => //).
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? ? ? Hr [?[?[?[? Hs]]]]. inv Hs. simplify_option_eq.
  by apply Hr.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? [? /bind_Some[? [? ?]]]. simplify_eq/=.
  by repeat econstructor.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? Hr [?[?[?[? Hs]]]]. inv Hs. simplify_option_eq.
  by apply Hr.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? ? ? [? /bind_Some[v [/bind_Some [? [? ?]] ?]]]. simplify_eq/=.
  destruct v as [[]| | | |] => //.
  by repeat econstructor.
Qed.
Next Obligation.
  move => /= ? ? ? ? ? ? ? ? ? ? Hr [?[?[?[? Hs]]]]. inv Hs. simplify_option_eq.
  by apply Hr.
Qed.
Next Obligation. Admitted.
Next Obligation. Admitted.

Global Program Instance reducible_dec (e : expr) (σ : state) : Decision (reducible e σ) :=
  cast_if (decide (base_reducible (split_expr_ectx (expr_depth e) e).2 σ)).
Next Obligation.
  move => e σ Hb.
  rewrite (split_expr_ectx_correct (expr_depth e) e).
  by apply reducible_fill, base_prim_reducible.
Qed.
Next Obligation.
  move => e σ /not_base_reducible Hb.
  destruct (to_val e) eqn:Hv.
  { move => /reducible_not_val. naive_solver. }
  rewrite (split_expr_ectx_correct (expr_depth e) e).
  apply not_reducible.
  apply irreducible_fill.
  { by apply split_expr_ectx_not_val. }
  apply prim_base_irreducible; [done|].
  by apply split_expr_ectx_sub.
Qed.

Global Instance stuck_dec (e : expr) σ : Decision (stuck e σ).
Proof.
  destruct (decide (reducible e σ)) as [Hred|Hirr].
  - right. destruct Hred as (κ&e'&σ'&efs&Hstep). intros [_ Hirr].
    by apply Hirr in Hstep.
  - destruct (to_val e) eqn:Hval.
    * right. intros [Hval' _]. destruct e; discriminate.
    * left. split; first done. intros κ e' σ' efs Hstep. apply Hirr.
      by do 4 eexists.
Qed.
