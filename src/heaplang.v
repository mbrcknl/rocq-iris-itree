From stdpp Require Import countable numbers gmap strings stringmap.
From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi threadpool choice ub state handler.
From iris.prelude Require Import prelude.
From iris Require Import gen_heap.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.

Record loc := Loc { loc_car : Z }.

Add Printing Constructor loc.

Module Loc.
  Local Open Scope Z_scope.

  Lemma eq_spec l1 l2 : l1 = l2 ↔ loc_car l1 = loc_car l2.
  Proof. destruct l1, l2; naive_solver. Qed.

  Global Instance eq_dec : EqDecision loc.
  Proof. solve_decision. Defined.

  Global Instance inhabited : Inhabited loc := populate {|loc_car := 0 |}.

  Global Instance countable : Countable loc.
  Proof. by apply (inj_countable' loc_car Loc); intros []. Defined.

  Global Program Instance infinite : Infinite loc :=
    inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
  Next Obligation. done. Qed.

  Definition add (l : loc) (off : Z) : loc :=
    {| loc_car := loc_car l + off|}.

  Definition le (l1 l2 : loc) : Prop := loc_car l1 ≤ loc_car l2.

  Definition lt (l1 l2 : loc) : Prop := loc_car l1 < loc_car l2.

  Module Import notations.
    Notation "l +ₗ off" :=
      (add l off) (at level 50, left associativity) : stdpp_scope.
    Notation "l1 ≤ₗ l2" := (le l1 l2) (at level 70) : stdpp_scope.
    Notation "l1 <ₗ l2" := (lt l1 l2) (at level 70) : stdpp_scope.
  End notations.

  Lemma add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
  Proof. rewrite eq_spec /=. lia. Qed.

  Lemma add_0 l : l +ₗ 0 = l.
  Proof. rewrite eq_spec /=; lia. Qed.

  Global Instance add_inj l : Inj eq eq (add l).
  Proof. intros x1 x2. rewrite eq_spec /=. lia. Qed.

  Global Instance le_dec l1 l2 : Decision (l1 ≤ₗ l2).
  Proof. rewrite /le. apply _. Qed.

  Global Instance lt_dec l1 l2 : Decision (l1 <ₗ l2).
  Proof. rewrite /lt. apply _. Qed.

  Global Instance le_po : PartialOrder le.
  Proof.
    rewrite /le. split; [split|].
    - by intros ?.
    - intros [x] [y] [z]; lia.
    - intros [x] [y] ??; f_equal/=; lia.
  Qed.

  Global Instance le_total : Total le.
  Proof. rewrite /Total /le. lia. Qed.

  Lemma le_ngt l1 l2 : l1 ≤ₗ l2 ↔ ¬l2 <ₗ l1.
  Proof. apply Z.le_ngt. Qed.

  Lemma le_lteq l1 l2 : l1 ≤ₗ l2 ↔ l1 <ₗ l2 ∨ l1 = l2.
  Proof. rewrite eq_spec. apply Z.le_lteq. Qed.

  Lemma add_le_mono l1 l2 i1 i2 :
    l1 ≤ₗ l2 → i1 ≤ i2 → l1 +ₗ i1 ≤ₗ l2 +ₗ i2.
  Proof. apply Z.add_le_mono. Qed.

  Definition fresh (ls : gset loc) : loc :=
    {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r) 1 ls |}.

  Lemma fresh_fresh ls i : 0 ≤ i → fresh ls +ₗ i ∉ ls.
  Proof.
    intros Hi. cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh ls) + i).
    { intros help Hf%help. simpl in *. lia. }
    apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)));
      set_solver by eauto with lia.
  Qed.

  Global Opaque fresh.
End Loc.

Export Loc.notations.

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit
  | LitLoc (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  (** We use "quot" and "rem" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30/-4 == 7. ("div" would return 8.) *)
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : string) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | Free (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  | Xchg (e0 : expr) (e1 : expr) (* exchange *)
  | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
  (* Concurrency *)
  | Fork (e : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : string) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

(* Parallel substitution *)
Fixpoint subst_map (vs : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (delete y (delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e => Fst (subst_map vs e)
  | Snd e => Snd (subst_map vs e)
  | InjL e => InjL (subst_map vs e)
  | InjR e => InjR (subst_map vs e)
  | Case e0 e1 e2 => Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Fork e => Fork (subst_map vs e)
  | AllocN e1 e2 => AllocN (subst_map vs e1) (subst_map vs e2)
  | Free e => Free (subst_map vs e)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | Xchg e1 e2 => Xchg (subst_map vs e1) (subst_map vs e2)
  | CmpXchg e0 e1 e2 => CmpXchg (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | FAA e1 e2 => FAA (subst_map vs e1) (subst_map vs e2)
  end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.

Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  | LitInt _ | LitBool _  | LitLoc _ | LitUnit => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fst e, Fst e' => cast_if (decide (e = e'))
     | Snd e, Snd e' => cast_if (decide (e = e'))
     | InjL e, InjL e' => cast_if (decide (e = e'))
     | InjR e, InjR e' => cast_if (decide (e = e'))
     | Case e0 e1 e2, Case e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | AllocN e1 e2, AllocN e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Free e, Free e' =>
        cast_if (decide (e = e'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | CmpXchg e0 e1 e2, CmpXchg e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Xchg e0 e1, Xchg e0' e1' =>
        cast_if_and (decide (e0 = e0')) (decide (e1 = e1'))
     | FAA e1 e2, FAA e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fork e, Fork e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   for go); try (clear go gov; abstract intuition congruence).
Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

(** The state: heaps of [option val]s, with [None] representing deallocated locations. *)
Record state : Type := {
  heap: gmap loc val;
}.

Definition state_upd_heap (f: gmap loc val → gmap loc val) (σ : state) : state :=
  {| heap := f σ.(heap) |}.
Global Arguments state_upd_heap _ !_ /.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc val :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = w ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite Loc.add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite Loc.add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite Loc.add_0; eauto. }
    right. split.
    { rewrite -{1}(Loc.add_0 l). intros ?%(inj (Loc.add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite Loc.add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc val) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

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

Definition compile_expr' (e : expr) : itree (callE expr val +' heaplangE) val :=
  match e with
  | Val v => Ret v
  | Rec f x e => Ret (RecV f x e)
  | App e1 e2 =>
      x ← call e2;
      f ← call e1;
      match f with
      | RecV f_ x_ e => call (subst_map ({[f_:=f; x_:=x]}) e1)
      | _ => ub
      end
  | UnOp op e =>
      v ← call e;
      match un_op_eval op v with
      | Some v => Ret v
      | None => ub
      end
  | BinOp op e1 e2 =>
      v1 ← call e1;
      v2 ← call e2;
      match bin_op_eval op v1 v2 with
      | Some v => Ret v
      | None => ub
      end
  | If e0 e1 e2 =>
      v0 ← call e0;
      match v0 with
      | LitV (LitBool b) => if b then call e1 else call e2
      | _ => ub
      end
  | Pair e1 e2 =>
      v1 ← call e1;
      v2 ← call e2;
      Ret (PairV v1 v2)
  | Fst e =>
      v ← call e;
      match v with
      | PairV x _ => Ret x
      | _ => ub
      end
  | Snd e =>
      v ← call e;
      match v with
      | PairV _ y => Ret y
      | _ => ub
      end
  | InjL e =>
      v ← call e;
      Ret (InjLV v)
  | InjR e =>
      v ← call e;
      Ret (InjRV v)
  | Case e0 e1 e2 =>
      v0 ← call e0;
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
          v ← call e;
          match v with
          | LitV LitUnit =>
              x ← trigger EKillThread : itree _ Empty_set;
              match x with end
          | _ => ub
          end
      end
  | AllocN ne e =>
      v ← call e;
      n ← call ne;
      match n with
      | LitV (LitInt n) =>
          trigger EYield;;
          σ ← trigger EGetState;
          l ← trigger (EDemonic {l : loc | ∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (l +ₗ i) = None});
          trigger (ESetState (state_init_heap (proj1_sig l) n v σ));;
          Ret (LitV LitUnit)
      | _ => ub
      end
  | Free e =>
      l ← call e;
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some _ =>
              trigger (ESetState (state_upd_heap (delete l) σ));;
              Ret (LitV LitUnit)
          | _ => ub
          end
      | _ => ub
      end
  | Load e =>
      l ← call e;
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some v =>
              Ret v
          | _ => ub
          end
      | _ => ub
      end
  | Store e1 e2 =>
      v ← call e2;
      l ← call e1;
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some w =>
              trigger (ESetState (state_upd_heap <[l:=v]> σ));;
              Ret (LitV LitUnit)
          | _ => ub
          end
      | _ => ub
      end
  | Xchg e1 e2 =>
      v ← call e2;
      l ← call e1;
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some w =>
              trigger (ESetState (state_upd_heap <[l:=v]> σ));;
              Ret w
          | _ => ub
          end
      | _ => ub
      end
  | CmpXchg le e1 e2 =>
      v2 ← call e2;
      v1 ← call e1;
      l ← call le;
      match l with
      | LitV (LitLoc l) =>
          trigger EYield;;
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some w =>
              (* Asserts that equality coincides with the equality of the language. *)
              trigger (EDemonic (vals_compare_safe v1 w));;
              if decide (v1 = w) then
                trigger (ESetState (state_upd_heap <[l:=v2]> σ));;
                Ret w
              else Ret w
          | _ => ub
          end
      | _ => ub
      end
  | FAA e1 e2 =>
      v ← call e2;
      l ← call e1;
      match (v, l) with
      | (LitV (LitInt v), LitV (LitLoc l)) =>
          trigger EYield;;
          σ ← trigger EGetState;
          match σ.(heap) !! l with
          | Some (LitV (LitInt n)) =>
              trigger (ESetState (state_upd_heap <[l:=LitV (LitInt (n + v))]> σ));;
              Ret (LitV (LitInt n))
          | _ => ub
          end
      | _ => ub
      end
  | _ => ub
  end%itree.

Definition compile_expr : expr → itree heaplangE val := rec compile_expr'.

Class heaplangHPreG (Σ : gFunctors) := HeapLangHPreG {
  heaplangH_pre_ghost_varG :> gen_heapGpreS loc val Σ;
}.
Class heaplangHGS (Σ : gFunctors) := HeapLangHGS {
  heaplangH_ghost_varGS :> gen_heapGS loc val Σ;
}.
Definition heaplangHΣ : gFunctors :=
  gen_heapΣ loc val.
Global Instance subG_heaplangHΣ Σ :
  subG heaplangHΣ Σ → heaplangHPreG Σ.
Proof. solve_inG. Qed.

Global Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

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
    iIntros "HΦ Hwp". iEval (rewrite /compile_expr rec_as_interp /= interp_bind ).
    iApply wpi_bind.
    setoid_rewrite interp_trigger. iApply (wpi_yield (H := heaplangH)).
    rewrite interp_bind. setoid_rewrite interp_trigger. simpl.
    rewrite bind_trigger. iApply (wpi_fork (H := heaplangH)). iSplitL "HΦ".
    - rewrite interp_ret. by iApply wpi_ret.
    - rewrite interp_bind. iApply wpi_bind. setoid_rewrite interp_trigger. simpl.
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
    iEval (rewrite /compile_expr rec_as_interp /= interp_bind).
    iApply wpi_bind.
    setoid_rewrite interp_trigger. iApply (wpi_wand with "[Hn] Hv"). iIntros (r ->).
    setoid_rewrite interp_bind. iApply wpi_bind. setoid_rewrite interp_trigger.
    iApply (wpi_wand with "[] Hn"). iIntros (r ->).
    setoid_rewrite interp_bind. iApply wpi_bind. setoid_rewrite interp_trigger.
    iApply (wpi_yield (H := heaplangH)).
    setoid_rewrite interp_bind. iApply wpi_bind. setoid_rewrite interp_trigger.
    iApply (wpi_get (H := heaplangH)).
    iIntros (s) "$ !>". iApply wpi_ret.
    setoid_rewrite interp_bind. iApply wpi_bind. setoid_rewrite interp_trigger.
    iApply (wpi_demonic (H := heaplangH)). iIntros (l). iApply wpi_ret.
    setoid_rewrite interp_bind. iApply wpi_bind. setoid_rewrite interp_trigger.
    iApply (wpi_set (H := heaplangH)). iIntros (s') "Hstate".
End heaplangH.
