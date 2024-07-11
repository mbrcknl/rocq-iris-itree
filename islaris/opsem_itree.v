From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi choice ub state handler itree halt step.
Require Export isla.opsem.
Require Import isla.spec_itree.

Global Hint Transparent sail_name accessor_list : itree_auto.


Lemma bvn_to_bv_Some n bn b:
  bvn_to_bv n bn = Some b ↔ bn = bv_to_bvn b.
Proof.
  rewrite /bvn_to_bv.
  case_decide as Heq => //.
  - destruct Heq, bn. naive_solver.
  - destruct bn. naive_solver.
Qed.

Lemma bvn_to_bv_to_bvn n (b : bv n) :
  bvn_to_bv n b = Some b.
Proof. by rewrite bvn_to_bv_Some. Qed.


Global Instance base_val_eq_decision : EqDecision base_val.
Proof. solve_decision. Qed.

Global Program Instance valu_eq_decision : EqDecision valu :=
  fix go v1 v2 :=
    match v1, v2 with
    | RegVal_Base b, RegVal_Base b' => cast_if (decide (b = b'))
    | RegVal_I z1 z2, RegVal_I z1' z2' =>
        cast_if_and (decide (z1 = z1')) (decide (z2 = z2'))
    | RegVal_String s, RegVal_String s' =>
        cast_if (decide (s = s'))
    | RegVal_Unit, RegVal_Unit => left _
    | RegVal_Poison, RegVal_Poison => left _
    | RegVal_Vector l, RegVal_Vector l' =>
        (fix inner l1 l2 :=
           match l1, l2 with
           | [], [] => left _
           | x::l1',y::l2' => cast_if_and (go x y) (inner l1' l2')
           | _, _ => right _
           end) l l'
    | RegVal_List l, RegVal_List l' =>
        (fix inner l1 l2 :=
           match l1, l2 with
           | [], [] => left _
           | x::l1',y::l2' => cast_if_and (go x y) (inner l1' l2')
           | _, _ => right _
           end) l l'
    | RegVal_Struct l, RegVal_Struct l' =>
        (fix inner l1 l2 :=
           match l1, l2 with
           | [], [] => left _
           | (x1, x2)::l1', (y1, y2)::l2' => cast_if_and3 (decide (x1 = y1)) (go x2 y2) (inner l1' l2')
           | _, _ => right _
           end) l l'
    | RegVal_Constructor s v, RegVal_Constructor s' v' =>
        cast_if_and (decide (s = s')) (go v v')
    | _, _ => right _
    end.
Solve Obligations with naive_solver.

Global Instance annot_eq_decision : EqDecision annot.
Proof. solve_decision. Defined.

Global Instance ty_eq_decision : EqDecision ty.
Proof. solve_decision. Defined.

Global Instance unop_eq_decision : EqDecision unop.
Proof. solve_decision. Defined.

Global Instance bvarith_eq_decision : EqDecision bvarith.
Proof. solve_decision. Defined.

Global Instance bvcomp_eq_decision : EqDecision bvcomp.
Proof. solve_decision. Defined.

Global Instance binop_eq_decision : EqDecision binop.
Proof. solve_decision. Defined.

Global Instance bvmanyarith_eq_decision : EqDecision bvmanyarith.
Proof. solve_decision. Defined.

Global Instance manyop_eq_decision : EqDecision manyop.
Proof. solve_decision. Defined.

Global Instance accessor_eq_decision : EqDecision accessor.
Proof. solve_decision. Defined.

Global Instance assume_val_eq_decision : EqDecision assume_val.
Proof. solve_decision. Defined.

Global Program Instance exp_eq_decision : EqDecision exp :=
  fix go e1 e2 :=
    match e1, e2 with
    | Val v1 a1, Val v2 a2 => cast_if_and (decide (v1 = v2)) (decide (a1 = a2))
    | Unop op1 e1 a1, Unop op2 e2 a2 => cast_if_and3 (decide (op1 = op2)) (go e1 e2) (decide (a1 = a2))
    | Binop op1 e1 e1' a1, Binop op2 e2 e2' a2 =>
        cast_if_and4 (decide (op1 = op2)) (go e1 e2) (go e1' e2') (decide (a1 = a2))
    | Manyop op1 x1 a1, Manyop op2 x2 a2 =>
        cast_if_and3 (decide (op1 = op2)) (decide (a1 = a2))
          ((fix inner l1 l2 : {l1 = l2} + {l1 ≠ l2} :=
           match l1, l2 with
           | [], [] => left _
           | x::l1',y::l2' =>
               cast_if_and (go x y) (inner l1' l2')
           | _, _ => right _
           end) x1 x2)
    | Ite e11 e21 e31 a1, Ite e12 e22 e32 a2 =>
        cast_if_and4 (go e11 e12) (go e21 e22) (go e31 e32) (decide (a1 = a2))
    | _, _ => right _
    end.
Solve Obligations with intros; destruct_all annot; naive_solver.

Global Program Instance a_exp_eq_decision : EqDecision a_exp :=
  fix go e1 e2 :=
    match e1, e2 with
    | AExp_Val v1 a1, AExp_Val v2 a2 => cast_if_and (decide (v1 = v2)) (decide (a1 = a2))
    | AExp_Unop op1 e1 a1, AExp_Unop op2 e2 a2 => cast_if_and3 (decide (op1 = op2)) (go e1 e2) (decide (a1 = a2))
    | AExp_Binop op1 e1 e1' a1, AExp_Binop op2 e2 e2' a2 =>
        cast_if_and4 (decide (op1 = op2)) (go e1 e2) (go e1' e2') (decide (a1 = a2))
    | AExp_Manyop op1 x1 a1, AExp_Manyop op2 x2 a2 =>
        cast_if_and3 (decide (op1 = op2)) (decide (a1 = a2))
          ((fix inner l1 l2 : {l1 = l2} + {l1 ≠ l2} :=
           match l1, l2 with
           | [], [] => left _
           | x::l1',y::l2' =>
               cast_if_and (go x y) (inner l1' l2')
           | _, _ => right _
           end) x1 x2)
    | AExp_Ite e11 e21 e31 a1, AExp_Ite e12 e22 e32 a2 =>
        cast_if_and4 (go e11 e12) (go e21 e22) (go e31 e32) (decide (a1 = a2))
    | _, _ => right _
    end.
Solve Obligations with intros; destruct_all annot; naive_solver.

Global Instance smt_eq_decision : EqDecision smt.
Proof. solve_decision. Defined.

Global Instance event_eq_decision : EqDecision event.
Proof. solve_decision. Defined.

Global Program Instance isla_trace_eq_decision : EqDecision isla_trace :=
  fix go t1 t2 :=
    match t1, t2 with
    | tnil, tnil => left _
    | tcons e1 ts1, tcons e2 ts2 => cast_if_and (decide (e1 = e2)) (go ts1 ts2)
    | tcases ts1, tcases ts2 =>
        (fix inner l1 l2 :=
           match l1, l2 with
           | [], [] => left _
           | x::l1',y::l2' =>
               cast_if_and (go x y) (inner l1' l2')
           | _, _ => right _
           end) ts1 ts2
    | _, _ => right _
    end.
Solve Obligations with intros; destruct_all annot; naive_solver.


Definition base_val_to_bool (v : base_val) : option bool :=
  match v with
  | Val_Bool b => Some b
  | _ => None
  end.

Definition val_to_bits (n : N) (v : valu) : option (bv n) :=
  match v with
  | RVal_Bits b => bvn_to_bv n b
  | _ => None
  end.

Lemma val_to_bits_Some n b v:
  val_to_bits n v = Some b ↔ v = RVal_Bits b.
Proof.
  split.
  - case v => //. case => //= vb /bvn_to_bv_Some ->. done.
  - move => -> /=. apply bvn_to_bv_to_bvn.
Qed.


(* TODO: Upstream these wrappers? *)
Definition get_state {S} `{!stateE S -< E} : itree E S :=
  trigger EGetState.

Definition set_state {S} `{!stateE S -< E} (s : S) : itree E unit :=
  trigger (ESetState s).

Lemma get_state_to_translate {E1 E2 S} (HE1 : stateE S -< E1) (HE2 : stateE S -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate get_state Hin get_state.
Proof. move => ?. rewrite /get_state. by apply trigger_to_translate. Qed.
Global Hint Resolve get_state_to_translate : itree_auto.
Lemma set_state_to_translate {E1 E2 S} s (HE1 : stateE S -< E1) (HE2 : stateE S -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (set_state s) Hin (set_state s).
Proof. move => ?. rewrite /set_state. by apply trigger_to_translate. Qed.
Global Hint Resolve set_state_to_translate : itree_auto.


Record seq_state := {
   seq_local : seq_local_state;
   seq_global : seq_global_state;
}.
Global Instance eta_seq_state : Settable _ := settable! Build_seq_state <seq_local; seq_global>.

Definition islaE : Type → Type := demonicE +' specE +' stateE seq_state +' stepE +' haltE +' ubE.
Global Hint Transparent islaE : itree_auto.


Definition read_reg {E} `{!stateE seq_state -< E} `{!ubE -< E} (r : string) (al : accessor_list) : itree E valu :=
  s ← get_state;
  v ← (s.(seq_local).(seq_regs) !! r)?;
  read_accessor al v?.

Lemma read_reg_to_translate {E1 E2} r al
  (HE1 : stateE seq_state -< E1) (HE2 : stateE seq_state -< E2)
  (Hub1 : ubE -< E1) (Hub2 : ubE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin Hub1 Hub2 →
  ITreeToTranslate (read_reg r al) Hin (read_reg r al).
Proof.
  move => ??. rewrite /read_reg.
  apply bind_to_translate; [by apply get_state_to_translate|]. move => ?.
  apply bind_to_translate; [by apply some_or_ub_to_translate|]. move => ?.
  by apply some_or_ub_to_translate.
Qed.
Global Hint Resolve read_reg_to_translate : itree_auto.


Definition write_reg {E} `{!stateE seq_state -< E} `{!ubE -< E} (r : string) (al : accessor_list) (v : valu) : itree E unit :=
  s ← get_state;
  vold ← (s.(seq_local).(seq_regs) !! r)?;
  vnew ← (write_accessor al vold v)?;
  set_state (s <|seq_local; seq_regs := <[r := vnew]> s.(seq_local).(seq_regs) |>).

Lemma write_reg_to_translate {E1 E2} r al v
  (HE1 : stateE seq_state -< E1) (HE2 : stateE seq_state -< E2)
  (Hub1 : ubE -< E1) (Hub2 : ubE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin Hub1 Hub2 →
  ITreeToTranslate (write_reg r al v) Hin (write_reg r al v).
Proof.
  move => ??. rewrite /write_reg.
  apply bind_to_translate; [by apply get_state_to_translate|]. move => ?.
  apply bind_to_translate; [by apply some_or_ub_to_translate|]. move => ?.
  apply bind_to_translate; [by apply some_or_ub_to_translate|]. move => ?.
  by apply set_state_to_translate.
Qed.
Global Hint Resolve write_reg_to_translate : itree_auto.

Definition read_mem_checked {E} `{!stateE seq_state -< E} `{!ubE -< E} (addr : bv 64) (len : N) : itree E (option bvn) :=
  s ← get_state;
  assert (0 < Z.of_N len);;
  if read_mem s.(seq_global).(seq_mem) (bv_unsigned addr) len is Some m then
    Ret (Some m)
  else
    assert (bv_unsigned addr + Z.of_N len ≤ 2 ^ 64);;
    assert (set_Forall (λ a, ¬ (bv_unsigned addr ≤ bv_unsigned a < bv_unsigned addr + Z.of_N len)) (dom s.(seq_global).(seq_mem)));;
    Ret None.

Lemma read_mem_checked_to_translate {E1 E2} addr len
  (HE1 : stateE seq_state -< E1) (HE2 : stateE seq_state -< E2)
  (Hub1 : ubE -< E1) (Hub2 : ubE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin Hub1 Hub2 →
  ITreeToTranslate (read_mem_checked addr len) Hin (read_mem_checked addr len).
Proof.
  move => ??. rewrite /read_mem_checked.
  apply bind_to_translate; [by apply get_state_to_translate|]. move => ?.
  apply bind_to_translate; [by apply assert_to_translate|]. move => ?.
  case_match.
  - by apply Ret_to_translate.
  - apply bind_to_translate; [by apply assert_to_translate|]. move => ?.
    apply bind_to_translate; [by apply assert_to_translate|]. move => ?.
    by apply Ret_to_translate.
Qed.
Global Hint Resolve read_mem_checked_to_translate : itree_auto.


Definition compile_trace' (t : isla_trace) :
  itree (callE isla_trace void +' islaE) void :=
  step.step;;
  match t with
  | Smt (DeclareConst x ty) ann :t: es =>
      v ← (match ty with
           | Ty_BitVec b =>
               n ← trigger (EDemonic Z);
               Hwf ← assume (BvWf b n);
               Ret (Val_Bits (@BV b n Hwf))
           | Ty_Bool =>
               b ← trigger (EDemonic bool);
               Ret (Val_Bool b)
           | Ty_Enum i =>
               c ← trigger (EDemonic _);
               Ret (Val_Enum c)
           | _ => ub
           end);
      call (subst_trace v x es)
  | Smt (DefineConst x e) ann :t: es =>
      v ← eval_exp e?;
      call (subst_trace v x es)
  | Smt (Assert e) ann :t: es =>
      v ← eval_exp e?;
      b ← base_val_to_bool v?;
      assume b;;
      call es
  | Assume e ann :t: es =>
      s ← get_state;
      v ← eval_a_exp s.(seq_local).(seq_regs) e?;
      b ← base_val_to_bool v?;
      assert b;;
      call es
  | AssumeReg r al v ann :t: es =>
      v' ← read_reg r al;
      assert (v' = v);;
      call es
  | ReadReg r al v ann :t: es =>
      v' ← read_reg r al;
      vread ← (read_accessor al v)?;
      assume (vread = v');;
      call es
  | WriteReg r al v ann :t: es =>
      vnew ← (read_accessor al v)?;
      write_reg r al vnew;;
      call es
  | ReadMem data kind addr len tag ann :t: es =>
      addr' ← (val_to_bits 64 addr)?;
      data' ← (val_to_bits (8 * len) data)?;
      res ← read_mem_checked addr' len;
      if res is Some databvn then
        data'' ← (bvn_to_bv (8 * len) databvn)?;
        assume (data' = data'');;
        call es
      else
        emit_label (SReadMem addr' data');;
        call es
  | WriteMem res kind addr data len tag ann :t: es =>
      addr' ← (val_to_bits 64 addr)?;
      data' ← (val_to_bits (8 * len) data)?;
      res ← read_mem_checked addr' len;
      if res is Some _ then
        s ← get_state;
        let mem' := write_mem len s.(seq_global).(seq_mem) addr' (bv_unsigned data') in
        set_state (s <|seq_global;seq_mem := mem'|>);;
        call es
      else
        emit_label (SWriteMem addr' data');;
        call es
  | tcases ts =>
      assert (ts ≠ []);;
      es ← trigger (EDemonic _);
      assume (es ∈ ts);;
      call es
  | tnil =>
      s ← get_state;
      vpc ← read_reg s.(seq_local).(seq_pc_reg) [];
      pc ← (val_to_bits 64 vpc)?;
      match s.(seq_global).(seq_instrs) !! pc with
      | Some es' => call es'
      | None => emit_label (SInstrTrap pc);; halt
      end
  | BranchAddress v ann :t: es => call es
  | Branch c desc ann :t: es => call es
  | Barrier v ann :t: es => call es
  | AbstractPrimop n v args ann :t: es => call es
  | _ => ub
  end.
Global Arguments compile_trace' !_ /.

Definition compile_trace : isla_trace → itree islaE void := rec compile_trace'.
Global Arguments compile_trace !_ /.

Definition compile_trace_direct_translation' (t : isla_trace) :
  itree (callE isla_trace void +' islaE) void :=
  step.step;;
  match t with
  | Smt (DeclareConst x (Ty_BitVec b)) ann :t: es =>
      n ← trigger (EDemonic Z);
      Hwf ← assume (BvWf b n);
      call (subst_trace (Val_Bits (@BV b n Hwf)) x es)
  | Smt (DeclareConst x Ty_Bool) ann :t: es =>
      b ← trigger (EDemonic bool);
      call (subst_trace (Val_Bool b) x es)
  | Smt (DeclareConst x (Ty_Enum i)) ann :t: es =>
      c ← trigger (EDemonic _);
      call (subst_trace (Val_Enum c) x es)
  | Smt (DefineConst x e) ann :t: es =>
      v ← eval_exp e?;
      call (subst_trace v x es)
  | Smt (Assert e) ann :t: es =>
      v ← eval_exp e?;
      b ← base_val_to_bool v?;
      assume b;;
      call es
  | Assume e ann :t: es =>
      s ← get_state;
      v ← eval_a_exp s.(seq_local).(seq_regs) e?;
      b ← base_val_to_bool v?;
      assert b;;
      call es
  | AssumeReg r al v ann :t: es =>
      s ← get_state;
      v' ← (s.(seq_local).(seq_regs) !! r)?;
      assert (read_accessor al v' = Some v);;
      call es
  | ReadReg r al v ann :t: es =>
      s ← get_state;
      v' ← (s.(seq_local).(seq_regs) !! r)?;
      v'' ← (read_accessor al v')?;
      vread ← (read_accessor al v)?;
      assume (vread = v'');;
      call es
  | WriteReg r al v ann :t: es =>
      s ← get_state;
      v' ← (s.(seq_local).(seq_regs) !! r)?;
      vnew ← (read_accessor al v)?;
      v'' ← (write_accessor al v' vnew)?;
      set_state (s <|seq_local; seq_regs := <[r := v'']> s.(seq_local).(seq_regs) |>);;
      call es
  | ReadMem data kind addr len tag ann :t: es =>
      s ← get_state;
      addr' ← (val_to_bits 64 addr)?;
      data' ← (val_to_bits (8 * len) data)?;
      assert (0 < Z.of_N len);;
      if read_mem s.(seq_global).(seq_mem) (bv_unsigned addr') len is Some _ then
        databvn ← (read_mem s.(seq_global).(seq_mem) (bv_unsigned addr') len)?;
        data'' ← (bvn_to_bv (8 * len) databvn)?;
        assume (data' = data'');;
        call es
      else
        assert (bv_unsigned addr' + Z.of_N len ≤ 2 ^ 64);;
        assert (set_Forall (λ a, ¬ (bv_unsigned addr' ≤ bv_unsigned a < bv_unsigned addr' + Z.of_N len)) (dom s.(seq_global).(seq_mem)));;
        emit_label (SReadMem addr' data');;
        call es
  | WriteMem res kind addr data len tag ann :t: es =>
      s ← get_state;
      addr' ← (val_to_bits 64 addr)?;
      data' ← (val_to_bits (8 * len) data)?;
      assert (0 < Z.of_N len);;
      if read_mem s.(seq_global).(seq_mem) (bv_unsigned addr') len is Some _ then
        let mem' := write_mem len s.(seq_global).(seq_mem) addr' (bv_unsigned data') in
        set_state (s <|seq_global;seq_mem := mem'|>);;
        call es
      else
        assert (bv_unsigned addr' + Z.of_N len ≤ 2 ^ 64);;
        assert (set_Forall (λ a, ¬ (bv_unsigned addr' ≤ bv_unsigned a < bv_unsigned addr' + Z.of_N len)) (dom s.(seq_global).(seq_mem)));;
        emit_label (SWriteMem addr' data');;
        call es
  | tcases ts =>
      assert (ts ≠ []);;
      es ← trigger (EDemonic _);
      assume (es ∈ ts);;
      call es
  | tnil =>
      s ← get_state;
      vpc ← (s.(seq_local).(seq_regs) !! s.(seq_local).(seq_pc_reg))?;
      pc ← (val_to_bits 64 vpc)?;
      match s.(seq_global).(seq_instrs) !! pc with
      | Some es' => call es'
      | None => emit_label (SInstrTrap pc);; halt
      end
  | BranchAddress v ann :t: es => call es
  | Branch c desc ann :t: es => call es
  | Barrier v ann :t: es => call es
  | AbstractPrimop n v args ann :t: es => call es
  | _ => ub
  end.
