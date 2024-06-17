From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi choice ub state handler itree halt later.
Require Export isla.opsem.
Require Import isla.spec_itree.

Global Hint Transparent sail_name accessor_list : itree_auto.


  Lemma bvn_to_bv_to_bvn n (b : bv n) :
    bvn_to_bv n b = Some b.
  Proof.
    rewrite /bvn_to_bv. case_decide as Heq => //. destruct (bv_to_bvn b) eqn:Heq2.
    by simplify_K.
  Qed.


Global Instance base_val_eq_decision : EqDecision base_val.
Proof. solve_decision. Qed.

Global Instance valu_eq_decision : EqDecision valu.
Proof.
  unfold EqDecision; intros.
  unfold Decision.
decide equality.
all: try solve_trivial_decision.
1: decide equality.
Admitted.

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

Global Instance exp_eq_decision : EqDecision exp.
Proof.
  unfold EqDecision; intros.
  unfold Decision.
decide equality.
all: try solve_trivial_decision.
1: decide equality.
Admitted.

Global Instance a_exp_eq_decision : EqDecision a_exp.
Proof.
  unfold EqDecision; intros.
  unfold Decision.
decide equality.
all: try solve_trivial_decision.
1: decide equality.
Admitted.

Global Instance smt_eq_decision : EqDecision smt.
Proof. solve_decision. Defined.

Global Instance event_eq_decision : EqDecision event.
Proof. solve_decision. Defined.

Global Instance isla_trace_eq_decision : EqDecision isla_trace.
Proof.
  unfold EqDecision; intros.
  unfold Decision.
decide equality.
all: try solve_trivial_decision.
1: decide equality.
Admitted.


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

Lemma bvn_to_bv_Some n bn b:
  bvn_to_bv n bn = Some b ↔ bn = bv_to_bvn b.
Proof.
  rewrite /bvn_to_bv.
  case_decide as Heq => //.
  - destruct Heq, bn. naive_solver.
  - destruct bn. naive_solver.
Qed.

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

Definition islaE : Type → Type := demonicE +' specE +' stateE seq_state +' laterE +' haltE +' ubE.
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
  later.step;;
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
  later.step;;
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
