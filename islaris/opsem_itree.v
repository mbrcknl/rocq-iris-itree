From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.itree Require Import wpi choice ub state handler itree.
Require Export isla.opsem.

(* TODO: It would be very nice to have demonic without sideconditions in decidability. *)
Program Definition demonic {E} `{demonicE -< E} (A : Type) : itree E A :=
  trigger (@EDemonic A _ _).
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition nb {E} `{demonicE -< E} {R} : itree E R :=
  a ← demonic void; match a with end.

(* TODO: It would be very nice to have this assert without sideconditions on decidability. *)
Program Definition assert {E} `{!ubE -< E} (P : Prop) : itree E unit :=
  if @bool_decide P _ then ub else Ret ().
Next Obligation. Admitted.

(* TODO: switch to nbE and decision *)
Definition assume {E} `{!demonicE -< E} (P : Prop) : itree E P :=
  demonic P.

(* TODO: define in terms of state? use a definition of wpi_translation *)
Variant visibleE (EV : Type) : Type → Type :=
  | EVisible (e : EV) : visibleE EV unit.

Definition visible {EV} `{!visibleE EV -< E} (e : EV) : itree E unit :=
  trigger (EVisible _ e).

(* TODO: Upstream these wrappers? *)
Definition get_state {S} `{!stateE S -< E} : itree E S :=
  trigger EGetState.

Definition set_state {S} `{!stateE S -< E} (s : S) : itree E unit :=
  trigger (ESetState s).

Definition some_or_nb {E R} `{!demonicE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => nb end)%itree.
Notation "x !" := (some_or_nb x) (at level 10, format "x !") : itree_scope.

Record seq_state := {
   seq_local : seq_local_state;
   seq_global : seq_global_state;
}.
Global Instance eta_seq_state : Settable _ := settable! Build_seq_state <seq_local; seq_global>.

Definition islarisE : Type → Type := demonicE +' visibleE seq_label +' stateE seq_state +' ubE.

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

Definition compile_trace' (t : isla_trace) :
  itree (callE isla_trace void +' islarisE) void :=
  match t with
  | Smt (DeclareConst x (Ty_BitVec b)) ann :t: es =>
      n ← demonic Z;
      Hwf ← assume (BvWf b n);
      call (subst_trace (Val_Bits (@BV b n Hwf)) x es)
  | Smt (DeclareConst x Ty_Bool) ann :t: es =>
      b ← demonic bool;
      call (subst_trace (Val_Bool b) x es)
  | Smt (DeclareConst x (Ty_Enum i)) ann :t: es =>
      c ← demonic _;
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
        visible (SReadMem addr' data');;
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
        visible (SWriteMem addr' data');;
        call es
  | tcases ts =>
      assert (ts ≠ []);;
      es ← demonic _;
      assume (es ∈ ts);;
      call es
  | tnil =>
      s ← get_state;
      vpc ← (s.(seq_local).(seq_regs) !! s.(seq_local).(seq_pc_reg))?;
      pc ← (val_to_bits 64 vpc)?;
      match s.(seq_global).(seq_instrs) !! pc with
      | Some es' => call es'
      | None => visible (SInstrTrap pc);; nb
      end
  | BranchAddress v ann :t: es => call es
  | Branch c desc ann :t: es => call es
  | Barrier v ann :t: es => call es
  | AbstractPrimop n v args ann :t: es => call es
  | _ => ub
  end.

Definition compile_trace : isla_trace → itree islarisE void := rec compile_trace'.
