From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.algebra Require Import dfrac_agree.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.itree Require Import itree exec handler wpi choice state step halt ub.
Require Import isla.adequacy.
Require Export isla.opsem.
Require Export isla.opsem_itree.
Require Import isla.spec_itree.
Require Import isla.lifting_itree.

Lemma step_singleton_inv Λ (e1 : expr Λ) σ1 κ ρ2 :
  step ([e1], σ1) κ ρ2 ↔ ∃ e2 σ2 efs,
      prim_step e1 σ1 κ e2 σ2 efs ∧ ρ2 = (e2 :: efs, σ2).
Proof.
  split.
  - inv 1. apply symmetry, app_singleton in H. naive_solver.
  - move => [?[?[?[??]]]]. simplify_eq/=.
    by apply: (step_atomic _ _ _ _ _ []).
Qed.

Definition islaEH Pκs : seHandler islaE :=
  (demonicEH ⊕ₑₛ specEH Pκs ⊕ₑₛ stateEH seq_state ⊕ₑₛ stepEH Later ⊕ₑₛ haltEH ⊕ₑₛ ubEH).

Local Notation isla_estate κs ls σ n := ((), (κs, ({| seq_local := ls; seq_global := σ |}, (n, ((), ()))))).


Lemma isla_exec_read_reg Pκs r al ls σ κs n C:
  (∀ v vr, seq_regs ls !! r = Some v → read_accessor al v = Some vr → C (Ret vr) (isla_estate κs ls σ n)) →
  exec (islaEH Pκs) (read_reg r al) (isla_estate κs ls σ n) C.
Proof.
  move => HC. rewrite /read_reg.
  exec_bind. apply: exec_trigger => /=.
  exec_bind. apply: exec_some_or_ub => /=??.
  exec_norm/=. apply: exec_some_or_ub => ??. naive_solver.
Qed.

Lemma isla_exec_not_stuck Pκs ls t κs σ n C :
  (∀ t' s',
     (∀ ls', ls'.(seq_trace) = t →
             ls'.(seq_regs) = ls.(seq_regs) →
             ls'.(seq_pc_reg) = ls.(seq_pc_reg) →
             not_stuck ls' σ) → C t' s') →
  exec (islaEH Pκs) (compile_trace t) (isla_estate κs ls σ (S n)) C.
Proof.
  move => HC.
  destruct ls as [????] => /=. destruct t as [|?|]; simplify_eq/=.
  - exec_bind. apply: exec_trigger => /=. eexists _. split; [done|].
    exec_bind. apply: exec_trigger => /=.
    exec_bind. apply: isla_exec_read_reg => /=. rewrite /read_accessor => ? vr ??.
    exec_bind. apply: exec_some_or_ub => pc /val_to_bits_Some?. simplify_option_eq.
    apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right.
    destruct (seq_instrs σ !! pc) eqn:?; repeat econstructor; simplify_eq/= => //; simplify_option_eq => //.
  - exec_bind. apply: exec_trigger => /=. eexists _. split; [done|].
    exec_norm/=. case_match.
    + case_match.
      * case_match.
        -- apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor.
        -- apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor.
        -- apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor.
        -- exec_bind. by apply: exec_vis.
      * exec_bind. apply: exec_some_or_ub => ??.
        apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
      * exec_bind. apply: exec_some_or_ub => b ?.
        exec_bind. apply: exec_some_or_ub => ??. destruct b => //; simplify_eq/=.
        apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
      * exec_norm/=. by apply: exec_vis.
    + apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
    + exec_bind. apply: isla_exec_read_reg => /= ????.
      exec_bind. apply: exec_some_or_ub => /= ??. simplify_eq/=.
      apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor; done.
    + exec_bind. apply: exec_some_or_ub => /= ??.
      rewrite /write_reg.
      exec_bind. apply: exec_trigger => /=.
      exec_bind. apply: exec_some_or_ub => /= ??.
      exec_bind. apply: exec_some_or_ub => /= ??.
      apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor; done.
    + exec_bind. apply: exec_some_or_ub => /= ? /val_to_bits_Some?.
      exec_bind. apply: exec_some_or_ub => /= ? /val_to_bits_Some?.
      rewrite /read_mem_checked. exec_bind. apply: exec_trigger => /=.
      exec_bind. apply: exec_assert => /= ?.
      case_match.
      * exec_bind. apply: exec_some_or_ub => /= ? /bvn_to_bv_Some?.
        apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
        simplify_option_eq. split_and! => //. by right.
      * exec_bind. apply: exec_assert => /= ?.
        exec_bind. apply: exec_assert => /= ?.
        apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
        by simplify_option_eq.
    + exec_bind. apply: exec_some_or_ub => /= ? /val_to_bits_Some?.
      exec_bind. apply: exec_some_or_ub => /= ? /val_to_bits_Some?.
      rewrite /read_mem_checked. exec_bind. apply: exec_trigger => /=.
      exec_bind. apply: exec_assert => /= ?.
      case_match.
      * exec_bind. apply: exec_trigger => /=.
        apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
        by simplify_option_eq.
      * exec_bind. apply: exec_assert => /= ?.
        exec_bind. apply: exec_assert => /= ?.
        apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
        by simplify_option_eq.
    + apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
    + apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_bind. apply: isla_exec_read_reg => ????.
      exec_bind. apply: exec_assert => ?. subst.
      apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
    + exec_bind. apply: exec_trigger => /=.
      exec_bind. apply: exec_some_or_ub => b ?.
      exec_bind. apply: exec_some_or_ub => b' ?.
      destruct b; simplify_eq/=.
      exec_bind. apply: exec_assert => ?. destruct b' => //.
      apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + exec_norm/=. by apply: exec_vis.
    + apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right. repeat econstructor => //.
  - exec_bind. apply: exec_trigger => /=. eexists _. split; [done|].
    exec_bind. apply: exec_assert => ?.
    apply exec_stop, HC => -[??? nb] ???; simplify_eq/=. destruct nb; [by left|]. right.
    destruct ts => //. repeat econstructor.
    Unshelve.
    { apply tnil. }
    { apply false. }
    { apply 0. }
    { apply bv_wf_in_range. pose proof (bv_modulus_pos nat5). lia. }
    { apply inhabitant. }
    { apply inhabitant. }
    { apply inhabitant. }
Qed.

Local Ltac rewrite_eq_Some :=
  repeat match goal with | H : ?x = Some ?y |- _ => rewrite H end.

Lemma nsteps_nb n ls gs κs t2 σ2 :
  nsteps n ([ls], gs) κs (t2, σ2) →
  ls.(seq_nb_state) = true →
  κs = [] ∧ t2 = [ls] ∧ σ2 = gs.
Proof.
  move => Hn ?. destruct ls; simplify_eq/=. inv Hn => //.
  revert select (step _ _ _) => /step_singleton_inv[?[? [? [Hs ?]]]].
  inv Hs.
Qed.

Lemma isla_exec_adequate_ind `{!Arch} n Pκs ls gs κs' κs t2 σ2 t ls':
  nsteps n ([ls], gs) κs (t2, σ2) →
  Pκs κs' →
  t = ls.(seq_trace) →
  ls.(seq_regs) = ls'.(seq_regs) →
  ls.(seq_pc_reg) = ls'.(seq_pc_reg) →
  exec (islaEH Pκs) (compile_trace t) (isla_estate κs' ls' gs (S n))
    (λ _ _, (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs (κs' ++ κs)).
Proof.
  elim: n ls ls' gs κs κs' t.
  - move => ls ????? Hs ? -> ??. inv Hs.
    apply isla_exec_not_stuck => ?? Hls. rewrite right_id_L. split; [|done].
    move => ? /list_elem_of_singleton ->. by apply Hls.
  - move => n IH ls ls' gs κs κs' ? Hs HPκs -> ??. destruct ls; simplify_eq/=.
    rewrite /compile_trace. exec_norm/=.
    exec_norm/=. inv Hs. revert select (step _ _ _) => /step_singleton_inv[?[? [? [Hs ?]]]].
    inv Hs; simplify_eq/=. rename select (trace_step _ _ _ _) into Hs.
    inv Hs; simplify_eq/=; destruct_and?; rewrite_eq_Some; simplify_eq/=; exec_norm/=.
    all: exec_bind; apply: exec_trigger => /=; eexists _; split; [done|].
    + exec_bind. apply: exec_trigger => /=. eexists _.
      exec_bind. apply: exec_assume => //=. move => ?.
      exec_norm/=. rewrite interp_recursive_call.
      eapply IH; [done|done| |done|done]. simpl. do 3 f_equal. by apply bv_eq.
    + exec_bind. apply: exec_trigger => /=. eexists _.
      exec_norm/=. rewrite interp_recursive_call. by eapply IH.
    + exec_bind. apply: exec_trigger => /=. eexists _.
      exec_norm/=. rewrite interp_recursive_call. by eapply IH.
    + exec_norm/=. rewrite interp_recursive_call. by eapply IH.
    + exec_norm/=. destruct b.
      * exec_bind. apply: exec_assume; [done|] => ?.
        exec_norm. rewrite -rec_as_interp. by eapply IH.
      * apply exec_stop. ogeneralize* nsteps_nb; [done..|] => -[-> [-> ->]].
        rewrite right_id_L. split; [|done] => ? /list_elem_of_singleton->.
        by repeat econstructor.
    + exec_bind. apply: exec_trigger => /=.
      exec_norm/=. rewrite_eq_Some.
      exec_bind. apply: exec_assert => ?.
      exec_norm/=. rewrite -rec_as_interp. by eapply IH.
    + exec_bind. apply: isla_exec_read_reg => /=????.
      revert select (∃ _, _) => -[??]. destruct_and!. simplify_eq/=.
      exec_bind. apply: exec_assert => ?. simplify_eq/=.
      exec_norm/=. rewrite -rec_as_interp. by eapply IH.
    + revert select (∃ _, _) => -[?[?[?[?[?[?[?[? Hor]]]]]]]]. simplify_eq/=.
      rewrite /read_reg. exec_bind. apply: exec_trigger => /=.
      exec_norm/=. rewrite_eq_Some.
      exec_norm/=. rewrite_eq_Some.
      exec_norm/=. destruct Hor as [[??]|?]; simplify_eq.
      * exec_bind. apply: exec_assume; [done|] => ?.
        exec_norm/=. rewrite -rec_as_interp. by eapply IH.
      * apply exec_stop. ogeneralize* nsteps_nb; [done..|] => -[-> [-> ->]].
        rewrite right_id_L. split; [|done] => ? /list_elem_of_singleton->.
        by repeat econstructor.
    + revert select (∃ _, _) => -[?[?[??]]]. destruct_and!. simplify_eq/=.
      rewrite /write_reg. rewrite_eq_Some.
      exec_bind. apply: exec_trigger => /=.
      exec_norm/=. rewrite_eq_Some.
      exec_norm/=. rewrite_eq_Some.
      exec_norm/=. rewrite_eq_Some.
      exec_bind. apply: exec_trigger => /=.
      exec_norm/=. rewrite -rec_as_interp. by eapply IH.
    + revert select (∃ _, _) => -[?[?[??]]]. destruct_and!. simplify_eq/=.
      exec_norm/=. rewrite bvn_to_bv_to_bvn.
      exec_norm/=. rewrite /read_mem_checked.
      exec_bind. apply: exec_trigger => /=.
      exec_bind. apply: exec_assert => /= ?.
      exec_norm/=. case_match; destruct_and!; simplify_eq/=.
      * exec_norm/=. rewrite bvn_to_bv_to_bvn.
        exec_norm/=. revert select (_ ∨ _) => -[[??]|?]; simplify_eq.
        -- exec_bind. apply: exec_assume => // ?.
           exec_norm/=. rewrite -rec_as_interp. by eapply IH.
        -- apply exec_stop. ogeneralize* nsteps_nb; [done..|] => -[-> [-> ->]].
           rewrite right_id_L. split; [|done] => ? /list_elem_of_singleton->.
           by repeat econstructor.
      * exec_bind. apply: exec_assert => /= ?.
        exec_bind. apply: exec_assert => /= ?.
        exec_bind. apply: exec_trigger => /= ?.
        exec_norm/=. rewrite -rec_as_interp.
        rewrite (cons_middle _ _ κs0) app_assoc. by eapply IH.
    + revert select (∃ _, _) => -[?[?[??]]]. destruct_and!. simplify_eq/=.
      exec_norm/=. rewrite bvn_to_bv_to_bvn.
      exec_norm/=. rewrite /read_mem_checked.
      exec_bind. apply: exec_trigger => /=.
      exec_bind. apply: exec_assert => /= ?.
      exec_norm/=. case_match; destruct_and!; simplify_eq/=.
      * exec_bind. apply: exec_trigger => /=.
        exec_bind. apply: exec_trigger => /=.
        exec_norm/=. rewrite -rec_as_interp. by eapply IH.
      * exec_bind. apply: exec_assert => /= ?.
        exec_bind. apply: exec_assert => /= ?.
        exec_bind. apply: exec_trigger => /= ?.
        exec_norm/=. rewrite -rec_as_interp.
        rewrite (cons_middle _ _ κs0) app_assoc. by eapply IH.
    + exec_norm/=. rewrite -rec_as_interp. by eapply IH.
    + exec_norm/=. rewrite -rec_as_interp. by eapply IH.
    + exec_norm/=. rewrite -rec_as_interp. by eapply IH.
    + exec_norm/=. rewrite -rec_as_interp. by eapply IH.
    + exec_bind. apply: exec_assert => /= ?.
      exec_bind. apply: exec_trigger => /=. eexists _.
      exec_bind. apply: exec_assume; [done|]. move => ?.
      exec_norm/=. rewrite interp_recursive_call. by eapply IH.
    + revert select (∃ _, _) => -[??]. destruct_and!. simplify_eq/=.
      exec_bind. apply: exec_trigger => /=.
      rewrite /read_reg.
      exec_bind. apply: exec_trigger => /=.
      exec_norm/=. rewrite_eq_Some.
      exec_norm/=. case_match; destruct_and!; simplify_eq/=.
      * exec_norm/=. rewrite interp_recursive_call. by eapply IH.
      * exec_bind. apply: exec_trigger => /= ?.
        apply exec_stop. ogeneralize* nsteps_nb; [done..|] => -[-> [-> ->]].
        split; [|done] => ? /list_elem_of_singleton->.
        by repeat econstructor.
Qed.

Lemma isla_exec_adequate `{!Arch} n Pκs regs instrs mem κs t2 σ2 :
  nsteps n ([initial_local_state regs], {| seq_instrs := instrs; seq_mem := mem |}) κs (t2, σ2) →
  Pκs [] →
  exec (islaEH Pκs) (compile_trace (initial_local_state regs).(seq_trace))
       (isla_estate [] (initial_local_state regs) {| seq_instrs := instrs; seq_mem := mem |} (S n))
    (λ _ _, (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs).
Proof. move => ??. by apply: isla_exec_adequate_ind. Qed.

Lemma isla_adequacy Σ `{!Arch} `{!islaPreG Σ} `{!statePreG Σ} (instrs : gmap addr isla_trace) (mem : mem_map) (regs : reg_map) (Pκs : spec) t2 σ2 κs n:
  Pκs [] →
  (∀ {HG : islaG Σ} {HS : stateG Σ},
    ⊢ instr_table instrs -∗ backed_mem (dom mem) -∗ spec_trace Pκs -∗ ([∗ map] a↦b∈mem, bv_unsigned a ↦ₘ b)
    ={⊤}=∗ ∀ (_ : threadG), ([∗ map] r↦v∈regs, r ↦ᵣ v) -∗ WPasm tnil) →
  nsteps n ([initial_local_state regs], {| seq_instrs := instrs; seq_mem := mem |}) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs.
Proof.
  move => ? Hwp Hnsteps.
  apply: (wpi_adequate_pure HasLc (S n)). { by apply isla_exec_adequate. }
  iIntros (?) "Hlater".
  set i := to_instrtbl instrs.
  set bm := to_backed_mem (dom mem).
  iMod (own_alloc (i)) as (γi) "#Hi" => //.
  iMod (own_alloc (bm)) as (γbm) "#Hb" => //.
  iMod (own_alloc (to_frac_agree (A:= _ -d> _) (1/2 + 1/2) Pκs)) as (γs) "Hs" => //.
  rewrite frac_agree_op. iDestruct "Hs" as "[Hs1 Hs2]".
  iMod (ghost_map_alloc mem) as (γm) "[Hm1 Hm2]".

  set (HheapG := HeapG _ _ γi _ _ _ γm _ γbm κs Pκs _ γs).
  set (HislaG := IslaG _ _ HheapG).
  iAssert (instr_table instrs) as "#His". { by rewrite instr_table_eq. }
  iAssert (backed_mem (dom mem)) as "#Hbm". { by rewrite backed_mem_eq. }

  iMod (ghost_var_alloc (_ : seq_state)) as (γl) "[Hl1 Hl2]".
  set (HstateG := StateG _ _ γl).

  iMod (Hwp HislaG HstateG with "His Hbm [Hs1] [Hm2]") as "Hwp". {
    rewrite spec_trace_eq. iExists _. rewrite spec_trace_raw_eq. by iFrame.
  } {
    iApply (big_sepM_impl with "Hm2"). iIntros "!>" (a b ?) "Ha".
    iApply mem_mapsto_byte_to_mapsto. rewrite mem_mapsto_byte_eq.
    iExists _. iFrame. by rewrite Z_to_bv_checked_bv_unsigned.
  }

  iExists islaH, _, _ => /=. iFrame.
  rewrite /state.state_interp/=/isla_state_interp state_link_eq. iFrame.

  iMod (ghost_map_alloc (regs)) as (γr) "[Hr1 Hr2]".
  iMod (ghost_map_alloc (∅ : gmap (string * string) valu)) as (γsr) "[Hsr1 _]".
  set (HthreadG := ThreadG γr γsr).
  iSpecialize ("Hwp" with "[Hr2]"). {
    iApply (big_sepM_impl with "Hr2").
    iIntros "!>" (???) "?". by rewrite reg_mapsto_eq.
  }
  rewrite wp_asm_unfold.
  iDestruct ("Hwp" with "[%] [Hl1] [Hr1 Hsr1] [] [Hm1]") as "Hwp".
  2: { by rewrite state_link_eq. } { done. }
  { iFrame. iPureIntro. split_and! => //.
    * move => /=. naive_solver.
    * move => ?? [?[??]]. simplify_map_eq. }
  { iFrame "His". } { iFrame "Hbm Hm1". }

  iFrame "Hwp". iModIntro. iSplitL "Hs2".
  - repeat iSplit => //. iExists _. rewrite spec_trace_raw_eq. by iFrame.
  - iIntros (?????) "_ _ !>". done.
Qed.
