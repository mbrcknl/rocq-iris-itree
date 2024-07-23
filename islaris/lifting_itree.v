(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

From ITree Require Import ITree Recursion RecursionFacts InterpFacts Eqit.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import tactics.
From iris.itree Require Import wpi choice ub state handler itree halt step.
From isla Require Export lifting opsem_itree ghost_state spec_itree.
Set Default Proof Using "Type".
Import uPred.

Class stateG Σ := StateG {
  state_link_inG :: ghost_varG Σ seq_state;
  state_link_name : gname;
}.

Class statePreG Σ := PreStateG {
  state_pre_link_inG :: ghost_varG Σ seq_state;
}.

Definition stateΣ : gFunctors :=
  #[ghost_varΣ seq_state].

Global Instance subG_statePreG {Σ} : subG stateΣ Σ → statePreG Σ.
Proof. solve_inG. Qed.

Section state_link.
  Context `{!stateG Σ}.

  Definition state_link_def (σ: seq_state) : iProp Σ :=
    ghost_var state_link_name (1/2) σ.
  Definition state_link_aux : seal (@state_link_def). by eexists. Qed.
  Definition state_link := unseal state_link_aux.
  Definition state_link_eq : @state_link = @state_link_def :=
    seal_eq state_link_aux.

  Lemma state_link_agree σ1 σ2 :
    state_link σ1 -∗ state_link σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    rewrite state_link_eq. iIntros "Ht1 Ht2".
    by iCombine "Ht1 Ht2" as "H" gives %[? ->].
  Qed.

  Lemma state_link_update σ σ1 σ2 :
    state_link σ1 -∗ state_link σ2 ==∗ state_link σ ∗ state_link σ.
  Proof. rewrite state_link_eq. apply ghost_var_update_halves. Qed.
End state_link.

Global Instance isla_state_interp `{!stateG Σ} : stateInterp Σ seq_state := state_link.

Definition islaH {Σ} `{!stateG Σ} `{!islaG Σ}  : iHandler Σ islaE :=
  demonicH ⊕ specH ⊕ stateH seq_state ⊕ stepH Later ⊕ haltH ⊕ ubH.

Definition wp_asm_def `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} (e : isla_trace) : iProp Σ :=
  (∀ σ,
      ⌜σ.(seq_local).(seq_pc_reg) = arch_pc_reg⌝ -∗
      state_link σ -∗
      thread_ctx σ.(seq_local).(seq_regs) -∗
      instr_ctx σ.(seq_global).(seq_instrs) -∗
      mem_ctx σ.(seq_global).(seq_mem) -∗
      WPi compile_trace e @ islaH;⊤ {{ _, True }})%I.
Definition wp_asm_aux `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : seal (@wp_asm_def _ Σ _ _ _). by eexists. Qed.
Definition wp_asm `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : isla_trace → iProp Σ := (wp_asm_aux).(unseal).
Definition wp_asm_eq `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : wp_asm = @wp_asm_def _ Σ _ _ _ := (wp_asm_aux).(seal_eq).

Notation WPasm := wp_asm.

Definition wp_event_def `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} (e : event) (Φ : iProp Σ) : iProp Σ :=
  ∀ t, (Φ -∗ WPasm t) -∗ WPasm (e:t:t).
Definition wp_event_aux `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : seal (@wp_event_def _ _ _ _ _). by eexists. Qed.
Definition wp_event `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : event → iProp Σ → iProp Σ := (wp_event_aux).(unseal).
Definition wp_event_eq `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : wp_event = @wp_event_def _ _ _ _ _ := (wp_event_aux).(seal_eq).

(* We override the WPevent notation from lifting.v. We also make it a
local notation such that the warning is not triggered when this file
is imported. *)
Local Set Warnings "-notation-overridden".
Local Notation "'WPevent' e {{ Φ } }" := (wp_event e Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WPevent'  e  '/' '[   ' {{  Φ  } } ']' ']'") : bi_scope.
Local Set Warnings "notation-overridden".

Definition instr_pre'_def `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} (is_later : bool) (a : Z) (P : iProp Σ) : iProp Σ :=
  ▷?is_later (
  P -∗
  ∃ ins,
    instr (bv_wrap 64 a) ins ∗
    match ins with
    | Some t => arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 a) -∗ WPasm t
    | None => ∃ Pκs, ⌜Pκs [SInstrTrap (Z_to_bv 64 a)]⌝ ∗ spec_trace Pκs
    end
   ).
Definition instr_pre'_aux `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : seal (@instr_pre'_def _ Σ _ _ _). by eexists. Qed.
Definition instr_pre' `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : bool → Z → iProp Σ → iProp Σ := (instr_pre'_aux).(unseal).
Definition instr_pre'_eq `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG} : instr_pre' = @instr_pre'_def _ Σ _ _ _ := (instr_pre'_aux).(seal_eq).

Notation instr_pre := (instr_pre' true).
Notation instr_body := (instr_pre' false).

Section lifting.
  Context `{!Arch} `{!islaG Σ} `{!stateG Σ} `{!threadG}.

  (** * Unfolding *)
  Lemma wp_asm_unfold e :
    WPasm e ⊣⊢ wp_asm_def e.
  Proof. by rewrite wp_asm_eq. Qed.
  Lemma wp_event_unfold e Φ:
    WPevent e {{ Φ }} ⊣⊢ wp_event_def e Φ.
  Proof. by rewrite wp_event_eq. Qed.

  (** * Proof mode instances *)
  Global Instance elim_modal_bupd_wp_asm p P es :
    ElimModal True p false (|==> P) P (WPasm es) (WPasm es).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd ⊤) fupd_frame_r bi.wand_elim_r.
    rewrite wp_asm_eq.
    iIntros "_ Hs" (??) "????". iApply wpi_update.
    by iApply ("Hs" with "[//] [$] [$] [$] [$]").
  Qed.

  Global Instance elim_modal_fupd_wp_asm p P es :
    ElimModal True p false (|={⊤}=> P) P (WPasm es) (WPasm es).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r.
    rewrite wp_asm_eq.
    iIntros "_ Hs" (??) "????". iApply wpi_update.
    by iApply ("Hs" with "[//] [$] [$] [$] [$]").
  Qed.

  Global Instance is_except_0_wp_asm es:
    IsExcept0 (WPasm es).
  Proof.
    rewrite /IsExcept0. iIntros "Hwp".
    iAssert (|={⊤}=> WPasm es)%I with "[Hwp]" as ">$".
    by iMod "Hwp" as "$".
  Qed.

  (** * General lemmas *)
  Lemma wp_asm_thread_ctx es :
    (∀ regs, thread_ctx regs ={⊤}=∗ thread_ctx regs ∗ WPasm es) -∗
    WPasm es.
  Proof.
    rewrite wp_asm_eq.
    iIntros "HWP" (??) "? Hregs ??". iApply wpi_update. iMod ("HWP" with "Hregs") as "[? HWP]".
    iModIntro. iApply ("HWP" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_event_intro e Φ:
    (∀ t, (Φ -∗ WPasm t) -∗ WPasm (e:t:t)) -∗
    WPevent e {{ Φ }}.
  Proof. rewrite wp_event_eq. iIntros "?". done. Qed.

  Lemma wp_event_elim e t Φ:
    WPevent e {{ Φ }} -∗
    (Φ -∗ WPasm t) -∗
    WPasm (e:t:t).
  Proof. rewrite wp_event_eq. iIntros "Hwp HΦ". by iApply "Hwp". Qed.

  Lemma wp_event_mono e Φ Φ':
    WPevent e {{ Φ }} -∗
    (Φ -∗ Φ') -∗
    WPevent e {{ Φ' }}.
  Proof.
    rewrite wp_event_eq. iIntros "Hwp HΦ" (t) "HΦ'".
    iApply "Hwp". iIntros "?". iApply "HΦ'". by iApply "HΦ".
  Qed.

  Lemma wp_readreg_mono r al Φ' Φ :
    WPreadreg r @ al {{ Φ }} -∗
    (∀ v, Φ v -∗ Φ' v) -∗
    WPreadreg r @ al {{ Φ' }}.
  Proof.
    rewrite wpreadreg_eq. iIntros "Hr HΦ" (?) "?".
    iDestruct ("Hr" with "[$]") as (????) "[$ ?]".
    iExists _, _. do 2 (iSplit; [done|]). by iApply "HΦ".
  Qed.

  (** * Helper function (new)  *)
  Lemma wpi_get_state_isla σ Φ :
    state_link σ -∗
    (state_link σ -∗ Φ σ) -∗
    WPi get_state @ islaH;⊤ {{Φ}}.
  Proof.
    iIntros "Hσ HΦ". rewrite /get_state. iApply @wpi_get.
    iIntros (?) "Hs !>". iDestruct (state_link_agree with "[$] [$]") as %->.
    iFrame. iApply wpi_ret. by iApply "HΦ".
  Qed.

  Lemma wpi_set_state_isla σ σ' Φ :
    state_link σ -∗
    (state_link σ' -∗ Φ tt) -∗
    WPi set_state σ' @ islaH;⊤ {{Φ}}.
  Proof.
    iIntros "Hσ HΦ". rewrite /set_state. iApply @wpi_set.
    iIntros (?) "Hs". iMod (state_link_update with "[$] [$]") as "[$ ?]". iModIntro.
    iApply wpi_ret. by iApply "HΦ".
  Qed.

  Lemma wpi_read_reg r al σ Φ :
    state_link σ -∗
    regs_ctx σ.(seq_local).(seq_regs) -∗
    WPreadreg r @ al {{ v, state_link σ -∗ regs_ctx σ.(seq_local).(seq_regs) -∗ Φ v }} -∗
    WPi read_reg r al @ islaH;⊤ {{Φ}}.
  Proof.
    rewrite wpreadreg_eq /read_reg. iIntros "Hσ Hregs Hread".
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "Hσ".
    iDestruct ("Hread" with "Hregs") as (?? -> Heq) "[? HΦ]". wpi_norm/=. rewrite Heq /=.
    iApply wpi_ret. iApply ("HΦ" with "[$] [$]").
  Qed.

  Lemma wpi_write_reg r al σ Φ v vold vnew :
    seq_regs (seq_local σ) !! r = Some vold →
    write_accessor al vold v = Some vnew →
    state_link σ -∗
    (state_link (σ <| seq_local; seq_regs := <[r:=vnew]> (seq_regs (seq_local σ)) |>) -∗ Φ tt) -∗
    WPi write_reg r al v @ islaH;⊤ {{Φ}}.
  Proof.
    iIntros (Hold Hnew) "Hσ Hcont".
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "Hσ".
    rewrite Hold. wpi_norm/=. rewrite Hnew. wpi_norm/=. by iApply (wpi_set_state_isla with "[$]").
  Qed.

  (** * Next instruction & instr_pre'  *)
  Lemma wp_next_instr (PC : bv 64) ins :
    arch_pc_reg ↦ᵣ RVal_Bits PC -∗
    instr (bv_unsigned PC) (Some ins) -∗
    ▷ (arch_pc_reg ↦ᵣ RVal_Bits PC -∗ WPasm ins) -∗
    WPasm tnil.
  Proof.
    iIntros "HPC Hi Hcont". setoid_rewrite wp_asm_unfold. iIntros (? Hpc) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro. rewrite -Hpc.
    iApply wpi_bind. iApply (@wpi_get_state_isla with "[$]"). iIntros "?".
    iApply wpi_bind. iApply (@wpi_read_reg with "[$] [$]").
    iApply (read_reg_nil with "[$]"). iIntros "???/=". wpi_norm/=.
    iDestruct (instr_lookup_unsigned with "[$] [$]") as %->.
    wpi_norm. rewrite interp_recursive_call.
    by iApply ("Hcont" with "[$] [//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_next_instr_extern (PC : bv 64) (Pκs : spec):
    Pκs [SInstrTrap PC] →
    arch_pc_reg ↦ᵣ RVal_Bits PC -∗
    instr (bv_unsigned PC) None -∗
    ▷ spec_trace Pκs -∗
    WPasm tnil.
  Proof.
    iIntros (?) "HPC Hi Hspec". setoid_rewrite wp_asm_unfold. iIntros (? Hpc) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro. rewrite -Hpc.
    iApply wpi_bind. iApply (@wpi_get_state_isla with "[$]"). iIntros "?".
    iApply wpi_bind. iApply (@wpi_read_reg with "[$] [$]").
    iApply (read_reg_nil with "[$]"). iIntros "???/=". wpi_norm/=.
    iDestruct (instr_lookup_unsigned with "[$] [$]") as %->.
    wpi_norm. iApply wpi_bind. iApply (@wpi_emit_label with "[$]"); [done|]. iIntros "?".
    by iApply @wpi_halt.
  Qed.

  Lemma wp_next_instr_pre (PC : bv 64) P l:
    arch_pc_reg ↦ᵣ RVal_Bits PC -∗
    instr_pre' l (bv_unsigned PC) P -∗
    P -∗
    WPasm tnil.
  Proof.
    rewrite instr_pre'_eq. iIntros "HPC Hpre HP".
    iDestruct ("Hpre" with "[$HP]") as (ins) "(>Hinstr & Hwp)".
    rewrite bv_wrap_small; [| by apply bv_unsigned_in_range].
    iDestruct (laterN_le _ 1 with "Hwp") as "Hwp". { destruct l => /=; lia. }
    destruct ins; rewrite Z_to_bv_bv_unsigned.
    - by iApply (wp_next_instr with "HPC Hinstr"); [done..|].
    - iDestruct "Hwp" as (?) "[>% Hwp]".
      by iApply (wp_next_instr_extern with "[$] [$] [$]").
  Qed.

  Lemma instr_pre_wand a1 a2 l1 l2 P Q:
    implb l1 l2 →
    bv_wrap 64 a1 = bv_wrap 64 a2 →
    instr_pre' l1 a1 P -∗
    (Q -∗ P) -∗
    instr_pre' l2 a2 Q.
  Proof.
    rewrite instr_pre'_eq => Himpl Ha.
    iIntros "Hinstr Hwand".
    iApply (laterN_le (Nat.b2n l1)). { destruct l1, l2 => //=. lia. }
    iIntros "!> HQ".
    rewrite Ha. have -> : Z_to_bv 64 a1 = Z_to_bv 64 a2 by apply bv_eq.
    iApply ("Hinstr" with "[HQ Hwand]"). by iApply "Hwand".
  Qed.

  Lemma instr_pre_to_body a P:
    ▷ instr_body a P -∗
    instr_pre a P.
  Proof. rewrite instr_pre'_eq. iIntros "?". done. Qed.

  Lemma instr_pre_intro_Some l P ins a:
    instr a (Some ins) -∗
    (P -∗ arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 a) -∗ WPasm ins) -∗
    instr_pre' l a P.
  Proof.
    rewrite instr_pre'_eq.
    iIntros "Hinstr Hwp !> HP".
    iDestruct (instr_addr_in_range with "Hinstr") as %?.
    iExists _. rewrite bv_wrap_small; [|done]. iFrame.
    iIntros "HPC". iApply ("Hwp" with "[$] [$]").
  Qed.

  Lemma instr_pre_intro_None P a l:
    instr a None -∗
    (P -∗ ∃ Pκs, ⌜Pκs [SInstrTrap (Z_to_bv 64 a)]⌝ ∗ spec_trace Pκs) -∗
    instr_pre' l a P.
  Proof.
    rewrite instr_pre'_eq.
    iIntros "Hinstr Hspec !> HP".
    iDestruct (instr_addr_in_range with "Hinstr") as %?.
    iDestruct ("Hspec" with "HP") as (??) "Hspec".
    iExists _. rewrite bv_wrap_small; [|done]. iFrame. iExists _. by iFrame.
  Qed.

  (** * Case distinction  *)
  Lemma wp_cases ts:
    ts ≠ [] →
    (∀ t, ⌜t ∈ ts⌝ -∗ WPasm t) -∗
    WPasm (tcases ts).
  Proof.
    iIntros (?) "Hwp". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    iApply wpi_bind. iApply wpi_assert; [done|].
    iApply wpi_bind. iApply @wpi_demonic_trigger. iIntros (?).
    iApply wpi_bind. iApply @wpi_assume. iIntros (?).
    rewrite interp_recursive_call. by iApply ("Hwp" with "[//] [//] [$] [$] [$] [$]").
  Qed.

  (** * Registers  *)
  Lemma wp_read_reg r v vread ann es al:
    read_accessor al v = Some vread →
    WPreadreg r @ al {{ v', ⌜vread = v'⌝ -∗ WPasm es }} -∗
    WPasm (ReadReg r al v ann :t: es).
  Proof.
    iIntros (Heq) "Hread". setoid_rewrite wp_asm_unfold at 2. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro. rewrite Heq.
    iApply wpi_bind. iApply (wpi_read_reg with "[$] [$]").
    iApply (wp_readreg_mono with "Hread"). iIntros (?) "Hwp ??/=". wpi_norm/=.
    iApply wpi_bind. iApply @wpi_assume. iIntros (?).
    rewrite interp_recursive_call. rewrite wp_asm_unfold.
    by iApply ("Hwp" with "[//] [//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_assume_reg r v ann es al:
    WPreadreg r @ al {{ v', ⌜v = v'⌝ ∗ WPasm es }} -∗
    WPasm (AssumeReg r al v ann :t: es).
  Proof.
    iIntros "Hread". setoid_rewrite wp_asm_unfold at 2. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    iApply wpi_bind. iApply (wpi_read_reg with "[$] [$]").
    iApply (wp_readreg_mono with "Hread"). iIntros (?) "[% Hwp] ??/=". wpi_norm/=.
    iApply wpi_bind. iApply @wpi_assert; [done|].
    rewrite interp_recursive_call. rewrite wp_asm_unfold.
    by iApply ("Hwp" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_write_reg_acc r v v' v'' vnew ann es al:
    read_accessor al v = Some vnew →
    write_accessor al v' vnew = Some v'' →
    r ↦ᵣ v' -∗
    (r ↦ᵣ v'' -∗ WPasm es) -∗
    WPasm (WriteReg r al v ann :t: es).
  Proof.
    iIntros (Hread Hwrite) "Hr Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro. rewrite Hread/=.
    iDestruct (reg_mapsto_lookup with "[$] Hr") as %?.
    wpi_norm/=. iApply wpi_bind. iApply (wpi_write_reg with "[$]"); [done..|]. iIntros "?".
    iApply wpi_update. iMod (reg_mapsto_update with "[$] Hr") as "[? Hr]"; [done..|]. iModIntro.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[$] [%] [$] [$] [$] [$]").
  Qed.

  Lemma wp_write_reg_struct r v v' vnew ann es f:
    read_accessor [Field f] v = Some vnew →
    r # f ↦ᵣ v' -∗
    (r # f ↦ᵣ vnew -∗ WPasm es) -∗
    WPasm (WriteReg r [Field f] v ann :t: es).
  Proof.
    iIntros (Hread) "Hr Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro. rewrite Hread/=.
    iDestruct (struct_reg_mapsto_lookup with "[$] Hr") as %(?&?&?&?&?).
    wpi_norm/=. iApply wpi_bind. iApply (wpi_write_reg with "[$]"); [done| |].
    { rewrite /write_accessor/=. by simplify_option_eq. } iIntros "?".
    iApply wpi_update. iMod (struct_reg_mapsto_update with "[$] Hr") as "[? Hr]"; [done..|]. iModIntro.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[$] [%] [$] [$] [$] [$]").
  Qed.

  Lemma wp_write_reg r v v' ann es:
    r ↦ᵣ v' -∗
    (r ↦ᵣ v -∗ WPasm es) -∗
    WPasm (WriteReg r [] v ann :t: es).
  Proof. by apply: wp_write_reg_acc. Qed.

  (** * Memory  *)
  Lemma wp_read_mem n len a vread (vmem : bv n) es ann kind tag q:
    n = (8 * len)%N →
    0 < Z.of_N len →
    bv_unsigned a ↦ₘ{q} vmem -∗
    (⌜vread = vmem⌝ -∗ bv_unsigned a ↦ₘ{q} vmem -∗ WPasm es) -∗
    WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iIntros (??) "Hm Hcont". setoid_rewrite wp_asm_unfold. subst. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite bvn_to_bv_to_bvn/=/read_mem_checked. wpi_norm/=.
    iDestruct (mem_mapsto_lookup with "[$] Hm") as %[len' [? Heq]].
    have ? : len' = len by lia. subst.
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "?".
    iApply wpi_bind. iApply wpi_assert; [done|]. rewrite Heq. wpi_norm/=.
    rewrite bvn_to_bv_to_bvn/=. wpi_norm/=.
    iApply wpi_bind. iApply @wpi_assume. iIntros (?).
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [%] [$] [$] [$] [$]").
  Qed.

  Lemma wp_read_mem_array n len a a' vread vmem (i : nat) (l : list (bv n)) es ann kind tag q:
    n = (8 * len)%N →
    0 < Z.of_N len →
    l !! i = Some vmem →
    a' = bv_unsigned a - (i * Z.of_N len) →
    a' ↦ₘ{q}∗ l -∗
    (⌜vread = vmem⌝ -∗ a' ↦ₘ{q}∗ l -∗ WPasm es) -∗
    WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iIntros (??? ->) "Hm Hcont".
    iDestruct (mem_mapsto_array_lookup_acc with "Hm") as "[Hv Hm]"; [done..|].
    rewrite Z.sub_add. iApply (wp_read_mem with "Hv"); [lia..|].
    iIntros (?) "Hl". iApply ("Hcont" with "[//]"). by iApply "Hm".
  Qed.

  Lemma wp_read_mmio n len a (vread : bv _) es ann kind tag (Pκs : spec):
    n = (8 * len)%N →
    0 < Z.of_N len →
    Pκs [SReadMem a vread] →
    mmio_range (bv_unsigned a) (Z.of_N len) -∗
    spec_trace Pκs -∗
    (spec_trace (λ κs, Pκs (SReadMem a vread::κs)) -∗ WPasm es) -∗
    WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iIntros (???) "Hm Hspec Hcont". setoid_rewrite wp_asm_unfold. subst. iIntros (? ?) "??? Hmem".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite bvn_to_bv_to_bvn/=/read_mem_checked. wpi_norm/=.
    iDestruct (mmio_range_lookup with "Hmem Hm") as %Hread; [done|].
    rewrite N2Z.id in Hread.
    iDestruct (mmio_range_in_range with "Hm") as %?.
    iDestruct (mmio_range_Forall with "Hmem Hm") as %?.
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "?".
    iApply wpi_bind. iApply wpi_assert; [done|]. rewrite Hread. wpi_norm/=.
    iApply wpi_bind. iApply wpi_assert; [naive_solver|].
    iApply wpi_bind. iApply wpi_assert; [naive_solver|].
    iApply wpi_bind. iApply (@wpi_emit_label with "[$]"); [done|]. iIntros "?".
    rewrite interp_recursive_call. by iApply ("Hcont" with "[$] [%] [$] [$] [$] [$]").
  Qed.

  Lemma wp_write_mem n len a (vold vnew : bv n) es ann res kind tag:
    n = (8 * len)%N →
    0 < Z.of_N len →
    bv_unsigned a ↦ₘ vold -∗
    (bv_unsigned a ↦ₘ vnew -∗ WPasm es) -∗
    WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iIntros (??) "Hm Hcont". subst. setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite bvn_to_bv_to_bvn/=/read_mem_checked. wpi_norm/=.
    iDestruct (mem_mapsto_lookup with "[$] Hm") as %[len' [? Heq]].
    have ? : len' = len by lia. subst.
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "?".
    iApply wpi_bind. iApply wpi_assert; [done|]. rewrite Heq. wpi_norm/=.
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "?".
    iApply wpi_bind. iApply (wpi_set_state_isla with "[$]"). iIntros "?".
    iApply wpi_update.
    iMod (mem_mapsto_update with "[$] Hm") as (len' ?) "[Hmem Hm]". iModIntro.
    rewrite Z_to_bv_bv_unsigned. have ? : len' = len by lia. subst.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[$] [%] [$] [$] [$] [$]").
  Qed.

  Lemma wp_write_mem_array n len a a' vnew (i : nat) (l : list (bv n)) es ann kind res tag:
    n = (8 * len)%N →
    0 < Z.of_N len →
    (i < length l)%nat →
    a' = bv_unsigned a - (i * Z.of_N len) →
    a' ↦ₘ∗ l -∗
    (a' ↦ₘ∗ <[i := vnew]> l -∗ WPasm es) -∗
    WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iIntros (??[??]%lookup_lt_is_Some_2 ->) "Hm Hcont".
    iDestruct (mem_mapsto_array_insert_acc with "Hm") as "[Hv Hm]"; [done..|].
    rewrite Z.sub_add. iApply (wp_write_mem with "Hv"); [lia..|].
    iIntros "Hl". iApply ("Hcont"). by iApply "Hm".
  Qed.

  Lemma wp_write_mmio n len a (vnew : bv n) es ann res kind tag (Pκs : spec):
    n = (8 * len)%N →
    0 < Z.of_N len →
    Pκs [SWriteMem a vnew] →
    mmio_range (bv_unsigned a) (Z.of_N len) -∗
    spec_trace Pκs -∗
    (spec_trace (λ κs, Pκs (SWriteMem a vnew::κs)) -∗ WPasm es) -∗
    WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iIntros (???) "Hm Hspec Hcont". subst. setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite bvn_to_bv_to_bvn/=/read_mem_checked. wpi_norm/=.
    iDestruct (mmio_range_lookup with "[$] Hm") as %Hread; [done|].
    rewrite N2Z.id in Hread.
    iDestruct (mmio_range_in_range with "Hm") as %?.
    iDestruct (mmio_range_Forall with "[$] Hm") as %?.
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "?".
    iApply wpi_bind. iApply wpi_assert; [done|]. rewrite Hread. wpi_norm/=.
    iApply wpi_bind. iApply wpi_assert; [naive_solver|].
    iApply wpi_bind. iApply wpi_assert; [naive_solver|].
    iApply wpi_bind. iApply (@wpi_emit_label with "[$]"); [done|]. iIntros "?".
    rewrite interp_recursive_call. by iApply ("Hcont" with "[$] [%] [$] [$] [$] [$]").
  Qed.

  (** * Other lifting lemmas  *)
  Lemma wp_branch_address v es ann:
    WPasm es -∗
    WPasm (BranchAddress v ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_branch c desc es ann:
    WPasm es -∗
    WPasm (Branch c desc ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_declare_const_bv v es ann b:
    (∀ (n : bv b), WPasm (subst_trace (Val_Bits n) v es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    iApply wpi_bind. iApply @wpi_demonic_trigger. iIntros (?).
    iApply wpi_bind. iApply @wpi_assume. iIntros (?).
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_declare_const_bool v es ann:
    (∀ (b : bool), WPasm (subst_trace (Val_Bool b) v es)) -∗
    WPasm (Smt (DeclareConst v Ty_Bool) ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    iApply wpi_bind. iApply @wpi_demonic_trigger. iIntros (?).
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_declare_const_enum v es i ann:
    (∀ c, WPasm (subst_trace (Val_Enum (c)) v es)) -∗
    WPasm (Smt (DeclareConst v (Ty_Enum i)) ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    iApply wpi_bind. iApply @wpi_demonic_trigger. iIntros (?).
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_define_const n es ann e:
    WPexp e {{ v, WPasm (subst_trace v n es) }} -∗
    WPasm (Smt (DefineConst n e) ann :t: es).
  Proof.
    rewrite wp_asm_unfold wp_exp_unfold. iDestruct 1 as (v Hv) "Hcont".
    rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite Hv. wpi_norm/=.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_assert es ann e:
    WPexp e {{ v, ∃ b, ⌜v = Val_Bool b⌝ ∗ (⌜b = true⌝ -∗ WPasm es) }} -∗
    WPasm (Smt (Assert e) ann :t: es).
  Proof.
    rewrite wp_exp_unfold. iDestruct 1 as (v Hv b ?) "Hcont". subst v.
    rewrite !wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite Hv. wpi_norm/=. iApply wpi_bind. iApply @wpi_assume. iIntros (?). destruct b => //.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_assume es ann e:
    WPaexp e {{ v, ⌜v = Val_Bool true⌝ ∗ WPasm es }} -∗
    WPasm (Assume e ann :t: es).
  Proof.
    rewrite wp_a_exp_unfold wp_asm_eq. iIntros "Hexp". iIntros (? ?) "????".
    iDestruct ("Hexp" with "[$]") as (v Hv) "(?&%&Hcont)"; subst.
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    iApply wpi_bind. iApply (wpi_get_state_isla with "[$]"). iIntros "?". rewrite Hv /=. wpi_norm/=.
    iApply wpi_bind. iApply wpi_assert; [done|].
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_barrier es v ann:
    WPasm es -∗
    WPasm (Barrier v ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

  Lemma wp_abstract_primop es n v args ann:
    WPasm es -∗
    WPasm (AbstractPrimop n v args ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold. iIntros (? ?) "????".
    wpi_norm/=. iApply wpi_bind. iApply @wpi_step => /=. do 2 iModIntro.
    rewrite interp_recursive_call. by iApply ("Hcont" with "[//] [$] [$] [$] [$]").
  Qed.

End lifting.
