From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import bi.
Import uPred.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.itree Require Import itree.
From iris.itree Require Import axioms.
From iris.bi Require Import fixpoint.
From iris.bi Require Import derived_laws.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import ITree.
From ITree Require Import Basics.Monad.
From ITree Require Import Eqit.

Definition voidE : Type → Type := const void.

(* TODO: Use syntactic sugar such as stdpp's Equiv (≡) and (>>=). *)

Variant ubE : Type → Type :=
  | EUb : ubE void.

Definition ub {R : Type} `{ubE -< E} : itree E R :=
  vis EUb (λ (a : Empty_set), match a with end).

Section handler.
  Context {Σ : gFunctors}.

  Program Definition ubH : iHandler Σ ubE :=
    IHandler (λ _ _ _ _, False%I) _.
  Next Obligation.
    eauto.
  Qed.
  Global Instance ubH_Sequential :
    Sequential ubH.
  Proof.
    by iIntros (A e Φ s) "HH".
  Qed.
End handler.

Section ub_adequacy.
  (** TODO: [invGS_gen hlc Σ] should imply [invGpresS Σ]. *)
  Context `{!invGS_gen hlc Σ} `{invGpreS Σ} {R : Type}.

  Inductive no_ub : itree ubE R → Prop :=
  | NoUbRet r :
    no_ub (Ret r)
  | NoUbTau t :
    no_ub t →
    no_ub (Tau t).

  Inductive returns : itree ubE R → R → Prop :=
  | ReturnsRet r :
    returns (Ret r) r
  | ReturnsTau t r :
    returns t r →
    returns (Tau t) r.

  Lemma no_ub_returns t :
    no_ub t → ∃ r, returns t r.
  Proof.
    induction 1 as [|? ? [? ?]]; eexists; constructor; eauto.
  Qed.

  Lemma ub_adequacy' t Φ :
    WPi t @ ubH; ∅ {{ Φ }} -∗ |={∅}=> ⌜no_ub t⌝.
  Proof.
    iRevert (t Φ). iApply wpi_iter'.
    - iIntros "!>" (Φ r) "Hwp". iPureIntro. constructor.
    - iIntros "!>" (Φ t) ">>%Hwp". iPureIntro. by constructor.
    - iIntros "!>" (Φ A [] k) ">[]".
  Qed.

  (* TODO: Prove full adequacy theorem.

  (** TODO: A lemma like this is in the new Iris, but I need to update. *)
  Lemma fupd_soundness_gen `{!invGpreS Σ} (φ : Prop) n E1 E2 :
    (∀ `{Hinv : invGS_gen hlc Σ},
      £ n ={E1,E2}=∗ ⌜ φ ⌝) →
    φ.
  Proof.
    destruct hlc.
    - apply fupd_soundness_lc.
    - intros Hφ.
      apply (pure_soundness (M:=iResUR Σ) φ).
      apply fupd_plain_soundness_no_lc with (E1 := E1) (E2 := E2) (m := n).
      { apply _. }
      done.
  Qed.

  Lemma fupd_pure E1 E2 φ :
    (∀ `{Hinv : invGS_gen hlc Σ}, ⊢@{iProp Σ} |={E1,E2}=> ⌜φ⌝) → φ.
  Proof.
    intros Hφ.
    apply fupd_soundness_gen with (n := 0) (E1 := E1) (E2 := E2).
    iIntros (Hinv) "_". iApply Hφ.
  Qed.

  Lemma ub_adequacy'' t Φ :
    (∀ `{Hinv : invGS_gen hlc Σ}, ⊢ WPi t @ ubH; ∅ {{ r, ⌜Φ r⌝ }}) → ∃ r, returns t r ∧ Φ r.
  Proof.
    intros Hwp.
    assert (Hub : ∀ Hinv : invGS_gen hlc Σ, ⊢@{iProp Σ} |={∅}=> ⌜no_ub t⌝).
    { iIntros (Hinv). specialize (Hwp Hinv). rewrite ub_adequacy' in Hwp. }
    rewrite ub_adequacy' in Hwp'. apply fupd_pure in Hwp' as Hub.
    apply no_ub_returns in Hub as [r Hret]. exists r. split; first done.
    induction Hret as [|t r Hret IH].
    - rewrite -wpi_ret' in Hwp. by apply fupd_pure in Hwp.
    - apply IH.
      * by rewrite -wpi_tau in Hwp.
      * apply fupd_pure in Hwp'. inversion Hwp'. eauto.
  Qed.

    apply fancy_updates.fupd_soundness_gen in Hwp.
    iRevert (t Φ). iApply wpi_iter'.
    - iIntros "!>" (Φ r) "Hwp". iPureIntro. constructor.
    - iIntros "!>" (Φ t) ">>%Hwp". iPureIntro. by constructor.
    - iIntros "!>" (Φ A [] k) ">[]".
  Qed.

  (** TODO: Enhance with masks. *)

  *)
End ub_adequacy.
