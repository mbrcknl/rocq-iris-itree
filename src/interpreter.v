From ITree Require Import ITree Eqit.
From iris.itree Require Import wpi itree handler void.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop fancy_updates.
From Paco Require Import paco paco2.
From iris.itree Require Export axioms.

Fixpoint exec {R} (fuel : nat) (t : itree voidE R) : option R :=
  match fuel with
  | O => None
  | S n =>
    match observe t with
    | TauF t' => exec n t'
    | VisF e k => match e with end
    | RetF r => Some r
    end
  end.

Lemma exec_stable {R} n m (t : itree voidE R) :
  n ≥ m →
  is_Some (exec m t) →
  exec n t = exec m t.
Proof.
  intros Hlt Hterm.
  induction n as [|n IH]. { destruct m; first done. lia. }
  destruct (decide (S n = m)) as [Heq|Hneq].
  - rewrite -Heq //.
  - rewrite -IH; last lia. rewrite -IH in Hterm; last lia.
    clear IH Hlt Hneq m. revert t Hterm. induction n.
    * intros t Hterm. apply is_Some_None in Hterm as [].
    * intros t Hterm. simpl. simpl in Hterm. destruct (observe t) eqn:Heq; eauto.
Qed.

Lemma exec_eutt {R} n (t t' : itree voidE R) r :
  t ≈ t' →
  exec n t = Some r →
  ∃ n', exec n' t' = Some r.
Proof.
  intros Heutt Hexec.
  destruct n as [|n]. { discriminate. }
  induction n.
Admitted.

Lemma exec_soundness' `{!invGS_gen hlc Σ} {R} M (t : itree voidE R) Φ :
  WPi t @ voidH; M {{ v, ⌜Φ v⌝ }} -∗
  |={M, ∅}=> |={∅, M}=> ⌜∃ n, ∃ r, exec n t = Some r ∧ Φ r⌝.
Proof.
  iIntros "Hwp".
  iMod (voidE_terminates with "Hwp") as "[%v [%Heutt HΦ]]".
  iModIntro. iMod "HΦ". iModIntro. iDestruct "HΦ" as "%HΦ".
  iPureIntro. symmetry in Heutt.
  apply exec_eutt with (n := 1) (r := v) in Heutt as [n Hexec]; last done.
  by exists n, v.
Qed.

Lemma exec_soundness `{!invGpreS Σ} {R} M (t : itree voidE R) Φ :
  (∀ {HG : invGS Σ}, ⊢ WPi t @ voidH; M {{ v, ⌜Φ v⌝ }}) →
  ∃ n, ∃ r, exec n t = Some r ∧ Φ r.
Proof.
  intros Hwp.
  apply: uPred.pure_soundness.
  eapply fupd_soundness_gen with (n := 0); first apply _.
  intros Hinv. iIntros "_". iDestruct Hwp as "Hwp".
  iDestruct (exec_soundness' with "Hwp") as "HΦ".
  iMod "HΦ". iMod "HΦ". by iModIntro.
Qed.
