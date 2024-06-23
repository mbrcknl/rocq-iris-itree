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

Lemma exec_agree {R} n m r1 r2 (t : itree voidE R) :
  exec m t = Some r1 →
  exec n t = Some r2 →
  r1 = r2.
Proof.
  intros Hr1 Hr2.
  destruct (decide (n ≤ m)) as [Hlt|Hgt].
  - rewrite (exec_stable m n) // Hr2 in Hr1. by injection Hr1.
  - rewrite (exec_stable n m) // in Hr2; last lia. rewrite Hr1 in Hr2. by injection Hr2.
Qed.

Inductive returns' {R} : itree' voidE R → R → Prop :=
  | returns_Tau t r :
  returns' (observe t) r →
  returns' (TauF t) r
  | returns_Ret r :
  returns' (RetF r) r.
Definition returns {R} (t : itree voidE R) (r : R) : Prop :=
  returns' (observe t) r.

Lemma eutt_returns {R} t (r : R) :
  t ≈ Ret r →
  returns t r.
Proof.
  intros Heutt. rewrite /eutt in Heutt. rewrite /eqit in Heutt. punfold Heutt.
  rewrite /returns.
  rewrite /eqit_ in Heutt. simpl in Heutt. remember (RetF r) as t'.
  induction Heutt; simplify_eq.
  - constructor.
  - constructor. by apply IHHeutt.
Qed.

Lemma exec_ret {R} (t : itree voidE R) r :
  t ≈ Ret r →
  ∃ n, exec n t = Some r.
Proof.
  intros Hret%eutt_returns.
  rewrite /returns in Hret.
  remember (observe t) as ot.
  revert t Heqot.
  induction Hret.
  - intros t' Heqot. destruct (observe t') eqn:Heq; try discriminate. simplify_eq.
    odestruct (IHHret t0 _) as [n Hexec]; first done. exists (S n).
    rewrite /= Heq //.
  - intros t' Heqot. destruct (observe t') eqn:Heq; try discriminate. simplify_eq.
    exists 1. rewrite /= Heq //.
Qed.

Lemma exec_soundness' `{!invGS_gen hlc Σ} {R} M (t : itree voidE R) Φ :
  WPi t @ voidH; M {{ v, ⌜Φ v⌝ }} -∗
  |={M, ∅}=> |={∅, M}=> ⌜∃ n, ∃ r, exec n t = Some r ∧ Φ r⌝.
Proof.
  iIntros "Hwp".
  iMod (voidE_terminates with "Hwp") as "[%v [%Heutt HΦ]]".
  iModIntro. iMod "HΦ". iModIntro. iDestruct "HΦ" as "%HΦ".
  iPureIntro.
  apply exec_ret in Heutt as [n Hexec].
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
