From ITree Require Import ITree.
From ITree Require Import Eqit.
From ITree Require Import EqAxiom.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.

Global Instance itree_equiv (E : Type → Type) R : Equiv (itree E R) := eq_itree (=).

Global Instance eq_itree_iff {E R} (t' : itree E R) :
  Proper (eq_itree (=) ==> iff) (λ t, t ≅ t').
Proof.
  intros t1 t2 Heqit. by rewrite Heqit.
Qed.

(** TODO: Is this to be found anywhere in the ITree library? *)
Lemma itree_match {E R} (t : itree E R) :
  (∃ r, t = Ret r) ∨
  (∃ t', t = Tau t') ∨
  (∃ A (e : E A) k, t = Vis e k).
Proof.
  rewrite /eq_itree /eqit /eqit_.
  destruct (observe t) as [r|t'|A e k] eqn:Heq.
  - left. exists r. apply bisimulation_is_eq. pfold. rewrite /eqit_ Heq. by apply EqRet.
  - right. left. exists t'. apply bisimulation_is_eq. pfold. rewrite /eqit_ Heq. apply EqTau.
    rewrite /upaco2 /bot2. left. by apply Reflexive_eqit.
  - right. right. exists A, e, k. apply bisimulation_is_eq. pfold. rewrite /eqit_ Heq. apply EqVis.
    rewrite /upaco2 /bot2. left. by apply Reflexive_eqit.
Qed.

Lemma ret_observe_eqit {E R} (r : R) (t : itree E R) :
  RetF r = observe t →
  Ret r ≅ t.
Proof.
  intros Heq. rewrite /eq_itree /eqit. pfold. rewrite /eqit_ -Heq. by constructor.
Qed.

Lemma tau_observe_eqit {E R} (t t' : itree E R) :
  TauF t' = observe t →
  Tau t' ≅ t.
Proof.
  intros Heq. rewrite /eq_itree /eqit. pfold. rewrite /eqit_ -Heq. constructor.
  rewrite /upaco2 /bot2. left. by apply Reflexive_eqit.
Qed.

Lemma vis_observe_eqit {E A R} (e : E A) (k : A → itree E R) (t : itree E R) :
  VisF e k = observe t →
  Vis e k ≅ t.
Proof.
  intros Heq. rewrite /eq_itree /eqit. pfold. rewrite /eqit_ -Heq. constructor.
  rewrite /upaco2 /bot2. left. by apply Reflexive_eqit.
Qed.

Lemma eqit_cases {E R} (t1 t2 : itree E R) :
  t1 ≅ t2 →
  (∃ r, observe t1 = RetF r ∧ observe t2 = RetF r) ∨
  (∃ t1' t2', observe t1 = TauF t1' ∧ observe t2 = TauF t2' ∧ t1' ≅ t2') ∨
  (∃ A (e : E A) k1 k2, observe t1 = VisF e k1 ∧ observe t2 = VisF e k2 ∧ (∀ a, k1 a ≅ k2 a)).
Proof.
  intros Ht. punfold Ht. inversion Ht.
  - left. eexists _. simplify_eq. done.
  - right. left. eexists _, _. simplify_eq. split; first done. split; first done. by pclearbot.
  - right. right. eexists _, _, _, _. split; first done. split; first done. by pclearbot.
  - done.
  - done.
Qed.
