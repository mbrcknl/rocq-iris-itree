From ITree Require Import ITree.
From ITree Require Import Eqit.
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
  (∃ r, t ≅ Ret r) ∨
  (∃ t', t ≅ Tau t') ∨
  (∃ A (e : E A) k, t ≅ Vis e k).
Proof.
  rewrite /eq_itree /eqit /eqit_.
  destruct (observe t) as [r|t'|A e k] eqn:Heq.
  - left. exists r. pfold. rewrite Heq. by apply EqRet.
  - right. left. exists t'. pfold. rewrite Heq. apply EqTau. rewrite /upaco2 /bot2. left.
    by apply Reflexive_eqit.
  - right. right. exists A, e, k. pfold. rewrite Heq. apply EqVis. rewrite /upaco2 /bot2. left.
    by apply Reflexive_eqit.
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
