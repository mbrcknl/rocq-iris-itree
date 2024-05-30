From iris.itree Require Export axioms.
From ITree Require Import ITree.
From ITree Require Import Eqit.
From ITree Require Import TranslateFacts InterpFacts RecursionFacts.
From iris.proofmode Require Import proofmode.
From Paco Require Import paco.

Notation "m ≫= f" := (ITree.bind f m) (at level 60, right associativity) : itree_scope.
Notation "x ← y ; z" := (ITree.bind y (fun x : _ => z)%itree)
  (at level 20, y at level 100, z at level 200,
  format "x  ←  y ;  '/' z") : itree_scope.
Notation "' x ← y ; z" := (ITree.bind y (fun x_ : _ => match x_ with x => z end)%itree)
  (at level 20, x pattern, y at level 100, z at level 200,
  format "' x  ←  y ;  '/' z") : itree_scope.
Notation "x ;; z" := (ITree.bind x (fun _ => z)%itree)
  (at level 100, z at level 200, right associativity) : itree_scope.

(* Global Instance itree_equiv (E : Type → Type) R : Equiv (itree E R) := eq_itree (=). *)

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

Lemma bind_tau_r {A B E} (t : itree E A) (k : A → itree E B) :
  ITree.bind t (λ x : A, Tau (k x)) ≈ ITree.bind t k.
Proof.
  apply eqit_bind; first done. intros a. apply tau_eutt.
Qed.

Lemma translate_Ret_inv {E1 E2 R} (f : E1 ~> E2) (t : itree E1 R) (r : R) :
  translate f t ≅ Ret r →
  t ≅ Ret r.
Proof.
  intros. rewrite (itree_eta t) in H. setoid_rewrite (itree_eta t).
  desobs t Ht; clear t Ht; rewrite unfold_translate in H; cbn in H.
  - punfold H; red in H; inversion H. by simplify_eq.
  - punfold H; red in H; inversion H; inversion CHECK.
  - apply eqitree_inv_Ret_r in H. discriminate.
Qed.

Lemma translate_Tau_inv {E1 E2 R} (f : E1 ~> E2) (t1 : itree E1 R) (t2' : itree E2 R) :
  translate f t1 ≅ Tau t2' →
  ∃ t1', t1 ≅ Tau t1' ∧ translate f t1' ≅ t2'.
Proof.
  intros. rewrite (itree_eta t1) in H. setoid_rewrite (itree_eta t1).
  desobs t1 Ht; clear t1 Ht; rewrite unfold_translate in H; cbn in H.
  - punfold H; red in H; inversion H. by simplify_eq.
  - punfold H; red in H; inversion H; exists t; by pclearbot.
  - apply eqitree_inv_Tau_r in H as [t [H _]]. discriminate.
Qed.

Lemma eqit_flip' {R E} b1 b2 (t1 t2 : itree E R) :
  eqit (=) b1 b2 t1 t2 → eqit (=) b2 b1 t2 t1.
Proof.
  intros Heqit. apply eqit_flip. eapply eqit_mon; last apply Heqit; eauto. by intros.
Qed.

Lemma eutt_weak {E R} b1 b2 (t1 t2 : itree E R) :
  eqit (=) b1 b2 t1 t2 →
  t1 ≈ t2.
Proof.
  intros Heqit.
  destruct b1, b2.
  - done.
  - by apply euttge_sub_eutt.
  - apply eqit_flip' in Heqit. symmetry. by apply euttge_sub_eutt.
  - by apply eq_sub_eutt.
Qed.

Lemma map_vis {E A B T} (f : A → B) (e : E T) (k : T → itree E A) :
  @ITree.map E _ _ f (Vis e k) ≅ Vis e (λ a, ITree.map f (k a)).
Proof.
  rewrite /ITree.map bind_vis //.
Qed.

Lemma unobserve {E R} (to : itree' E R) :
  ∃ t, to = observe t.
Proof.
  destruct to.
  - by exists (Ret r).
  - by exists (Tau t).
  - by exists (Vis e k).
Qed.

Ltac simplify_obs :=
  repeat match goal with
  | H : RetF _ = observe _ |- _ =>
    apply ret_observe_eqit in H as <-
  | H : TauF _ = observe _ |- _ =>
    apply tau_observe_eqit in H as <-
  | H : VisF _ _ = observe _ |- _ =>
    apply vis_observe_eqit in H as <-
  end.

Ltac _simpl_itree :=
  repeat (setoid_rewrite bind_ret_l || setoid_rewrite bind_ret_r || setoid_rewrite bind_bind || setoid_rewrite interp_bind || setoid_rewrite interp_trigger || setoid_rewrite interp_ret || setoid_rewrite rec_as_interp || rewrite rec_as_interp || setoid_rewrite interp_vis || simpl).
Ltac _simpl_itree' H :=
  do [_simpl_itree] in H.
Tactic Notation "simpl_itree" :=
  _simpl_itree.
Tactic Notation "simpl_itree" "in" ident(H) :=
  _simpl_itree' H.
