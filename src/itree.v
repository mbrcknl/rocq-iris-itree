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

Lemma eutt_weak {E R} {b1 b2} {t1 t2 : itree E R} :
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

Lemma translate_trigger_eq {E F G} `{E -< F} :
  forall X (e: E X) (h: F ~> G),
    translate h (trigger e) ≅ trigger (h _ (subevent X e)).
Proof.
  intros; unfold trigger; rewrite translate_vis; setoid_rewrite translate_ret; reflexivity.
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
    destruct (bisimulation_is_eq _ _ (ret_observe_eqit _ _ H))
  | H : TauF _ = observe _ |- _ =>
    destruct (bisimulation_is_eq _ _ (tau_observe_eqit _ _ H))
  | H : VisF _ _ = observe _ |- _ =>
    destruct (bisimulation_is_eq _ _ (vis_observe_eqit _ _ _ H))
  end.

Definition do {E R A B} (t : itree E R) : itree (callE A B +' E) R :=
  translate inr1 t.

Lemma interp_do {E A B R} (f : A → itree (callE A B +' E) B) (t : itree E R) :
  interp (recursive f) (do t) ≈ t.
Proof. rewrite /do interp_translate /= interp_trigger_h //. Qed.

Ltac _simpl_itree :=
  repeat (setoid_rewrite bind_ret_l || setoid_rewrite bind_ret_r || setoid_rewrite bind_bind || setoid_rewrite interp_bind || setoid_rewrite interp_trigger || setoid_rewrite interp_ret || setoid_rewrite rec_as_interp || rewrite rec_as_interp || setoid_rewrite interp_vis || setoid_rewrite interp_do || simpl).
Ltac _simpl_itree' H :=
  do [_simpl_itree] in H.
Tactic Notation "simpl_itree" :=
  _simpl_itree.
Tactic Notation "simpl_itree" "in" ident(H) :=
  _simpl_itree' H.

(** * Typeclass-based itree automation *)
(** ** Creating the hint database *)
(** We use a new hint database instead of typeclass_instances such
that we can make everything opaque by default (via Hint Constants Opaque). *)
Create HintDb itree_auto discriminated.
Global Hint Constants Opaque : itree_auto.

(** ** Typeclasses for translating itrees from one event type to another  *)
Class TranslateReSum {E E1 E2} (Hin : E1 -< E2) (HE1 : E -< E1) (HE2 : E -< E2) := {
  translate_resum : ∀ T x, HE2 T x = Hin _ (HE1 T x);
}.
Global Hint Extern 5 (TranslateReSum _ _ _) => (constructor; constructor) : itree_auto.

Record ITreeToTranslate {E1 E2 R} (i : itree E1 R) (H : E2 -< E1) (o : itree E2 R) := {
    itree_to_translate : i ≅ translate (@resum _ _ _ _ H) o
}.
Global Hint Mode ITreeToTranslate + + + ! + - : itree_auto.

Lemma trigger_to_translate R E E1 E2 (e : E _)
  (Hin : E1 -< E2) (Hin2 : E -< E1) (Hin3 : E -< E2) :
  TranslateReSum Hin Hin2 Hin3 →
  ITreeToTranslate (R:=R) (ITree.trigger (subevent _ e)) Hin (ITree.trigger (subevent _ e)).
Proof. move => [?]. constructor. rewrite translate_trigger_eq. by f_equiv. Qed.
Global Hint Resolve trigger_to_translate : itree_auto.

Lemma do_to_translate R A B E (t : itree E R) :
  ITreeToTranslate (R:=R) (do (A:=A) (B:=B) t) _ t.
Proof. constructor. done. Qed.
Global Hint Resolve do_to_translate : itree_auto.

(* TODO: make this an instance or add a normalize lemma for vis? *)
Lemma vis_to_translate R S E E1 E2 (e : E _) k k'
  (Hin : E1 -< E2) (Hin2 : E -< E1) (Hin3 : E -< E2) :
  TranslateReSum Hin Hin2 Hin3 →
  (∀ x : R, ITreeToTranslate (k x) Hin (k' x)) →
  ITreeToTranslate (R:=S) (Vis (subevent _ e) k) Hin (Vis (subevent _ e) k').
Proof.
  move => [Heq] Hk. constructor. rewrite translate_vis /=.
  rewrite -!bind_trigger. f_equiv; [by rewrite /subevent/resum Heq|].
  move => ?. by apply Hk.
Qed.

(* Not an instance since we have [normalize_itree_interp_bind], but this
lemma is useful for proving ITreeToTranslate for definitions. *)
Lemma bind_to_translate R S E1 E2 (Hin : E1 -< E2) t1 t2 (k1 k2 : R → _) :
  ITreeToTranslate (R:=R) t1 Hin t2 →
  (∀ x, ITreeToTranslate (k1 x) Hin (k2 x)) →
  ITreeToTranslate (R:=S) (ITree.bind t1 k1) Hin (ITree.bind t2 k2).
Proof. intros [?] Hk. constructor. rewrite translate_bind. f_equiv; [done|]. intros ?. apply Hk. Qed.

(* Not an instance since we have [normalize_itree_interp_Ret], but this
lemma is useful for proving ITreeToTranslate for definitions. *)
Lemma Ret_to_translate R E1 E2 (Hin : E1 -< E2) (x : R) :
  ITreeToTranslate (Ret x) Hin (Ret x).
Proof. constructor. by rewrite translate_ret. Qed.

(** ** Typeclasses for normalizing itree [i] to itree [o]  *)
(** The parameter [progress] determines whether the instance performed
any simplification. The only instance with [false] for [progress]
should be [normalize_itree_default]. *)
Record NormalizeITree {E R} (progress : bool) (i : itree E R) (o : itree E R) := {
    normalize_itree : i ≈ o
}.
Global Hint Mode NormalizeITree + + - ! - : itree_auto.

Lemma normalize_itree_default {E R} (t : itree E R) :
  NormalizeITree false t t.
Proof. constructor. done. Qed.
Global Hint Resolve normalize_itree_default | 1000 : itree_auto.

Lemma normalize_itree_tau {E R} p (t t' : itree E R) :
  NormalizeITree p t t' →
  NormalizeITree true (Tau t) t'.
Proof. move => [Heq]. constructor. by rewrite Heq tau_eutt. Qed.
Global Hint Resolve normalize_itree_tau : itree_auto.

Lemma normalize_itree_bind_bind {E R S T} p (t1 : itree E S) (t2 : S → itree E T) t3 (t' : itree E R) :
  NormalizeITree p (ITree.bind t1 (λ x, ITree.bind (t2 x) t3)) t' →
  NormalizeITree true (ITree.bind (ITree.bind t1 t2) t3) t'.
Proof. move => [Heq]. constructor. by rewrite -Heq bind_bind. Qed.
Global Hint Resolve normalize_itree_bind_bind : itree_auto.

Lemma normalize_itree_bind_rec_l {E R S} p (t1 t1' : itree E S) t2 (t : itree E R) :
  NormalizeITree true t1 t1' →
  NormalizeITree p (ITree.bind t1' t2) t →
  NormalizeITree true (ITree.bind t1 t2) t.
Proof. move => [Heq1] [Heq2]. constructor. by rewrite -Heq2 Heq1. Qed.
Global Hint Resolve normalize_itree_bind_rec_l | 50 : itree_auto.

Lemma normalize_itree_bind_rec_r {E R S} (t1 : itree E S) (t2 t2' : S → itree E R) :
  (∀ x, NormalizeITree true (t2 x) (t2' x)) →
  NormalizeITree true (ITree.bind t1 t2) (ITree.bind t1 t2').
Proof. move => Heq1. constructor. f_equiv => x. apply Heq1. Qed.
Global Hint Resolve normalize_itree_bind_rec_r | 60 : itree_auto.

Lemma normalize_itree_bind_ret {E R S} p x (t : S → itree E R) t' :
  NormalizeITree p (t x) t' →
  NormalizeITree true (ITree.bind (Ret x) t) t'.
Proof. move => [Heq]. constructor. by rewrite -Heq bind_ret_l. Qed.
Global Hint Resolve normalize_itree_bind_ret : itree_auto.

Lemma normalize_itree_bind_ret_r {E R} p (t : itree E R) t' :
  NormalizeITree p t t' →
  NormalizeITree true (ITree.bind t (λ x, Ret x)) t'.
Proof. move => [Heq]. constructor. by rewrite -Heq bind_ret_r. Qed.
Global Hint Resolve normalize_itree_bind_ret_r | 1 : itree_auto.

Lemma normalize_itree_interp_bind {E F R S} p1 p2 (f : E ~> itree F) (t1 t1' : itree E S) t2 (t' : itree _ R) :
  NormalizeITree p1 t1 t1' →
  NormalizeITree p2 (ITree.bind (interp f t1') (λ x, (interp f (t2 x)))) t' →
  NormalizeITree true (interp f (ITree.bind t1 t2)) t'.
Proof.
  move => [Heq1] [Heq2]. constructor. by rewrite Heq1 -Heq2 interp_bind.
Qed.
Global Hint Resolve normalize_itree_interp_bind : itree_auto.

Lemma normalize_itree_interp_Ret {E F R} (f : E ~> itree F) (x : R) :
  NormalizeITree true (interp f (Ret x)) (Ret x).
Proof. constructor. by rewrite interp_ret. Qed.
Global Hint Resolve normalize_itree_interp_Ret : itree_auto.

Lemma normalize_itree_rec {E A B} p1 p2 (f : A → itree (callE A B +' E) B) (x : A) fx' t' :
  NormalizeITree p1 (f x) fx' →
  NormalizeITree p2 (interp (recursive f) fx') t' →
  NormalizeITree true (rec f x) t'.
Proof. move => [Heq1] [Heq2]. constructor. rewrite rec_as_interp -Heq2 -Heq1 //. Qed.
Global Hint Resolve normalize_itree_rec : itree_auto.

Lemma normalize_itree_interp_trigger {E F R} p (f : ∀ T : Type, E T → itree F T) (e : E R) t' :
  NormalizeITree p (f R e) t' →
  NormalizeITree true (interp f (trigger e)) t'.
Proof. move => [Heq]. constructor. by setoid_rewrite interp_trigger. Qed.
Global Hint Resolve normalize_itree_interp_trigger : itree_auto.

(* TODO: generalize to more interp functions? *)
Lemma normalize_itree_interp_recursive_translate {E R A B} f (t : itree (callE A B +' E) R) t' :
  ITreeToTranslate t _ t' →
  NormalizeITree true (interp (recursive (A:=A) (B:=B) f) t) t'.
Proof.
  move => [Heq]. constructor.
  by rewrite Heq /= interp_translate /recursive interp_trigger_h.
Qed.
Global Hint Resolve normalize_itree_interp_recursive_translate | 20 : itree_auto.

Lemma normalize_itree_translate_Ret {E F R} h (x : R) :
  NormalizeITree true (translate (E:=E) (F:=F) h (Ret x)) (Ret x).
Proof. constructor. by rewrite translate_ret. Qed.
Global Hint Resolve normalize_itree_translate_Ret : itree_auto.

Lemma normalize_itree_translate_Tau {E F R} h (t : itree E R) t' p :
  NormalizeITree p (translate h t) t' →
  NormalizeITree true (translate (E:=E) (F:=F) h (Tau t)) t'.
Proof. move => [Heq]. constructor. by rewrite -Heq translate_tau tau_eutt. Qed.
Global Hint Resolve normalize_itree_translate_Tau : itree_auto.

Lemma normalize_itree_translate_Vis {E F R} A e h (k : A →itree E R) t' p :
  NormalizeITree p (Vis (h _ e) (λ x, translate h (k x))) t' →
  NormalizeITree true (translate (E:=E) (F:=F) h (Vis e k)) t'.
Proof. move => [Heq]. constructor. by rewrite -Heq translate_vis. Qed.
Global Hint Resolve normalize_itree_translate_Vis : itree_auto.

(** ** Tactic for normalizing eutt using NormalizeITree *)
Lemma tac_normalize_eutt {E R} p1 p2 (t1 t1' t2 t2' : itree E R) :
  NormalizeITree p1 t1 t1' →
  NormalizeITree p2 t2 t2' →
  t1' ≈ t2' →
  t1 ≈ t2.
Proof. by move => [->] [->]. Qed.
Lemma tac_normalize_eutt_l {E R} p1 (t1 t1' t2 : itree E R) :
  NormalizeITree p1 t1 t1' →
  t1' ≈ t2 →
  t1 ≈ t2.
Proof. by move => [->]. Qed.

Ltac solve_normalize_itree :=
  solve [typeclasses eauto with itree_auto].

Ltac eutt_norm :=
  rewrite -/(eutt _ _);
  lazymatch goal with
  | |- ?t1 ≈ ?t2 =>
      tryif is_evar t2 then
        notypeclasses refine (tac_normalize_eutt_l _ _ _ _ _ _);
            [solve_normalize_itree..|]
        else
          notypeclasses refine (tac_normalize_eutt _ _ _ _ _ _ _ _ _);
          [solve_normalize_itree..|]
  end.
Tactic Notation "eutt_norm/=" :=
  repeat (simpl; eutt_norm).

(** ** Tests for itree automation *)
Module itree_auto_test.
  Inductive testE : Type → Type :=
  | test (n : nat) : testE nat.

  Implicit Types (t : itree (callE nat nat +' testE) unit).

  Goal ∀ t, Tau t ≈ t.
    unfold eutt. intros. eutt_norm. match goal with | |- t ≈ t => idtac end.
  Abort.

  Goal ∀ t, ((Tau (Ret tt));; t) ≈ t.
    intros. eutt_norm. match goal with | |- t ≈ t => idtac end.
  Abort.

  (*
  Goal ∀ t, (interp (recursive (λ x : nat, Ret x)) (trigger (test 1));; t) ≈ t.
    intros. eutt_norm. match goal with | |- (trigger (test 1);; t) ≈ t => idtac end.
  Abort.
  *)

  Goal ∀ t, ∃ t', Tau t ≈ t' ∧ t' = t'.
    intros. eexists _. split. { eutt_norm. done. }
    match goal with | |- t = t => idtac end.
  Abort.
End itree_auto_test.
