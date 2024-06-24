From ITree Require Import ITree Eqit.
From stdpp Require Import list.
From iris.itree Require Import axioms itree.
From Paco Require Import paco.
From Paco Require Import paco2.
From Coq Require Import ssreflect.

Inductive trace (E : Type → Type) (R : Type) :=
  | TRet (r : R)
  | TVis (A : Type) (e : E A) (a : A) (k : trace E R)
  | TVisEmpty (A : Type) (e : E A)
  | TCut.

Arguments TRet {_ _}.
Arguments TVis {_ _}.
Arguments TVisEmpty {_ _}.
Arguments TCut {_ _}.

Section is_trace.
  Context {E : Type → Type} {R : Type}.

  Inductive is_trace_
    : trace E R
    → itree' E R
    → Prop :=
  | is_TRet r :
    is_trace_ (TRet r) (RetF r)
  | is_TVis tr' A (e : E A) a k :
    is_trace_ tr' (observe (k a)) →
    is_trace_ (TVis A e a tr') (VisF e k)
  | is_TVisEmpty A (f : A → Empty_set) (e : E A) k :
    is_trace_ (TVisEmpty A e) (VisF e k)
  | is_TCut t :
    is_trace_ TCut t
  | trace_skip_tau tr t' :
    is_trace_ tr (observe t') →
    is_trace_ tr (TauF t').

  Definition is_trace (tr : trace E R) (t : itree E R) : Prop :=
    is_trace_ tr (observe t).

  Local Instance is_trace_eqit_unilateral tr b1 b2 :
    Proper (eqit (=) b1 b2 ==> impl) (is_trace tr).
  Proof.
    intros t1 t2 Heqit%eutt_weak Htr.
    rewrite /is_trace. rewrite /is_trace in Htr.
    remember (observe t1) as ot1. remember (observe t2) as ot2.
    revert t1 t2 ot2 Heqot1 Heqot2 Heqit. induction Htr as [r|tr' A e a k Htr IH|A f e k|t|tr t' Htr IH]; intros t1 t2 ot2 Heqot1 Heqot2 Heqit.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. destruct Heqot2.
      induction Heqit as [r1 r2| | | | ot1 t2' _ _ IH ]; try discriminate.
      * injection Heqot1 as ->. destruct REL. constructor.
      * constructor. by apply IH.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. destruct Heqot2.
      induction Heqit as [ | | B e' k1 k2 REL | | ot1 t2' _ _ IH' ]; try discriminate.
      * simplify_K. simplify_K. constructor. apply IH with (t1 := k1 a) (t2 := k2 a); try done.
        pclearbot. apply REL.
      * constructor. by apply IH'.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. destruct Heqot2.
      induction Heqit as [ | | B e' k1 k2 REL | | ot1 t2' _ _ IH' ]; try discriminate.
      * simplify_K. simplify_K. by constructor.
      * constructor. by apply IH'.
    - punfold Heqit. rewrite /eqit_ in Heqit. remember (observe t1) as ot1. destruct Heqot2.
      induction Heqit as [ | | B e' k1 k2 REL | | ot1 t2' _ _ IH' ]; try discriminate; constructor.
    - apply IH with (t1 := t') (t2 := t2); eauto.
      transitivity (Tau t'). { apply eqit_inv_Tau_l. reflexivity. }
      pfold. rewrite /eqit_. simpl. rewrite Heqot1. punfold Heqit.
  Qed.
  Global Instance is_trace_eqit tr b1 b2 :
    Proper (eqit (=) b1 b2 ==> (↔)) (is_trace tr).
  Proof.
    intros t1 t2 Heqit. split.
    - by apply (is_trace_eqit_unilateral tr b1 b2).
    - apply (is_trace_eqit_unilateral tr b2 b1). apply eqit_flip. eapply (eqit_Proper_R (=)); eauto.
      rewrite /HeterogeneousRelations.eq_rel /HeterogeneousRelations.subrelationH. naive_solver.
  Qed.

  Lemma is_trace_Vis A e a tr' k :
    is_trace tr' (k a) →
    is_trace (TVis A e a tr') (Vis e k).
  Proof.
    intros Htr. by constructor.
  Qed.

  Lemma is_trace_Ret_inv (t : itree E R) r :
    is_trace (TRet r) t →
    t ≈ Ret r.
  Proof.
    intros Htr. rewrite /is_trace in Htr.
    remember (TRet r) as tr. remember (observe t) as ot. revert t Heqot Heqtr.
    induction Htr; intros t_ Heqot Heqtr; simplify_obs; simplify_eq.
    - reflexivity.
    - apply tau_eutt_RR_l; eauto. apply _.
  Qed.
End is_trace.

Class AnswerEqDecision (E : Type → Type) :=
  is_AnswerEqDecision A : E A → EqDecision A.

Global Instance AnswerEqDecisionSum E E' :
  AnswerEqDecision E →
  AnswerEqDecision E' →
  AnswerEqDecision (E +' E').
Proof. by intros HE HE' A [e%HE|e%HE']. Qed.

Program Definition equal `{AnswerEqDecision E} {A : Type} (e : E A) (a a' : A) : {a = a'} + {a ≠ a'} :=
  @decide (a = a') _.
Next Obligation.
  intros E Hdec A e a a'. by apply is_AnswerEqDecision.
Qed.

Fixpoint interp_tr {R E E'} (tr : trace (E +' E') R) : trace E' R :=
  match tr with
  | TRet r => TRet r
  | TVis A (inl1 e) _ k => interp_tr k
  | TVis A (inr1 e) a k => TVis A e a (interp_tr k)
  | TVisEmpty A (inl1 e) =>  (* Placeholder: *) TCut
  | TVisEmpty A (inr1 e) => TVisEmpty A e
  | TCut => TCut
  end.

Inductive is_postfix {E R}
  : trace E R
  → trace E R
  → Prop :=
| is_postfix_same tr :
  is_postfix tr tr
| is_postfix_TVis tr tr' A e a :
  is_postfix tr tr' →
  is_postfix tr (TVis A e a tr').

Lemma interp_tr_is_postfix {E E' R} (tr tr' : trace (E +' E') R) :
  is_postfix tr tr' →
  is_postfix (interp_tr tr) (interp_tr tr').
Proof.
  induction 1; first constructor. destruct e.
  - done.
  - simpl. by constructor.
Qed.
