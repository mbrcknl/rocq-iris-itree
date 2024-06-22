From ITree Require Import ITree.
From ITree Require Import Eqit.
From ITree Require Import TranslateFacts InterpFacts RecursionFacts.
From Paco Require Import paco.
From iris.bi.lib Require Import fixpoint.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import invariants.
From iris.itree Require Import itree wpi handler ub state choice halt later.
From iris.itree.threadpool Require Import handler.

Local Unset Program Cases.

Lemma delete_app_r {A} i (l1 l2 : list A) :
  length l1 ≤ i →
  delete i (l1 ++ l2) = l1 ++ delete (i - length l1) l2.
Proof.
  move => Hi. rewrite !delete_take_drop.
  rewrite take_app_ge ?drop_app_ge ?app_assoc ?Nat.sub_succ_l //. lia.
Qed.

Lemma delete_app_l {A} i (l1 l2 : list A) :
  i < length l1 →
  delete i (l1 ++ l2) = delete i l1 ++ l2.
Proof.
  move => Hi. rewrite !delete_take_drop.
  by rewrite take_app_le ?drop_app_le ?app_assoc; [|lia..].
Qed.


(** * [bi_close] *)
Definition bi_close {PROP : bi} {A : Type} (R : relation A) (P : A → PROP) : A → PROP :=
  λ a, (∃ a', ⌜R a a'⌝ ∗ P a')%I.

Arguments bi_close : simpl never.

Section bi_close.
  Context {PROP : bi} {A : Type} (R : relation A).
  Implicit Types (P : A → PROP).

  Global Instance bi_close_proper P `{!Symmetric R} `{!Transitive R}:
    Proper (R ==> (⊣⊢)) (bi_close R P).
  Proof.
    move => ?? HR.
    iSplit; iIntros "[%a [Hp $]]"; iApply (bi.pure_mono with "Hp") => ?.
    - etrans; [|done]. done.
    - etrans; [|done]. done.
  Qed.

  Lemma bi_close_mono P1 P2 x:
    bi_close R P1 x -∗ (∀ y, P1 y -∗ P2 y) -∗ bi_close R P2 x.
  Proof.
    iIntros "[%a [HR ?]] Hwand". iExists _. iSplitL "HR"; [done|]. by iApply "Hwand".
  Qed.

  Lemma bi_close_intro P x `{!Reflexive R}:
    P x -∗
    bi_close R P x.
  Proof. iIntros "$". by iPureIntro. Qed.
End bi_close.

(** * [bi_mono0] *)
(* TODO: rename to limo or lin_mon? for linear monotonicity *)
Definition bi_mono0 {PROP : bi} {A : Type} (P : (A → PROP) → PROP) : (A → PROP) → PROP :=
  λ Q, (∃ Q', P Q' ∗ (∀ x, Q' x -∗ Q x))%I.

Arguments bi_mono0 : simpl never.

Section bi_mono0.
  Context {PROP : bi} {A : Type}.
  Implicit Types (P : (A → PROP) → PROP).

  Lemma bi_mono0_intro0 P Q :
    P Q -∗
    bi_mono0 P Q.
  Proof. iIntros "?". iExists _. iFrame. iIntros (?) "$". Qed.

  Lemma bi_mono0_mono P Q1 Q2 :
    bi_mono0 P Q1 -∗
    (∀ x, Q1 x -∗ Q2 x) -∗
    bi_mono0 P Q2.
  Proof.
    iIntros "[% [HP HQ1]] HQ". iExists _. iFrame "HP". iIntros (?) "?".
    iApply "HQ". by iApply "HQ1".
  Qed.

  Lemma bi_mono0_mono_l P1 P2 Q :
    bi_mono0 P1 Q -∗
    (∀ Q, P1 Q -∗ P2 Q) -∗
    bi_mono0 P2 Q.
  Proof.
    iIntros "[% [HP HQ1]] HQ". iExists _. iFrame "HQ1". by iApply "HQ".
  Qed.

  Lemma bi_mono0_elim P Q :
    bi_mono0 P Q -∗
    (∀ Q Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗
    P Q.
  Proof. iIntros "[% [??]] HP". iApply ("HP" with "[$] [$]"). Qed.

  (** Derived laws *)
  Lemma bi_mono0_dup P Q :
    bi_mono0 (bi_mono0 P) Q -∗
    bi_mono0 P Q.
  Proof.
    iIntros "?".
    iApply (bi_mono0_elim with "[$] []").
    iIntros (??) "??". by iApply (bi_mono0_mono with "[$]").
  Qed.

  Lemma bi_mono0_intro P Q Q' :
    P Q' -∗
    (∀ x, Q' x -∗ Q x) -∗
    bi_mono0 P Q.
  Proof.
    iIntros "HP HQ".
    iApply (bi_mono0_mono with "[HP] HQ").
    by iApply bi_mono0_intro0.
  Qed.

End bi_mono0.
Global Typeclasses Opaque bi_mono0.

(** * [lfp_tp] *)
Section lfp_tp.
  Context {Σ : gFunctors} {A : Type}.
  Context (F : (A -d> iProp Σ) -d> (A -d> iProp Σ)).

  Definition lfp_tpF
    (lfp_tp : leibnizO (list (((A → iProp Σ) → iProp Σ))) -d> iPropO Σ) :
    leibnizO (list (((A → iProp Σ) → iProp Σ))) -d> iPropO Σ :=
    λ Ms, (∀ i M, ⌜Ms !! i = Some M⌝ -∗ bi_mono0 M (λ x, ∃ G, F G x ∗
       (∀ Ms', ([∗ list] M'∈Ms', M' G) -∗ lfp_tp (Ms' ++ delete i Ms))))%I.

  Global Instance lfp_tpF_ne :
    NonExpansive lfp_tpF.
  Proof. move => ?. rewrite /lfp_tpF /bi_mono0. solve_proper. Qed.

  Lemma lfp_tpF_mono tp1 tp2 :
    ⊢ □ (∀ Ms, tp1 Ms -∗ tp2 Ms)
    -∗ ∀ Ms, lfp_tpF tp1 Ms -∗ lfp_tpF tp2 Ms.
  Proof.
    iIntros "#Hwand" (Ms) "Htp".
    iIntros (???). iApply (bi_mono0_mono with "[Htp]"); [by iApply "Htp"|].
    iIntros (?) "[%G [$ Htp]]". iIntros (?) "?". iApply "Hwand". by iApply "Htp".
  Qed.

  Global Instance lfp_tp_monotone :
    BiMonoPred lfp_tpF.
  Proof.
    constructor; [|apply _].
    move => ????. by apply lfp_tpF_mono.
  Qed.

  Definition lfp_tp (Ms : list (((A → iProp Σ) → iProp Σ))) : iProp Σ :=
    bi_least_fixpoint lfp_tpF Ms.

  Lemma lfp_tp_unfold Ms :
    lfp_tp Ms ⊣⊢ lfp_tpF lfp_tp Ms.
  Proof. apply: least_fixpoint_unfold. Qed.

  Lemma lfp_tp_ind Φ :
    □ (∀ y, lfp_tpF (λ x, Φ x ∧ lfp_tp x) y -∗ Φ y) -∗
    ∀ Ms, lfp_tp Ms -∗ Φ Ms.
  Proof. apply: least_fixpoint_ind. Qed.

  Lemma lfp_tp_nil :
    ⊢ lfp_tp [].
  Proof. iApply lfp_tp_unfold. by iIntros (???). Qed.

  Lemma lfp_tpF_perm Ms1 Ms2 wp1 wp2:
    Ms1 ≡ₚ Ms2 →
    lfp_tpF wp1 Ms1 -∗
    (∀ Ms1 Ms2, ⌜Ms1 ≡ₚ Ms2⌝ -∗ wp1 Ms1 -∗ wp2 Ms2) -∗
    lfp_tpF wp2 Ms2.
  Proof.
    intros Hperm%symmetry. iIntros "Htp Hwp". iIntros (?? Hm).
    erewrite delete_Permutation in Hperm; [|done].
    move: (Hperm). intros [Ms1' [Ms2' ?]]%symmetry%Permutation_vs_cons_inv. subst.
    rewrite -Permutation_middle in Hperm. apply Permutation_cons_inv in Hperm.
    iApply (bi_mono0_mono with "[Htp]").
    { iApply ("Htp" $! (length Ms1')). iPureIntro. by apply list_lookup_middle. }
    iIntros (?) "[%G [$ Htp]]". iIntros (?) "?".
    iDestruct ("Htp" with "[$]") as "Htp". iApply "Hwp"; [|done].
    iPureIntro. rewrite delete_middle. by rewrite -Hperm.
  Qed.

  Lemma lfp_tpF_perm_close Ms1 Ms2 wp:
    Ms1 ≡ₚ Ms2 →
    lfp_tpF wp Ms1 -∗
    lfp_tpF (bi_close (≡ₚ) wp) Ms2.
  Proof.
    iIntros (?) "?". iApply (lfp_tpF_perm with "[$]"); [done|].
    iIntros (?? Hperm) "?". rewrite -Hperm. by iApply bi_close_intro.
  Qed.

  Lemma lfp_tp_perm Ms1 Ms2 :
    Ms1 ≡ₚ Ms2 →
    lfp_tp Ms1 -∗ lfp_tp Ms2.
  Proof.
    move => Hperm. iIntros "Htp". iRevert (Ms2 Hperm). iRevert (Ms1) "Htp".
    iApply lfp_tp_ind. iIntros "!>" (Ms1) "Htp".
    iIntros (Ms2 ?). rewrite lfp_tp_unfold.
    iApply (lfp_tpF_perm with "Htp"); [done|].
    iIntros (???) "[Hw _]". by iApply "Hw".
  Qed.

  Global Instance lfp_tp_proper_perm :
    Proper ((≡ₚ) ==> (⊣⊢)) lfp_tp.
  Proof. move => Ms1 Ms2 Hperm. iSplit; by iApply lfp_tp_perm. Qed.

  Lemma lfp_tp_app Ms1 Ms2 :
    lfp_tp Ms1 -∗ lfp_tp Ms2 -∗ lfp_tp (Ms1 ++ Ms2).
  Proof.
    iIntros "Hx1 Hx2". iRevert (Ms2) "Hx2"; iRevert (Ms1) "Hx1".
    iApply lfp_tp_ind.
    iIntros "!>" (Ms1) "Hx1". iIntros (Ms2) "Hx2".
    iRevert (Ms1) "Hx1"; iRevert (Ms2) "Hx2".
    iApply lfp_tp_ind.
    iIntros "!>" (Ms2) "Hx2". iIntros (Ms1) "Hx1".
    iApply lfp_tp_unfold. iIntros (??[?|[??]]%lookup_app_Some).
    - iDestruct ("Hx1" with "[//]") as "Hx".
      iApply (bi_mono0_mono with "Hx"). iDestruct 1 as (?) "[$ HG]".
      iIntros (?) "Hx'".
      iDestruct ("HG" with "[$]") as "[Hc _]".
      rewrite delete_app_l. 2: by apply: lookup_lt_Some.
      rewrite app_assoc. iApply "Hc". iApply lfp_tp_unfold.
      iApply (lfp_tpF_mono with "[] Hx2"). by iIntros "!>" (?) "[_ $]".
    - iDestruct ("Hx2" with "[//]") as "Hx".
      iApply (bi_mono0_mono with "Hx"). iDestruct 1 as (?) "[$ HG]".
      iIntros (?) "Hx'". iDestruct ("HG" with "[$]") as "[Hc _]".
      iDestruct ("Hc" with "[$]") as "?".
      rewrite app_assoc (Permutation_app_comm Ms1) -app_assoc delete_app_r //.
  Qed.

  Lemma lfp_tp_cons M Ms :
    lfp_tp [M] -∗ lfp_tp Ms -∗ lfp_tp (M :: Ms).
  Proof. iIntros "Hx HMs". iDestruct (lfp_tp_app with "Hx HMs") as "$". Qed.

  Lemma lfp_tp_singleton_mod_elim M :
    M (λ x, (lfp_tp [λ P, P x])) -∗ lfp_tp [M].
  Proof.
    iIntros "Hx". iApply lfp_tp_unfold.
    iIntros (??[-> <-]%list_lookup_singleton_Some).
    iApply (bi_mono0_intro with "Hx") => /=. iIntros (?) "Hx".
    rewrite lfp_tp_unfold. iDestruct ("Hx" $! 0 with "[//]") as "Hx" => /=.
    iDestruct (bi_mono0_elim with "Hx []") as "$".
    iIntros (??) "Hwand". by iApply "Hwand".
  Qed.


  Lemma lfp_tp_intro x :
    BiMonoPred (F : (leibnizO A → iPropI Σ) → _) →
    bi_least_fixpoint (F : (leibnizO A → iPropI Σ) → _) x -∗ lfp_tp [λ P, P x].
  Proof.
    iIntros (?). iRevert (x).
    iApply least_fixpoint_iter. iIntros "!>" (x) "HF".
    iApply lfp_tp_unfold. iIntros (??[-> <-]%list_lookup_singleton_Some).
    iApply bi_mono0_intro0 => /=. iExists _. iFrame.
    iIntros (Ms') "HG". iInduction Ms' as [|x' Ms'] "IH"; [iApply lfp_tp_nil|].
    simpl. iDestruct "HG" as "[Hx HMs]".
    iApply (lfp_tp_cons with "[Hx] [HMs]"). 2: by iApply "IH".
    by iApply lfp_tp_singleton_mod_elim.
  Qed.

End lfp_tp.


(** * [eHandler] *)
Record eHandler (E GE : Type → Type) (R : Type) := EHandler {
  eh_state : Type;
  eh_state_rel : eh_state → eh_state → Prop;
  ehandle :> ∀ A, E A → eh_state → (A → itree GE R) → (itree GE R → eh_state → Prop) → Prop;
  ehandler_mono : ∀ A e s k C C',
    (∀ s' t', C t' s' → C' t' s') →
    ehandle A e s k C → ehandle A e s k C';
  ehandler_proper A e :
    Proper (eh_state_rel ==> (pointwise_relation _ (eutt eq)) ==> (eutt eq ==> eh_state_rel ==> impl) ==> impl) (ehandle A e);
  eh_state_rel_refl :: Equivalence eh_state_rel;
}.
Arguments EHandler {_ _ _} _ _ _.
Arguments eh_state {_ _ _}.
Arguments eh_state_rel {_ _ _}.

(** * [seHandler] *)
(* Simple version of eHandler *)
Record seHandler (E : Type → Type) := SEHandler {
  seh_state : Type;
  sehandle : ∀ A, E A → seh_state → (A → seh_state → Prop) → Prop;
  sehandler_mono : ∀ A e s C C',
    (∀ a s', C a s' → C' a s') →
    sehandle A e s C → sehandle A e s C';
}.
Arguments SEHandler {_} _ _ _.
Arguments seh_state {_}.
Arguments sehandle {_}.

Program Definition se_to_eHandler E GE R (EH : seHandler E) : eHandler E GE R := {|
   eh_state := EH.(seh_state);
   eh_state_rel := (=);
   ehandle A e s k C := sehandle EH A e s (λ a s', C (k a) s');
|}.
Next Obligation.
  move => ?????????? HC /=. apply sehandler_mono. naive_solver.
Qed.
Next Obligation.
  move => ?????????????? HC /= ?. subst.
  apply: sehandler_mono; [|done]. move => ?? /=.
  by apply: HC.
Qed.

Coercion se_to_eHandler : seHandler >-> eHandler.


(** * [inEH] *)
Class inEH {E1 E2 GE R} `{!E1 -< E2} (EH1 : eHandler E1 GE R) (EH2 : eHandler E2 GE R)
  (f1 : EH2.(eh_state) → EH1.(eh_state)) (f2 : EH1.(eh_state) → EH2.(eh_state) → EH2.(eh_state)) :=
  is_inEH : ∀ A e s2 k C, EH1 A e (f1 s2) k (λ t s1', C t (f2 s1' s2)) → EH2 A (subevent A e) s2 k C.
Global Hint Mode inEH + + + ! ! - ! - - : typeclass_instances.

Global Instance inEH_reflexivity {E GE R} (EH : eHandler E GE R) :
  inEH EH EH id (λ x _, x).
Proof. move => ?????. done. Qed.

(** * [exec] *)
Section exec.
  Context {E : Type → Type} {R : Type}.
  Context (EH : eHandler E E R).

  Variant execF
    (exec : itree E R → EH.(eh_state) → (itree E R → EH.(eh_state) → Prop) → Prop)
    : itree' E R
    → EH.(eh_state)
    → (itree E R → EH.(eh_state) → Prop)
    → Prop :=
  | ExecStop s s' t C t':
    go t ≈ t' →
    EH.(eh_state_rel) s s' →
    C t' s' →
    execF exec t s C
  | ExecTau s t C :
    exec t s C →
    execF exec (TauF t) s C
  | ExecVis s A e k C :
    EH A e s k (λ t' s', exec t' s' C) →
    execF exec (VisF e k) s C.
  Hint Constructors execF : iris_itree.
  Definition exec_
    (exec : itree E R → EH.(eh_state) → (itree E R → EH.(eh_state) → Prop) → Prop)
    : itree E R
    → EH.(eh_state)
    → (itree E R → EH.(eh_state) → Prop)
    → Prop :=
    λ t s C, execF exec (observe t) s C.

  Lemma execF_mono exec exec' s t C :
    exec <3= exec' →
    execF exec  s t C →
    execF exec' s t C.
  Proof.
    intros Hleq HexecF. destruct HexecF; eauto with iris_itree.
    apply: ExecVis. apply: ehandler_mono; [|done]. eauto with iris_itree.
  Qed.
  Lemma exec__mono :
    monotone3 exec_.
  Proof.
    rewrite /monotone3 /exec_. intros. by eapply execF_mono; last done.
  Qed.
  Hint Resolve exec__mono : paco.

  Definition exec : itree E R → EH.(eh_state) → (itree E R → EH.(eh_state) → Prop) → Prop :=
    paco3 exec_ bot3.

  Global Instance exec__proper r:
    Proper (eqit (=) false false ==> (=) ==> (=) ==> (↔)) (exec_ r).
  Proof.
    (* TODO: prove without bisimulation_is_eq *)
    by move => t1 t2 /bisimulation_is_eq -> ?? -> ?? ->.
  Qed.

  Global Instance exec_proper_unilateral :
    Proper (eqit (=) true true ==> EH.(eh_state_rel) ==> (=) ==> impl) exec.
  Proof.
    intros t1 t2 Ht s1 s2 Hs C ? <- Hwpi.
    (* have {}Ht: t1 ≈ t2. { apply: eqit_mon; [..|by apply Ht]; naive_solver. } *)
    move: t1 t2 s1 s2 Ht Hs Hwpi.
    pcofix CIH.
    move => t1 t2 s1 s2 Ht Hs Hwpi.
    punfold Ht. punfold Hwpi.
    rewrite (itree_eta_ t1) in Hwpi. rewrite (itree_eta_ t2).
    elim: Ht Hwpi => //.
    - move => ??? Hwpi. inv Hwpi. pfold. apply: ExecStop; [done| |done].
      by rewrite -Hs.
    - move => ?? REL Hwpi. pclearbot. inv Hwpi.
      + pfold. apply: ExecStop; [|by rewrite -Hs|done]. rewrite -H /= eutt_Tau. done.
      + pfold. apply: ExecTau. right. eapply CIH; [done..| ]. by destruct H0.
    - move => ?? k1 k2 REL Hwpi.
      inv Hwpi.
      + pfold. apply: ExecStop; [|by rewrite -Hs|done]. symmetry. rewrite -H /=.
        pfold. by econstructor.
      + simplify_K. pfold. apply: ExecVis. apply: ehandler_proper; [done| | |done].
        *  move => ?. by edestruct REL.
        * move => /= ?? ? ?? ? [?|//]. right. by eapply CIH.
    - move => ???? IH Hwpi. apply IH. inv Hwpi.
      + apply: ExecStop; [|done|done]. by rewrite /= -H /= tau_eutt -itree_eta_.
      + destruct H0 => //. punfold H.
    - move => ???? IH Hwpi. pfold. apply: ExecTau. left.
      rewrite -itree_eta_ in IH. by apply IH.
  Qed.

  Global Instance exec_proper :
    Proper (eqit (=) true true ==> eh_state_rel EH ==> (=) ==> (↔)) exec.
  Proof.
    intros t1 t2 Ht ?? Hs ?? ->.
    (* have {}Ht: t1 ≈ t2. { apply: eqit_mon; [..|by apply Ht]; naive_solver. } *)
    by split; rewrite -Ht -Hs.
  Qed.

  Lemma exec_dup t s C :
    exec t s (λ t' s', exec t' s' C) →
    exec t s C.
  Proof.
    revert t s. pcofix CIH.
    move => t s He. punfold He.
    inv He.
    - rewrite -H -H0 -itree_eta_ in H1. by eapply paco3_mon.
    - rewrite (itree_eta_ t) -H. pfold. apply ExecTau. pclearbot.
      right. by apply CIH.
    - rewrite (itree_eta_ t) -H. pfold. apply ExecVis.
      apply: ehandler_mono; [|done]. move => /= ???. pclearbot.
      right. by apply CIH.
  Qed.

End exec.
Global Instance : Params (@exec) 3 := {}.
Global Hint Resolve exec__mono : paco.

Section exec.
  Lemma exec_stop E R EH (t : itree E R) s C :
    C t s →
    exec EH t s C.
  Proof. move => ?. pfold. apply: ExecStop; [|done..]. by rewrite -itree_eta_. Qed.

  Lemma exec_vis A E1 E R (e : E1 A) `{!E1 -< E} (EH : eHandler E E R) EH1 (k : A → itree E R) f1 f2 `{!inEH EH1 EH f1 f2} s C :
    EH1 A e (f1 s) k (λ t' s', exec EH t' (f2 s' s) C) →
    exec EH (vis e k) s C.
  Proof.
    move => H1. pfold. apply: ExecVis. apply is_inEH. apply: ehandler_mono; [|done].
    move => /= ???. by left.
  Qed.

  Lemma exec_trigger A E1 E (e : E1 A) `{!E1 -< E} (EH : eHandler E E A) EH1 f1 f2 `{!inEH EH1 EH f1 f2} s C :
    EH1 A e (f1 s) (λ x, Ret x) (λ t' s', C t' (f2 s' s)) →
    exec EH (trigger e) s C.
  Proof.
    move => ?. rewrite /ITree.trigger. apply: exec_vis. apply: ehandler_mono; [|done].
    move => /= ???. by apply exec_stop.
  Qed.
End exec.

(** * [bind rule for exec] *)
Class eHandlerBind {E1 E R S} (EH : eHandler E1 E R) (EHb : eHandler E1 E S) := {
  ebind_to_b : EH.(eh_state) → EHb.(eh_state);
  ebind_from_b : EHb.(eh_state) → EH.(eh_state);
  ebind_from_to_b s : ebind_to_b (ebind_from_b s) = s;
  ebind_to_from_b s : ebind_from_b (ebind_to_b s) = s;
  ebind_state_rel s s' :
    eh_state_rel EHb s s' → eh_state_rel EH (ebind_from_b s) (ebind_from_b s');
  ebind_ehandle A e s k k2 C:
    EHb A e (ebind_to_b s) k (λ t' s', C (ITree.bind t' k2) (ebind_from_b s')) →
    EH A e s (λ x, (x ← k x; k2 x)%itree) C
}.

Global Program Instance eHandlerBind_simple E1 E R S (EH : seHandler E1) :
  eHandlerBind (E:=E) (R:=R) (S:=S) EH EH := {|
   ebind_to_b s := s;
   ebind_from_b s := s;
|}.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Program Definition falseEH E S : seHandler E :=
  SEHandler S (λ A e s C, False) _.
Next Obligation. done. Qed.


Global Program Instance eHandlerBind_default E1 E R S (EH : eHandler E1 E R) :
  eHandlerBind (E:=E) (R:=R) (S:=S) EH (falseEH E1 EH.(eh_state)) | 1000 := {|
   ebind_to_b s := s;
   ebind_from_b s := s;
|}.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. naive_solver. Qed.
Next Obligation. naive_solver. Qed.

Section exec.

  Lemma exec_bind_post E R S EH EHb (t : itree E S) s (k : S → itree E R) C
    `{!eHandlerBind EH EHb} :
    exec EHb t (ebind_to_b s) (λ t' s', C (ITree.bind t' k) (ebind_from_b s')) →
    exec EH (ITree.bind t k) s C.
  Proof.
    revert t s. pcofix CIH.
    move => t s He. punfold He.
    inv He.
    - rewrite -itree_eta_ in H. pfold. apply: ExecStop; [| |done].
      + by rewrite -H -itree_eta_.
      + move: H0 => /ebind_state_rel. by rewrite ebind_to_from_b.
    - rewrite (itree_eta_ t) -H. pfold. rewrite bind_tau. apply ExecTau. right. apply CIH. by pclearbot.
    - rewrite (itree_eta_ t) -H. pfold. rewrite bind_vis. apply ExecVis.
      apply: ebind_ehandle. apply: ehandler_mono; [|done] => ?? /= [?|//].
      right. apply CIH. by rewrite ebind_from_to_b.
  Qed.

  Lemma exec_bind E R S EH EHb (t : itree E S) s (k : S → itree E R) C
    `{!eHandlerBind EH EHb} :
    exec EHb t (ebind_to_b s) (λ t' s', exec EH (ITree.bind t' k) (ebind_from_b s') C) →
    exec EH (ITree.bind t k) s C.
  Proof. move => ?. by eapply exec_dup, exec_bind_post. Qed.

End exec.


(** * [eHanderAdequate] *)
Class eHandlerAdequate {Σ E GE R} (H : iHandler Σ E) (EH : eHandler E GE R)
  `{!invGS_gen hlc Σ} := {
  ehandler_inv : EH.(eh_state) → list (((itree GE R → iProp Σ) → iProp Σ)) → iProp Σ;
  ehandler_adequate : ∀ G A e s Ms C k,
      EH A e s k C →
      H A e (λ a, G (k a)) (λ a, |={⊤, ∅}=> G (k a)) -∗
      ehandler_inv s Ms -∗
      |={∅}=> ∃ t' s' M' Ms' Msn, ⌜C t' s'⌝ ∗ ⌜M' :: Ms' ≡ₚ Msn ++ Ms⌝ ∗
        ([∗ list] M∈Msn, M G) ∗ ehandler_inv s' Ms' ∗
        bi_close (eutt eq) (λ t', (∀ P, M' P ={∅}=∗ P t')) t';
  ehandler_inv_proper :: Proper (EH.(eh_state_rel) ==> (=) ==> (⊢)) ehandler_inv;
}.

Class seHandlerAdequate {Σ E} (H : iHandler Σ E) (EH : seHandler E) `{!invGS_gen hlc Σ} := {
  sehandler_inv : EH.(seh_state) → iProp Σ;
  sehandler_adequate : ∀ A e s C Φ1 Φ2,
      sehandle EH A e s C →
      H A e Φ1 Φ2 -∗
      sehandler_inv s -∗
      |={∅}=> ∃ a s', ⌜C a s'⌝ ∗ sehandler_inv s' ∗ Φ1 a
}.

Program Instance handler_adequate_from_simple {Σ GE R E}
  (H : iHandler Σ E) (EH : seHandler E) `{!invGS_gen hlc Σ}
  `{!seHandlerAdequate H EH} : eHandlerAdequate (GE:=GE) (R:=R) H EH := {
  ehandler_inv s _ := sehandler_inv s;
}.
Next Obligation.
  iIntros (?????????????????) "Hh Hs". simpl in *.
  iMod (sehandler_adequate with "Hh Hs") as (??) "Hp"; [done|].
  iDestruct "Hp" as (?) "[$ HG]". iModIntro. iExists _, _, Ms, [λ P, P (k a)] => /=.
  iSplit; [done|]. iSplit; [done|]. iFrame. iApply bi_close_intro.
  by iIntros (?) "$".
Qed.

Section wp_itree.
  Context {Σ : gFunctors} {R : Type} {E : Type → Type} `{!invGS_gen hlc Σ}.

  Definition wpi_constF (H : iHandler Σ E) (Φ : R → iProp Σ)
    (wpi : leibnizO (itree E R) → iPropO Σ) :
           leibnizO (itree E R) → iPropO Σ :=
    λ t,
      (|={∅}=>
        match observe t with
        | RetF r  => Φ r
        | TauF t' => wpi t'
        | VisF e k => H _ e
            (λ a, wpi (k a))
            (λ a, |={⊤, ∅}=> wpi (k a))
        end
      )%I.

  Lemma wpi_constF_mono H Φ wp1 wp2:
    ⊢ □ (∀ t, wp1 t -∗ wp2 t)
    → ∀ t, wpi_constF H Φ wp1 t -∗ wpi_constF H Φ wp2 t.
  Proof.
    iIntros "#Hwand" (t) "Hwp". rewrite /wpi_constF. destruct (observe t).
    - done.
    - by iApply "Hwand".
    - iApply ihandler_mono; last done.
      * iIntros (a) "Hwp". by iApply "Hwand".
      * iModIntro. iIntros (t') "Hwp". by iApply "Hwand".
  Qed.

  Global Instance wp_itree_pre_monotone H Φ:
    BiMonoPred (wpi_constF H Φ).
  Proof.
    constructor.
    - intros. iIntros "Hwand". by iApply wpi_constF_mono.
    - move => ??. solve_proper.
  Qed.

  Definition wpi_const (H : iHandler Σ E) (Φ : R → iProp Σ) : itree E R → iProp Σ :=
    bi_least_fixpoint (wpi_constF H Φ).

  Lemma wpi_const_iter H Φ P :
    □ (∀ y, wpi_constF H Φ P y -∗ P y) -∗ ∀ t, wpi_const H Φ t -∗ P t.
  Proof. apply: least_fixpoint_iter. Qed.

End wp_itree.


Definition wpi_tp {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGS_gen hlc Σ}
  (H : iHandler Σ E) (Ms : list (((itree E R → iProp Σ) → iProp Σ)))
    (Φ : R → iProp Σ) : iProp Σ :=
    lfp_tp (wpi_constF H Φ) Ms.

Notation "'WPi_tp' ts @ H {{ v , Q } }" := (wpi_tp H ts (λ v, Q))
  (at level 20, ts, Q at level 200,
   format "'[hv' 'WPi_tp'  ts  '/' @  '[' H ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WPi_tp' ts @ H {{ Φ } }" := (WPi_tp ts @ H {{ v, Φ v }})%I
  (at level 20, ts, Φ at level 200, only parsing) : bi_scope.

Section wpi_tp.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGS_gen hlc Σ}.

  Lemma wpi_tp_intro (t : itree E R) H Φ :
    WPi t @ H; ∅ {{Φ}} -∗
    WPi_tp [λ P, P t] @ H {{Φ}}.
  Proof.
    iIntros "Hwpi". iApply lfp_tp_intro.
    iRevert (t Φ) "Hwpi". iApply wpi_iter'.
    { intros. move => ???. eapply least_fixpoint_ne; [|done]. solve_proper. }
    - iIntros "!>" (??) "HΦ". by rewrite least_fixpoint_unfold/wpi_constF/=.
    - iIntros "!>" (??) "HΦ". by iEval (rewrite least_fixpoint_unfold{1}/wpi_constF/=).
    - iIntros "!>" (????) "Hwp".
      iEval (rewrite least_fixpoint_unfold{1}/wpi_constF/=).
      iMod "Hwp". iModIntro. iApply ihandler_mono; [..|done].
      + by iIntros (?) "?".
      + iIntros "!>" (?) ">Hf". iModIntro. move: (k t) => t'.
        iRevert (t') "Hf". iApply wpi_const_iter.
        iIntros "!>" (?) "Hwp". rewrite {1}/wpi_constF/=.
        iEval (rewrite least_fixpoint_unfold{1}/wpi_constF/=).
        case_match => //. by iMod "Hwp".
  Qed.

  Global Instance wpi_tp_proper_perm (H : iHandler Σ E) :
    Proper ((≡ₚ) ==> (=) ==> (⊣⊢)) (wpi_tp (R:=R) H).
  Proof. move => Ms1 Ms2 Hperm ?? ->. by rewrite /wpi_tp Hperm. Qed.

End wpi_tp.

Section wpi_adequate.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGS_gen hlc Σ}.

  Theorem wpi_adequate_ind (Φ : R → iProp Σ) (H : iHandler Σ E) (EH : eHandler E E R)
    (A : eHandlerAdequate H EH) t s Ms Mss M C :
    exec EH t s C →
    Ms ≡ₚ M :: Mss →
    WPi_tp Ms @ H {{Φ}} -∗
    A.(ehandler_inv) s Mss -∗
    (∀ P, M P ={∅}=∗ P t) -∗
    |={∅}=> ∃ t' s' Ms' M', ⌜C t' s'⌝ ∗
         A.(ehandler_inv) s' Ms' ∗
         bi_close (eutt eq) (λ t', (∀ P, M' P ={∅}=∗ P t')) t' ∗
         WPi_tp (M'::Ms') @ H {{Φ}}.
  Proof.
    move => Hexec HMs.
    iIntros "Hlfp".
    iRevert (t s M Mss Hexec HMs).
    iRevert (Ms) "Hlfp". iApply lfp_tp_ind.
    iIntros "!>" (Ms) "IH". iIntros (t s M Mss Hexec HMs) "Hinv Ht".
    punfold Hexec. inv Hexec; pclearbot.
    - iModIntro. iExists _, _, _, _. rewrite H1. iFrame.
      iSplit; [done|]. rewrite -H0 -itree_eta_ -HMs. iSplit; [done|].
      iApply lfp_tp_unfold. iApply (lfp_tpF_mono with "[] IH").
      iIntros "!>" (?) "[_ $]".
    - iDestruct (lfp_tpF_perm_close with "IH") as "IH"; [done|].
      iDestruct ("IH" $! 0 with "[%]") as "Hlfp" => /=. { done. }
      iDestruct (bi_mono0_mono_l _ (λ P, |={∅}=> P t)%I with "Hlfp [Ht]") as "Hlfp".
      { iIntros (Q) "HM". by iMod ("Ht" with "HM"). }
      iMod (bi_mono0_elim with "Hlfp []") as (G) "[Hwpi Hc]".
      { iIntros (??) "Hwand >HQ". iModIntro. by iApply "Hwand". }
      iMod "Hwpi". rewrite -H0. iDestruct ("Hc" $! [λ P, P _]%I with "[Hwpi]") as (??%symmetry) "[IH _]".
      { by iFrame. }
      iApply ("IH" with "[//] [%] Hinv").
      + done.
      + by iIntros (?) "$".
    - iDestruct (lfp_tpF_perm_close with "IH") as "IH"; [done|].
      iDestruct ("IH" $! 0 with "[%]") as "Hlfp" => /=. { done. }
      iDestruct (bi_mono0_mono_l _ (λ P, |={∅}=> P t)%I with "Hlfp [Ht]") as "Hlfp".
      { iIntros (Q) "HM". by iMod ("Ht" with "HM"). }
      iMod (bi_mono0_elim with "Hlfp []") as (G) "[Hwpi Hc]".
      { iIntros (? ?) "Hwand >HQ". iModIntro. by iApply "Hwand". }
      iMod "Hwpi". rewrite -H0.
      iMod (ehandler_adequate G%I with "Hwpi Hinv") as "Hwpi"; [done|].
      iDestruct "Hwpi" as (t' s' M' Ms' Msn Hexec' Hlookup) "[Htsn [Hinv [%t'' [% Hmod]]]]".
      iSpecialize ("Hc" with "Htsn").
      iDestruct "Hc" as (? Heq) "[Hc _]".
      iApply ("Hc" with "[%] [%] Hinv Hmod").
      + rewrite -H2. by pclearbot.
      + by rewrite -Heq.
  Qed.

  Theorem wpi_adequate (Φ : R → iProp Σ) (H : iHandler Σ E) (EH : eHandler E E R)
    (A : eHandlerAdequate H EH) t s C :
    exec EH t s C →
    WPi t @ H; ∅ {{Φ}} -∗
    A.(ehandler_inv) s [] -∗
    |={∅}=> ∃ t' s' Ms' M', ⌜C t' s'⌝ ∗
         A.(ehandler_inv) s' Ms' ∗
         bi_close (eutt eq) (λ t', (∀ P, M' P ={∅}=∗ P t')) t' ∗
         WPi_tp (M'::Ms') @ H {{Φ}}.
  Proof.
    iIntros (Hexec) "Hwpi Hinv".
    iApply (wpi_adequate_ind with "[Hwpi] Hinv"); [done|done| |].
    - by iApply wpi_tp_intro.
    - by iIntros (?) "$".
  Qed.
End wpi_adequate.

Section wpi_adequate_pure.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGpreS Σ}.

  Theorem wpi_adequate_pure hlc n (EH : eHandler E E R) t s C Ψ:
    exec EH t s C →
    (∀ Hinv : invGS_gen hlc Σ,
      ⊢ £ n -∗ |={⊤, ∅}=> ∃ (H : iHandler Σ E) (A : eHandlerAdequate H EH) (Φ : R → iProp Σ),
       WPi t @ H;∅ {{Φ}} ∗
       A.(ehandler_inv) s [] ∗
       (∀ t' s' Ms' M', ⌜C t' s'⌝ -∗
         A.(ehandler_inv) s' Ms' -∗
         bi_close (eutt eq) (λ t', (∀ P, M' P ={∅}=∗ P t')) t' ∗
         WPi_tp (M'::Ms') @ H {{Φ}} ={∅}=∗ ⌜Ψ⌝)) → Ψ.
  Proof.
    move => Hexec Hwp.
    eapply uPred.pure_soundness.
    eapply (step_fupdN_soundness_gen _ hlc 0 n) => ?/=.
    iIntros "Hlc". iMod (Hwp with "Hlc") as (H A Φ) "[Hwp [Hs Hc]]".
    iMod (wpi_adequate with "Hwp Hs") as (????) "[Hp [??]]" ; [done|].
    iApply ("Hc" with "[$] [$] [$]").
  Qed.
End wpi_adequate_pure.

(** * [sumEH] *)
Program Definition sumEH {E1 E2 GE R} (EH1 : eHandler E1 GE R) (EH2 : eHandler E2 GE R)
  : eHandler (E1 +' E2) GE R :=
  EHandler (EH1.(eh_state) * EH2.(eh_state))
    (prod_relation EH1.(eh_state_rel) EH2.(eh_state_rel)) (λ A e s k C,
    match e with
    | inl1 e1 => EH1 A e1 s.1 k (λ t' s', C t' (s', s.2))
    | inr1 e2 => EH2 A e2 s.2 k (λ t' s', C t' (s.1, s'))
    end
  ) _ _ _.
Next Obligation.
  move => /= ???????????? Hmono Hp. case_match; (apply: ehandler_mono; [|done]) => /= ??; apply Hmono.
Qed.
Next Obligation.
  move => ???????? /= ?? [? ?] ??? ?? Hp /=. case_match.
  - apply ehandler_proper; [done..|].
    move => ??? ???. by apply Hp.
  - apply ehandler_proper; [done..|].
    move => ??? ???. by apply Hp.
Qed.
Notation "H1 ⊕ₚ H2" := (sumEH H1 H2)
  (at level 59, right associativity) : type_scope.

Global Instance sumEH_inEH_l {GE R E1 E2 E3} `{E1 -< E2} (EH1 : eHandler E1 GE R) (EH2 : eHandler E2 GE R) (EH3 : eHandler E3 GE R) f1 f2:
  inEH EH1 EH2 f1 f2 →
  inEH EH1 (EH2 ⊕ₚ EH3) (f1 ∘ fst) (λ s1 s, (f2 s1 s.1, s.2)).
Proof. move => Hin ????? /=. by apply: Hin. Qed.
Global Instance sumEH_inEH_r {GE R E1 E2 E3} `{E1 -< E3} (EH1 : eHandler E1 GE R) (EH2 : eHandler E2 GE R) (EH3 : eHandler E3 GE R) f1 f2:
  inEH EH1 EH3 f1 f2 →
  inEH EH1 (EH2 ⊕ₚ EH3) (f1 ∘ snd) (λ s1 s, (s.1, f2 s1 s.2)).
Proof. move => Hin ????? /=. by apply: Hin. Qed.

Global Program Instance eHandlerBind_sum E1 E2 E R S
  (EH1 : eHandler E1 E R) (EH2 : eHandler E2 E R)
  (EHb1 : eHandler E1 E S) (EHb2 : eHandler E2 E S)
  `{!eHandlerBind EH1 EHb1} `{!eHandlerBind EH2 EHb2}
  :
  eHandlerBind (EH1 ⊕ₚ EH2) (EHb1 ⊕ₚ EHb2) := {|
   ebind_to_b s := (ebind_to_b s.1, ebind_to_b s.2);
   ebind_from_b s := (ebind_from_b s.1, ebind_from_b s.2);
|}.
Next Obligation.
  move => ??????????? [? ?] /=. f_equal; apply ebind_from_to_b.
Qed.
Next Obligation.
  move => ??????????? [? ?] /=. f_equal; apply ebind_to_from_b.
Qed.
Next Obligation.
  move => ????????????? [? ?] /=. by constructor; apply ebind_state_rel.
Qed.
Next Obligation.
  move => /= ????????????????? He.
  case_match; apply ebind_ehandle; by rewrite ebind_to_from_b in He.
Qed.

Section handler_adequate.
  Context {Σ : gFunctors} `{!invGS_gen hlc Σ}.

  Global Program Instance sumEH_adequate {GE R E1 E2} (H1 : iHandler Σ E1) (EH1 : eHandler E1 GE R) (H2 : iHandler Σ E2) EH2
    (A1 : eHandlerAdequate H1 EH1) (A2 : eHandlerAdequate H2 EH2) :
    eHandlerAdequate (H1 ⊕ H2) (EH1 ⊕ₚ EH2) := {|
      ehandler_inv s Ms := (∃ Ms1 Ms2, ⌜Ms ≡ₚ Ms1 ++ Ms2⌝ ∗ A1.(ehandler_inv) s.1 Ms1 ∗ A2.(ehandler_inv) s.2 Ms2)%I |}.
  Next Obligation.
    iIntros (??????????????????) "HH (%Ms1&%Ms2&%Hm&Hs1&Hs2)". simpl in *. case_match.
    - iMod (A1.(ehandler_adequate) with "[$] [$]") as (?????) "Hwp"; [done|].
      iDestruct "Hwp" as (??) "[? [? ?]]". iModIntro.
      iExists _, (_, _), _, _, _ => /=. iFrame. iSplit; [done|].
      iPureIntro; split; [|done].
      by rewrite Hm app_assoc -H4 /=.
    - iMod (A2.(ehandler_adequate) with "[$] [$]") as (?????) "Hwp"; [done|].
      iDestruct "Hwp" as (??) "[? [? ?]]". iModIntro.
      iExists _, (_, _), _, _, _ => /=. iFrame. iSplit; [done|].
      iPureIntro; split; [|done].
      by rewrite Hm (Permutation_app_comm Ms1 Ms2) app_assoc -H4 /= Permutation_app_comm.
  Qed.
  Next Obligation.
    move => ???????????? [? ?] ?? ->.
    iIntros "(%&%&%&Hs1&Hs2)". iExists _, _. iSplit; [done|].
    iSplitL "Hs1"; by iApply @ehandler_inv_proper.
  Qed.
End handler_adequate.

(** * [sumSEH] *)
Program Definition sumSEH {E1 E2} (EH1 : seHandler E1) (EH2 : seHandler E2)
  : seHandler (E1 +' E2) :=
  SEHandler (EH1.(seh_state) * EH2.(seh_state))
    (λ A e s C,
    match e with
    | inl1 e1 => sehandle EH1 A e1 s.1 (λ a s', C a (s', s.2))
    | inr1 e2 => sehandle EH2 A e2 s.2 (λ a s', C a (s.1, s'))
    end
  ) _.
Next Obligation.
  move => /= ????????? Hmono Hp. case_match; (apply: sehandler_mono; [|done]) => /= ??; apply Hmono.
Qed.
Notation "H1 ⊕ₚₛ H2" := (sumSEH H1 H2)
  (at level 59, right associativity) : type_scope.


Global Instance sumSEH_inEH_l {GE R E1 E2 E3} `{E1 -< E2} (EH1 : seHandler E1) (EH2 : seHandler E2) (EH3 : seHandler E3) f1 f2:
  inEH EH1 EH2 f1 f2 →
  inEH (GE:=GE) (R:=R) EH1 (EH2 ⊕ₚₛ EH3) (f1 ∘ fst) (λ s1 s, (f2 s1 s.1, s.2)).
Proof.
(* TODO: fix this proof *)
  move => Hin A e [s1 s2] k C /= HC.
  apply: (sehandler_mono _ _ _ _ _ _).
  2: apply Hin.
  2: apply: sehandler_mono.
  3: done.
  all: simpl.
  instantiate (1:=k).
  instantiate (1:=(λ t s, C t (s, s2))).
  done.
  done.
Qed.
Global Instance sumSEH_inEH_r {GE R E1 E2 E3} `{E1 -< E3} (EH1 : seHandler E1) (EH2 : seHandler E2) (EH3 : seHandler E3) f1 f2:
  inEH EH1 EH3 f1 f2 →
  inEH (GE:=GE) (R:=R) EH1 (EH2 ⊕ₚₛ EH3) (f1 ∘ snd) (λ s1 s, (s.1, f2 s1 s.2)).
Proof.
(* TODO: fix this proof *)
  move => Hin A e [s1 s2] k C /= HC.
  apply: (sehandler_mono _ _ _ _ _ _).
  2: apply Hin.
  2: apply: sehandler_mono.
  3: done.
  all: simpl.
  instantiate (1:=k).
  instantiate (1:=(λ t s, C t (s1, s))).
  done.
  done.
Qed.

Section handler_adequate.
  Context {Σ : gFunctors} `{!invGS_gen hlc Σ}.

  Global Program Instance sumSEH_adequate {E1 E2} (H1 : iHandler Σ E1) (EH1 : seHandler E1) (H2 : iHandler Σ E2) EH2
    (A1 : seHandlerAdequate H1 EH1) (A2 : seHandlerAdequate H2 EH2) :
    seHandlerAdequate (H1 ⊕ H2) (EH1 ⊕ₚₛ EH2) := {|
      sehandler_inv s := (A1.(sehandler_inv) s.1 ∗ A2.(sehandler_inv) s.2)%I |}.
  Next Obligation.
    iIntros (???????????????) "HH [Hs1 Hs2]". simpl in *. case_match.
    - iMod (A1.(sehandler_adequate) with "[$] [$]") as (??) "Hwp"; [done|].
      iDestruct "Hwp" as (?) "[? $]". iModIntro. iExists (_, _) => /=. by iFrame.
    - iMod (A2.(sehandler_adequate) with "[$] [$]") as (??) "Hwp"; [done|].
      iDestruct "Hwp" as (?) "[? $]". iModIntro. iExists (_, _) => /=. by iFrame.
  Qed.
End handler_adequate.


(** * [ub] *)
Program Definition ubEH : seHandler ubE :=
  SEHandler unit (λ A e s C, True) _.
Next Obligation. done. Qed.

Global Program Instance ubEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    seHandlerAdequate ubH ubEH := {| sehandler_inv s := True%I |}.
Next Obligation. move => ??????????. by iIntros (?). Qed.


Lemma exec_some_or_ub E R (EH : eHandler E E R) `{!ubE -< E} f1 f2 `{!inEH ubEH EH f1 f2} (o : option R) s C:
  (∀ x, o = Some x → C (Ret x) s) →
  exec EH (o?) s C.
Proof. move => ?. destruct o => /=; [apply exec_stop; naive_solver|]. by apply: exec_vis. Qed.

Lemma exec_assert E (EH : eHandler E E unit) `{!ubE -< E} f1 f2 `{!inEH ubEH EH f1 f2} P `{!Decision P} s C:
  (P → C (Ret tt) s) →
  exec EH (assert P) s C.
Proof. move => ?. rewrite /assert. case_decide; [apply exec_stop; naive_solver|]. by apply: exec_vis. Qed.


(** * [state] *)
Program Definition stateEH S : seHandler (stateE S) :=
  SEHandler S (λ A e s,
      match e with
      | EGetState    => λ C, C s s
      | ESetState s' => λ C, C tt s'
      end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance stateEH_adequate {Σ} `{!invGS_gen hlc Σ} S `{!stateInterp Σ S} :
    seHandlerAdequate (stateH S) (stateEH S) := {| sehandler_inv s := state_interp s |}.
Next Obligation.
  move => ??????????? HEH.
  iIntros "HH Hs". rewrite /stateH/=. case_match.
  - iMod ("HH" with "Hs") as "[$ $]". by iModIntro.
  - iMod ("HH" with "Hs") as "[$ $]". by iModIntro.
Qed.


(** * [demonic] *)
Program Definition demonicEH : seHandler demonicE :=
  SEHandler unit (λ A e s, match e with | EDemonic A => λ C, ∃ x, C x tt end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance demonicEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    seHandlerAdequate demonicH demonicEH := {| sehandler_inv s := True%I |}.
Next Obligation.
  move => ????????? HP. iIntros "Hwp _".
  rewrite /demonicH/=. case_match => /=. simplify_eq/=. destruct HP as [??].
  iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|]. iApply "Hwp".
Qed.


(** * [halt] *)
Program Definition haltEH : seHandler haltE :=
  SEHandler unit (λ A e s C, False) _.
Next Obligation. done. Qed.

Global Program Instance haltEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    seHandlerAdequate haltH haltEH := {| sehandler_inv s := True%I |}.
Next Obligation. move => ????????? HP. done. Qed.

Lemma exec_assume (P : Prop) E (EH : eHandler E E P) `{!haltE -< E} f1 f2 `{!inEH haltEH EH f1 f2} `{!Decision P} s C:
  P →
  (∀ HP, C (Ret HP) s) →
  exec EH (assume P) s C.
Proof. move => ??. rewrite /assume. case_decide; [apply exec_stop; naive_solver|done]. Qed.

(** * [later] *)
Program Definition laterEH lat : seHandler laterE :=
  SEHandler nat (λ A e s, match e with | ELater =>
     λ C, ∃ s', s = S s' ∧ C tt (if lat is Later then s' else s) end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance laterEH_adequate {Σ} `{!invGS Σ} lat :
  seHandlerAdequate (laterH lat) (laterEH lat) := {| sehandler_inv s := £ s |}.
Next Obligation.
  move => /= ?? lat ?????? HP.
  iIntros "Hp Hs". case_match.
  destruct HP as [? [??]]; subst.
  destruct lat => /=.
  - iModIntro. by iFrame.
  - rewrite lc_succ. iDestruct "Hs" as "[Hl $]". iApply (lc_fupd_elim_later with "[$]").
    iModIntro. by iFrame.
Qed.


(** * [threadpool] *)
Program Definition threadpoolEH {GE R} : eHandler threadpoolE GE R :=
  EHandler (nat * list (option (itree GE R)))
    (prod_relation (=) (Forall2 (option_Forall2 (eutt eq)))) (λ A e s,
      match e with
      | EFork => λ k C, C (k CurrentThread) (s.1, s.2 ++ [Some (k NewThread)])
      | EYield => λ k C,
          let tp' := <[s.1 := Some (k tt)]>s.2 in
          ∃ i t', tp' !! i = Some (Some t') ∧ C t' (i, <[i := None]>tp')
      | EKillThread => λ k C,
          (* No need to set s.1 to None since it is already None *)
          let tp' := s.2 in
          ∃ i t', tp' !! i = Some (Some t') ∧ C t' (i, <[i := None]>tp')
      end) _ _ _.
Next Obligation. move => ???????? Hmono /=. case_match; naive_solver. Qed.
Next Obligation.
  move => /= * [tid1 ?] [tid2 ?] [Ht Hs] ?? Hk ?? HC Hh. case_match; simplify_eq/=.
  - apply: HC; [..|done].
    + apply: Hk.
    + constructor; [done|] => /=. apply Forall2_app; [done|].
      apply Forall2_cons. split; [|done]. constructor. apply Hk.
  - move: Hh => [i [y' [ ]]].
    move: (Hs) => /Forall2_length?.
    move => /list_lookup_insert_Some[[?[??]]|[??]] ?; simplify_eq.
    + eexists i, _. rewrite list_lookup_insert. 2: lia. split; [done|].
      apply: HC; [apply Hk|..|done].
      constructor; [done|] => /=. apply Forall2_insert. 2: by constructor.
      apply Forall2_insert; [done|]. by constructor.
    + ogeneralize* Forall2_lookup_l; [done..|] => -[? [? ]]. inv 1.
      eexists i, _. rewrite list_lookup_insert_ne //. split; [done|].
      apply: HC; [done|..|done].
      constructor; [done|] => /=. apply Forall2_insert. 2: by constructor.
      apply Forall2_insert; [done|]. by constructor.
  - move: Hh => [i [y' [ ]]].
    move: (Hs) => /Forall2_length? ??.
    ogeneralize* Forall2_lookup_l; [done..|] => -[? [? ]]. inv 1.
    eexists i, _. split; [done|].
    apply: HC; [done|..|done].
    constructor; [done|] => /=. apply Forall2_insert. 2: by constructor.
    done.
Qed.

Lemma big_sepL2_omap_id_insert {Σ A B} x (l : list (option A)) (Ms : list B) (P : A → B → iProp Σ) i M:
  l !! i = Some None →
  ([∗ list] t;M∈(omap id l);Ms, P t M) -∗
  P x M -∗
  ∃ Ms', ⌜Ms' ≡ₚ M :: Ms⌝ ∗ ([∗ list] t;M∈omap id (<[i:=Some x]>l);Ms', P t M).
Proof.
  iIntros (Hi) "Hs Hp".
  erewrite <-(take_drop_middle l i). 2: done.
  rewrite omap_app. csimpl.
  iDestruct (big_sepL2_app_inv_l with "Hs") as (Ms1 Ms2 ?) "[Hs1 Hs2]". subst.
  iExists (Ms1 ++ M :: Ms2). iSplit.
  - iPureIntro. by rewrite Permutation_middle.
  - move: (Hi) => /(lookup_lt_Some _ _ _)?.
    rewrite insert_app_r_alt take_length_le // ?Nat.sub_diag/= ?omap_app; csimpl.
    2,3:lia.
    iApply (big_sepL2_app with "Hs1"). iFrame.
Qed.

Lemma big_sepL2_omap_id_delete {Σ A B} x (l : list (option A)) (Ms : list B) (P : A → B → iProp Σ) i:
  l !! i = Some (Some x) →
  ([∗ list] t;M∈(omap id l);Ms, P t M) -∗
  ∃ M Ms', ⌜Ms ≡ₚ M :: Ms'⌝ ∗ P x M ∗ ([∗ list] t;M∈omap id (<[i:=None]>l);Ms', P t M).
Proof.
  iIntros (Hi) "Hs".
  erewrite <-(take_drop_middle l i). 2: done.
  rewrite omap_app. csimpl.
  iDestruct (big_sepL2_app_inv_l with "Hs") as (Ms1 Ms2' ?) "[Hs1 Hs2]".
  iDestruct (big_sepL2_cons_inv_l with "Hs2") as (M Ms2 ?) "[Hx Hs2]".  subst.
  iExists M, (Ms1 ++ Ms2). iFrame. iSplit.
  - iPureIntro. by rewrite Permutation_middle.
  - move: (Hi) => /(lookup_lt_Some _ _ _)?.
    rewrite insert_app_r_alt take_length_le // ?Nat.sub_diag/= ?omap_app; csimpl.
    2,3:lia.
    iApply (big_sepL2_app with "Hs1"). iFrame.
Qed.

Global Program Instance threadpoolEH_adequate {Σ GE R} `{!invGS_gen hlc Σ} :
  eHandlerAdequate (GE:=GE) (R:=R) (threadpoolH) (threadpoolEH) := {|
    ehandler_inv ts Ms := (⌜ts.2 !! ts.1 = Some None⌝ ∗
     [∗ list] t;M∈(omap id ts.2);Ms,
        bi_close (eutt eq) (λ t, ⌜M = λ P, |={⊤,∅}=> P t⌝) t)%I
  |}.
Next Obligation.
  move => ??????? e s Ms C k He.
  iIntros "HH [% Hs]". rewrite /threadpoolH/=. case_match; simplify_eq/=.
  - iDestruct "HH" as "[Hc Hn]".
    iModIntro. iExists _, _, _, _,
      [λ P, P (k CurrentThread); λ P, |={⊤,∅}=> P (k NewThread)]%I => /=.
    iSplit; [done|] => /=. iFrame => /=.
    iSplit; [|iSplitL; [iSplit|]].
    + iPureIntro. f_equiv. by rewrite Permutation_cons_append.
    + iPureIntro. rewrite lookup_app_l //. by apply: lookup_lt_Some.
    + rewrite omap_app /=. iApply big_sepL2_snoc. iFrame. by iApply bi_close_intro.
    + iApply bi_close_intro. by iIntros (?) "$".
  - destruct He as (?&?&Hl&?). iMod "HH". iApply fupd_mask_intro; [done|].
    iDestruct (big_sepL2_omap_id_insert (k ()) with "Hs []") as (? Hperm1) "Hs"; [done|..].
    { iApply bi_close_intro. done. }
    iDestruct (big_sepL2_omap_id_delete with "Hs") as (?? Hperm2) "[Hx Hs]"; [done|].
    iIntros "Hmask". iExists _, _, _, _,
      [λ P, |={⊤,∅}=> P (k ())]%I => /=.
    iSplit; [done|] => /=. iFrame => /=.
    iSplit; [| iSplit].
    * iPureIntro. by rewrite -Hperm1 Hperm2.
    * iPureIntro. rewrite list_lookup_insert // insert_length.
      move: Hl => /(lookup_lt_Some _ _ _). by rewrite insert_length.
    * iDestruct "Hx" as %(?&->&->). iApply bi_close_intro. iIntros (?) "HP". by iMod "Hmask".
  - destruct He as (?&?&Hl&?). iMod "HH". iApply fupd_mask_intro; [done|].
    iDestruct (big_sepL2_omap_id_delete with "Hs") as (???) "[Hx Hs]"; [done|].
    iIntros "Hmask". iExists _, _, _, _, []%I => /=.
    iSplit; [done|] => /=. iFrame => /=.
    iSplit; [| iSplit].
    * iPureIntro. by rewrite H1.
    * iPureIntro. rewrite list_lookup_insert //. by apply: lookup_lt_Some.
    * iDestruct "Hx" as %(?&->&->). iApply bi_close_intro. iIntros (?) "HP". by iMod "Hmask".
Qed.
Next Obligation.
  move => ????? [??] [??] [Htid Hs] ? Ms ->. simplify_eq/=.
  iIntros "[%Hl HM]". iSplit.
  - iPureIntro. ogeneralize* Forall2_lookup_l; [done..|].
    move => [? [? ]]. by inv 1.
  - clear Hl. iInduction Hs as [|? ? ? ? Ho] "IH" forall (Ms); [done|].
    inv Ho; csimpl.
    + iDestruct (big_sepL2_cons_inv_l with "[$]") as (?? ->) "[Hx Hs]" => /=.
      iSplitL "Hx"; [by rewrite H|]. by iApply "IH".
    + by iApply "IH".
Qed.

(** * [tactics] *)
Lemma tac_exec_norm {E R} EH p (t : itree E R) t' s C :
  NormalizeITree p t t' →
  exec EH t' s C →
  exec EH t s C.
Proof. by move => [->]. Qed.

Ltac exec_norm :=
  notypeclasses refine (tac_exec_norm _ _ _ _ _ _ _ _); [solve_normalize_itree|].
Tactic Notation "exec_norm/=" :=
  repeat (simpl; exec_norm).

Ltac exec_bind := exec_norm/=; apply: exec_bind => /=.


(*
Inductive ordinal : Type :=
| oO | oS (n : ordinal) | oLimit (T : Type) (f : T → ordinal).

Inductive ord_le : ordinal → ordinal → Prop :=
| o_le_O n : ord_le oO n
| o_le_S_S n1 n2 : ord_le n1 n2 → ord_le (oS n1) (oS n2)
| o_le_add_l T f n : (∀ x, ord_le (f x) n) → ord_le (oLimit T f) n
| o_le_add_r T f n x : ord_le n (f x) → ord_le n (oLimit T f).

Fixpoint ord_add (o1 o2 : ordinal) : ordinal :=
  match o1 with
  | oO => o2
  | oS o' => oS (ord_add o' o2)
  | oLimit T f => oLimit T (λ x, ord_add (f x) o2)
  end.

Definition ord_lt (o1 o2 : ordinal) : Prop :=
  ord_le (oS o1) o2.

Lemma ord_lt_le_r o o1 o2 :
  ord_lt o1 o →
  ord_le o o2 →
  ord_lt o1 o2.
Admitted.

Lemma ord_lt_le_l o o1 o2 :
  ord_le o1 o →
  ord_lt o o2 →
  ord_lt o1 o2.
Admitted.

Lemma ord_add_le o1 o1' o2 o2' :
  ord_le o1 o1' →
  ord_le o2 o2' →
  ord_le (ord_add o1 o2) (ord_add o1' o2').
Proof.
  move => Hle. elim: Hle o2 o2' => /=.
  - admit.
  - constructor. naive_solver.
  - constructor. naive_solver.
  - econstructor. naive_solver.
Admitted.

Lemma ord_add_lt_l o1 o1' o2 o2' :
  ord_lt o1 o1' →
  ord_le o2 o2' →
  ord_lt (ord_add o1 o2) (ord_add o1' o2').
Admitted.

Lemma ord_lt_S o :
  ord_lt o (oS o).
Admitted.

Lemma ord_le_lt o o':
  ord_lt o o' →
  ord_le o o'.
Admitted.

Lemma ord_le_S o :
  ord_le o (oS o).
Proof. apply ord_le_lt, ord_lt_S. Qed.

Global Instance ord_le_preorder : PreOrder ord_le.
Admitted.

Lemma ord_ind (P : ordinal → Prop):
  (∀ x : ordinal, (∀ y : ordinal, ord_lt y x → P y) → P x) → ∀ a, P a.
Proof. Admitted.

Class eHandlerAdequate {Σ E GE R} (H : iHandler Σ E) (EH : eHandler E GE R)
  `{!invGS_gen hlc Σ} := {
  handler_inv : ordinal → (ordinal → itree GE R → iProp Σ) → EH.(eh_state) → iProp Σ;
  handler_adequate : ∀ A e s C k G o oi,
      EH A e s k C →
      H A e (λ a, G (o a) (k a)) (λ a, |={⊤, ∅}=> G (o a) (k a)) -∗
      handler_inv oi G s -∗
      |={∅}=> ∃ t' s' o' oi', ⌜C t' s'⌝ ∗ ⌜ord_le (ord_add o' oi') (ord_add (oAdd _ o) oi)⌝
          ∗ handler_inv oi' G s' ∗ G o' t'
}.

Section wp_itree_n.
  Context {Σ : gFunctors} {E : Type → Type} `{!invGS_gen hlc Σ}.
  Context {H : iHandler Σ E}.

  Definition wpi_mask_n {R} (n : ordinal) (M : coPset) (t : itree E R) (Φ : R → iProp Σ) : iProp Σ.
  Admitted.

  Global Instance wpi_mask_n_proper R n M :
    Proper (eqit (=) false false ==> (pointwise_relation R (⊣⊢)) ==> (⊣⊢)) (wpi_mask_n (R:=R) n M).
  Proof.
    intros t1 t2 Ht Φ1 Φ2 HΦ.
  Admitted.
End wp_itree_n.

Notation "'WPi{' n '}' t @ H ; M {{ v , Q } }" := (wpi_mask_n (H := H) n M t (λ v, Q))
  (at level 20, n, t, Q at level 200,
   format "'[hv' 'WPi{' n '}'  t  '/' @  '[' H ; M ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WPi{' n '}' t @ H ; M {{ Φ } }" := (WPi{n} t @ H; M {{ v, Φ v }})%I
  (at level 20, n, t, Φ at level 200, only parsing) : bi_scope.

Section wpi_adequate.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGS_gen hlc Σ}.

  Lemma wpi_n_vis A (e : E A) k H n (Φ : R → _) :
    WPi{n} Vis e k @ H;∅ {{ Φ }} ⊣⊢ ∃ n',
     ⌜ord_lt (oAdd _ n') n⌝ ∗ H _ e (λ a, WPi{n' a} k a @ H;∅ {{ Φ }})
            (λ a, |={⊤, ∅}=> WPi{n' a} k a @ H;∅ {{ _, False }}).
  Admitted.

  Lemma wpi_n_Tau (t : itree E R) H n (Φ : R → _) :
    WPi{n} Tau t @ H;∅ {{ Φ }} ⊣⊢ ∃ n', ⌜n = oS n'⌝ ∗ WPi{n'} t @ H;∅ {{ Φ }}.
  Admitted.

  (* TODO: Do this by having X tokens where X is the sum of the n of
  the top-most itree and the ones inside the invariant. A bit like the
  fake laters in DimSum. *)
  Theorem wpi_adequate (Φ : R → iProp Σ) (H : iHandler Σ E) (EH : eHandler E E R)
    (A : eHandlerAdequate H EH) t s C o ow oi :
    exec EH t s C →
    ord_le (ord_add ow oi) o →
    WPi{ow} t @ H;∅ {{Φ}} -∗
    A.(handler_inv) oi (λ o t, WPi{o} t @ H;∅ {{Φ}}) s -∗
    |={∅}=> ∃ t' t'' s' ow' oi', ⌜C t' s'⌝ ∗ ⌜t' ≈ t''⌝ ∗ ⌜ord_le (ord_add ow' oi') o⌝ ∗
              A.(handler_inv) oi' (λ o t, WPi{o} t @ H;∅ {{Φ}}) s' ∗ WPi{ow'} t'' @ H;∅ {{Φ}}.
  Proof.
    move => Hexec Ho.
    iIntros "Hwp Hinv".
    iInduction o as [] "IH" using ord_ind forall (t s ow oi Hexec Ho).
    punfold Hexec. inv Hexec.
    - iModIntro. iExists _, _, _, _, _. iSplit; [done|]. iFrame. by rewrite -H0 -itree_eta.
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]; simplify_eq/=.
      pclearbot.
      iDestruct (wpi_n_Tau with "Hwp") as (ow' ->) "Hwp".
      iMod ("IH" with "[%] [%] [%] Hwp Hinv") as (????????) "[??]".
      2: done. 2: done. { apply: ord_lt_le_r; [|done]. apply ord_add_lt_l; [|done]. apply ord_lt_S. }
      iModIntro. iFrame. iExists _. iSplit; [done|]. iSplit; [done|]. iPureIntro. etrans; [|done].
      etrans; [done|]. apply ord_add_le; [|done]. apply ord_le_S.
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]. 1, 2: by simplify_eq/=.
      subst. simpl in *. do 2 simplify_K.
      rewrite wpi_n_vis. iDestruct "Hwp" as (n' Hn') "Hwp".
      iMod (handler_adequate with "[Hwp] Hinv") as (????) "Hwp"; [done| |].
      + iApply (ihandler_mono with "[] [] Hwp").
        * iIntros (?) "?" => /=. done.
        * iIntros "!>" (?) ">?" => /=. iModIntro. admit.
      + iDestruct "Hwp" as (??) "[Hs Hwp]". pclearbot.
        iMod ("IH" with "[%] [%] [%] Hwp Hs") as (????????) "[??]". 2: done. 2: reflexivity.
        { apply: ord_lt_le_r; [|done]. apply: ord_lt_le_l; [done|]. by apply ord_add_lt_l. }
        iModIntro. iFrame. iExists _. iSplit; [done|]. iSplit; [done|]. iPureIntro.
        etrans; [done|]. etrans; [|done]. etrans; [done|].
        apply ord_add_le; [|done]. by apply ord_le_lt.
  Admitted.

      (* iApply ("Hwp" with "[//] Hs"). *)

    iApply (wpi_iter G with "[] Hwp [//]"); clear. { solve_proper. }
    iIntros "!>" (t Φ') "Hwp". iIntros (s Hpure) "HΦ Hs".
    punfold Hpure. inv Hpure.
    - iModIntro. iExists _, _. iFrame. iSplit; [done|]. rewrite -H0. admit.
    - pclearbot. destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]; simplify_eq/=.
      rewrite /wpiF/=. iMod "Hwp". iApply ("Hwp" with "[//] HΦ Hs").
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]. 1, 2: by simplify_eq/=.
      subst. simpl in *. do 2 simplify_K.
      rewrite /wpiF/=. iMod "Hwp".
      unfold G.
      iMod (handler_adequate with "[Hwp] Hs") as (??) "Hwp"; [done| |].
      2: {
      iDestruct "Hwp" as (??) "[Hs Hwp]". pclearbot.


  (* Cannot be sound if P is not monotone, pick P := □ G -∗ False *)
  Lemma wpi_strong_ind P t (H : iHandler Σ E) (Φ : R → iProp Σ) :
    □ (∀ t' Φ' G,
          wpiF H G t' Φ' -∗
       □ (∀ t'' Φ'', G t'' Φ'' -∗ P G t'' Φ'') -∗
         P G t' Φ') -∗
    WPi t @ H;∅ {{Φ}} -∗ ∃ G, P G t Φ.
  Admitted.

  Theorem wpi_adequate (Φ : R → iProp Σ) (H : iHandler Σ E) (EH : eHandler E E R)
    (A : eHandlerAdequate H EH) t s C :
    exec EH t s C →
    WPi t @ H;∅ {{Φ}} -∗
    ∃ G, A.(handler_inv) (λ t, G t Φ) s -∗
    |={∅}=> ∃ t' s', ⌜C t' s'⌝ ∗ A.(handler_inv) (λ t, G t Φ) s' ∗ WPi t' @ H;∅ {{Φ}}.
  Proof.
    move => Hpure. iIntros "Hwp".
    pose (P := (λ G (t : leibnizO (itree E R)) (Φ' : R -d> iPropO Σ), (∀ s,
                 ⌜exec EH t s C⌝ -∗
                 (∀ a, Φ' a -∗ Φ a) -∗
                 A.(handler_inv) (λ t, G t Φ') s -∗
                 |={∅}=> ∃ t' s', ⌜C t' s'⌝ ∗ A.(handler_inv) (λ t, G t Φ') s' ∗ WPi t' @ H;∅ {{Φ}})%I)).
    iDestruct (wpi_strong_ind P with "[] Hwp") as (G) "HG".
    2: { iExists G. unfold P. iApply "HG".  done. by iIntros. }
  Abort.
    (* iIntros "Hwp". *)
    (* move Heq:{2 3 4}n => m. have Hle: itree_n_le n m. admit. clear Heq. *)
    (* iInduction n as [] "IH" using itree_n_ind forall (m t s Hpure Hle). *)
    (* punfold Hpure. inv Hpure. *)


  (* TODO: Do this by having X tokens where X is the sum of the n of
  the top-most itree and the ones inside the invariant. A bit like the
  fake laters in DimSum. *)
  Theorem wpi_adequate (Φ : R → iProp Σ) (H : iHandler Σ E) (EH : eHandler E E R)
    (A : eHandlerAdequate H EH) t s C n :
    exec EH t s C →
    WPi{n} t @ H;∅ {{Φ}} -∗
    A.(handler_inv) (λ t, ∃ n', ⌜itree_n_lt n' n⌝ ∗ WPi{n'} t @ H;∅ {{Φ}}) s -∗
    |={∅}=> ∃ t' t'' s', ⌜C t' s'⌝ ∗ ⌜t' ≈ t''⌝ ∗ A.(handler_inv) (λ t, ∃ n', ⌜itree_n_lt n' n⌝ ∗ WPi{n'} t @ H;∅ {{Φ}}) s' ∗ WPi{n} t'' @ H;∅ {{Φ}}.
  Proof.
    move => Hpure.
    iIntros "Hwp Hinv".
    move Heq:{2 3 4}n => m. have Hle: itree_n_le n m. admit. clear Heq.
    iInduction n as [] "IH" using itree_n_ind forall (m t s Hpure Hle).
    punfold Hpure. inv Hpure.
    - iModIntro. iExists _, _, _. iSplit; [done|]. iFrame.
      admit.
(* by rewrite -H0 -itree_eta. *)
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]; simplify_eq/=.
      pclearbot.
      iApply ("IH" with "[%] [%] [%] [Hwp] [Hinv]"). 2: done. all: admit.
      (* rewrite /wpiF/=. iMod "Hwp". iApply ("Hwp" with "[//] HΦ HG Hs"). *)
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]. 1, 2: by simplify_eq/=.
      subst. simpl in *. do 2 simplify_K.
      rewrite wpi_n_vis. iDestruct "Hwp" as (n' Hn') "Hwp".
      iMod (handler_adequate with "[Hwp] Hinv") as (??) "Hwp"; [done| |].
      + iApply (ihandler_mono with "[] [] Hwp").
        * iIntros (?) "?" => /=. iExists _. iFrame. iPureIntro. admit.
        * iIntros "!>" (?) ">?" => /=. iModIntro. iExists _. admit.
      + iDestruct "Hwp" as (?) "[Hs [%n'' [% Hwp]]]". pclearbot.
        iApply ("IH" with "[%] [//] [%] Hwp Hs"). 2:
      (* iApply ("Hwp" with "[//] Hs"). *)

    iApply (wpi_iter G with "[] Hwp [//]"); clear. { solve_proper. }
    iIntros "!>" (t Φ') "Hwp". iIntros (s Hpure) "HΦ Hs".
    punfold Hpure. inv Hpure.
    - iModIntro. iExists _, _. iFrame. iSplit; [done|]. rewrite -H0. admit.
    - pclearbot. destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]; simplify_eq/=.
      rewrite /wpiF/=. iMod "Hwp". iApply ("Hwp" with "[//] HΦ Hs").
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]. 1, 2: by simplify_eq/=.
      subst. simpl in *. do 2 simplify_K.
      rewrite /wpiF/=. iMod "Hwp".
      unfold G.
      iMod (handler_adequate with "[Hwp] Hs") as (??) "Hwp"; [done| |].
      2: {
      iDestruct "Hwp" as (??) "[Hs Hwp]". pclearbot.

    pose (G := (λ (t : leibnizO (itree E R)) (Φ' : R -d> iPropO Σ), (∀ s G' G'',
                 ⌜exec EH t s C⌝ -∗
                 (∀ a, Φ' a -∗ Φ a) -∗
                 □ (∀ t, G'' t Φ -∗ G' t) -∗
                 (∀ t s, ⌜exec EH t s C⌝ -∗ handler_inv G' s -∗ G' t -∗
                    |={∅}=> ∃ t' s', ⌜C t' s'⌝ ∗ A.(handler_inv) G' s' ∗
                                                     WPi t' @ H;∅ {{Φ}}) -∗
                 A.(handler_inv) G' s -∗
                 |={∅}=> ∃ t' s', ⌜C t' s'⌝ ∗ A.(handler_inv) G' s' ∗ WPi t' @ H;∅ {{Φ}})%I)).
    iIntros "Hwp".
    iExists (λ t, G t Φ).
    iApply (wpi_iter G with "[] Hwp [//]"); clear. { solve_proper. }
    2: by iIntros.
    2: admit.
    2: { unfold G at 2.
    iIntros "!>" (t Φ') "Hwp". iIntros (s G' G'' Hpure) "HΦ #HG Hs".
    punfold Hpure. inv Hpure.
    - iModIntro. iExists _, _. iFrame. iSplit; [done|]. rewrite -H0. admit.
    - pclearbot. destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]; simplify_eq/=.
      rewrite /wpiF/=. iMod "Hwp". iApply ("Hwp" with "[//] HΦ HG Hs").
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]. 1, 2: by simplify_eq/=.
      subst. simpl in *. do 2 simplify_K.
      rewrite /wpiF/=. iMod "Hwp".
      iMod (handler_adequate with "[Hwp] Hs") as (??) "Hwp"; [done| |].
      2: { simpl.
      iDestruct "Hwp" as (??) "[Hs Hwp]". pclearbot.
      (* iApply ("Hwp" with "[//] Hs"). *)

    iApply (wpi_iter G with "[] Hwp [//]"); clear. { solve_proper. }
    iIntros "!>" (t Φ') "Hwp". iIntros (s Hpure) "HΦ Hs".
    punfold Hpure. inv Hpure.
    - iModIntro. iExists _, _. iFrame. iSplit; [done|]. rewrite -H0. admit.
    - pclearbot. destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]; simplify_eq/=.
      rewrite /wpiF/=. iMod "Hwp". iApply ("Hwp" with "[//] HΦ Hs").
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]. 1, 2: by simplify_eq/=.
      subst. simpl in *. do 2 simplify_K.
      rewrite /wpiF/=. iMod "Hwp".
      unfold G.
      iMod (handler_adequate with "[Hwp] Hs") as (??) "Hwp"; [done| |].
      2: {
      iDestruct "Hwp" as (??) "[Hs Hwp]". pclearbot.
      (* iApply ("Hwp" with "[//] Hs"). *)
      admit.
  Admitted.

End wpi_adequate.

Program Definition threadpoolEH GE R : eHandler threadpoolE GE R :=
  EHandler (nat * list (option (itree GE R))) (λ A e s,
      match e with
      | EFork => λ k C, C CurrentThread (s.1, s.2 ++ [Some (k NewThread)]) (k CurrentThread)
      | EYield => λ k C,
          let tp' := <[s.1 := Some (k tt)]>s.2 in
          ∃ i t', tp' !! i = Some (Some t') ∧ C tt (i, tp') t'
      | EKillThread => λ k C,
          let tp' := <[s.1 := None]>s.2 in
          ∃ i t', tp' !! i = Some (Some t') ∧ C _ (i, tp') t'
      end) _.
Next Obligation. Admitted.
Next Obligation. move => /= *. Admitted.


Section handler_adequate.
  Context {Σ : gFunctors} `{!invGS_gen hlc Σ}.

  Global Program Instance sumEH_adequate {E1 E2} (H1 : iHandler Σ E1) EH1 (H2 : iHandler Σ E2) EH2
    (A1 : eHandlerAdequate H1 EH1) (A2 : eHandlerAdequate H2 EH2) :
    eHandlerAdequate (H1 ⊕ H2) (EH1 ⊕ₚ EH2) := {|
      handler_inv s := (A1.(handler_inv) s.1 ∗ A2.(handler_inv) s.2)%I |}.
  Next Obligation.
    iIntros (???????????????) "HH [Hs1 Hs2]". simpl in *. case_match.
    - iMod (A1.(handler_adequate) with "[$] [$]") as (??) "Hwp"; [done|].
      iDestruct "Hwp" as (?) "[? $]". iModIntro. iExists (_, _) => /=. by iFrame.
    - iMod (A2.(handler_adequate) with "[$] [$]") as (??) "Hwp"; [done|].
      iDestruct "Hwp" as (?) "[? $]". iModIntro. iExists (_, _) => /=. by iFrame.
  Qed.
End handler_adequate.

Program Definition ubEH : eHandler ubE :=
  EHandler unit (λ A e s C, True) _.
Next Obligation. done. Qed.

Global Program Instance ubEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    eHandlerAdequate ubH ubEH := {| handler_inv s := True%I |}.
Next Obligation. move => ??????????. by iIntros (?). Qed.


Program Definition stateEH S : eHandler (stateE S) :=
  EHandler S (λ A e s,
      match e with
      | EGetState    => λ C, C s s
      | ESetState s' => λ C, C tt s'
      end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance stateEH_adequate {Σ} `{!invGS_gen hlc Σ} S `{!stateInterp Σ S} :
    eHandlerAdequate (stateH S) (stateEH S) := {| handler_inv s := state_interp s |}.
Next Obligation.
  move => ??????????? HEH.
  iIntros "HH Hs". rewrite /stateH/=. case_match.
  - iMod ("HH" with "Hs") as "[$ $]". by iModIntro.
  - iMod ("HH" with "Hs") as "[$ $]". by iModIntro.
Qed.


Program Definition demonicEH : eHandler demonicE :=
  EHandler unit (λ A e s, match e with | EDemonic A => λ C, ∃ x, C x tt end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance demonicEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    eHandlerAdequate demonicH demonicEH := {| handler_inv s := True%I |}.
Next Obligation.
  move => ????????? HP. iIntros "Hwp _".
  rewrite /demonicH/=. case_match => /=. simplify_eq/=. destruct HP as [??].
  iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|]. iApply "Hwp".
Qed.


Program Definition haltEH : eHandler haltE :=
  EHandler unit (λ A e s C, False) _.
Next Obligation. done. Qed.

Global Program Instance haltEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    eHandlerAdequate haltH haltEH := {| handler_inv s := True%I |}.
Next Obligation. move => ????????? HP. done. Qed.


Program Definition laterEH lat : eHandler laterE :=
  EHandler nat (λ A e s, match e with | ELater =>
     λ C, ∃ s', s = S s' ∧ C tt (if lat is Later then s' else s) end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance laterEH_adequate {Σ} `{!invGS Σ} lat :
  eHandlerAdequate (laterH lat) (laterEH lat) := {| handler_inv s := £ s |}.
Next Obligation.
  move => /= ?? lat ?????? HP.
  iIntros "Hp Hs". case_match.
  destruct HP as [? [??]]; subst.
  destruct lat => /=.
  - iModIntro. by iFrame.
  - rewrite lc_succ. iDestruct "Hs" as "[Hl $]". iApply (lc_fupd_elim_later with "[$]").
    iModIntro. by iFrame.
Qed.

(* Program Definition threadpoolEH E R (EH : eHandler E) : eHandler (threadpoolE +' E) := *)
(*   EHandler (list ( R) * EH.(eh_state)) (λ A e s,  *)
(*       match e with *)
(*       | inl1 e =>  *)
(*           match e with *)
(*           | EFork => λ C, C CurrentThread (s.1 ++ [_], s.2) *)
(*           | EYield => λ C, _ *)
(*           | EKillThread => λ C, _ *)
(*           end *)
(*       | inr1 e => λ C, EH A e s.2 (λ a s', C a (s.1, s')) *)
(*       end) _. *)
(* Next Obligation. move => /= *. case_match; naive_solver. Qed. *)

(* Global Program Instance laterEH_adequate {Σ} `{!invGS Σ} lat : *)
(*   eHandlerAdequate (laterH lat) (laterEH lat) := {| handler_inv s := £ s |}. *)
(* Next Obligation. *)

(* Program Definition threadpoolEH E R (EH : eHandler E) : eHandler (threadpoolE +' E) := *)
(*   EHandler (list (option (itree (threadpoolE +' E) R)) * EH.(eh_state)) (λ A e s,  *)
(*       match e with *)
(*       | inl1 e =>  *)
(*           match e with *)
(*           | EFork => λ C, C CurrentThread (s.1 ++ [_], s.2) *)
(*           | EYield => λ C, _ *)
(*           | EKillThread => λ C, _ *)
(*           end *)
(*       | inr1 e => λ C, EH A e s.2 (λ a s', C a (s.1, s')) *)
(*       end) _. *)
(* Next Obligation. move => /= *. case_match; naive_solver. Qed. *)

(* Global Program Instance laterEH_adequate {Σ} `{!invGS Σ} lat : *)
(*   eHandlerAdequate (laterH lat) (laterEH lat) := {| handler_inv s := £ s |}. *)
(* Next Obligation. *)
*)
