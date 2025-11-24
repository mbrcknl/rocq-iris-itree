From ITree Require Import ITree.
From ITree Require Import Eqit.
From ITree Require Import TranslateFacts InterpFacts RecursionFacts.
From Paco Require Import paco.
From iris.bi.lib Require Import fixpoint_mono.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import invariants.
From iris.itree Require Import itree wpi handler.

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

(* se_to_eHandler does not satisfy the uniform inheritance condition
since seHandler does not restrict GE and R. The coercion seems to
work nevertheless. *)
Local Set Warnings "-uniform-inheritance".
Coercion se_to_eHandler : seHandler >-> eHandler.
Local Set Warnings "uniform-inheritance".


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
(* TODO: unbundle eh_state such that these conversion functions become unnecessary? *)
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
    (A : eHandlerAdequate H EH) t s C m :
    exec EH t s C →
    WPi t @ H; m {{Φ}} -∗
    A.(ehandler_inv) s [] -∗
    |={m, ∅}=> ∃ t' s' Ms' M', ⌜C t' s'⌝ ∗
         A.(ehandler_inv) s' Ms' ∗
         bi_close (eutt eq) (λ t', (∀ P, M' P ={∅}=∗ P t')) t' ∗
         WPi_tp (M'::Ms') @ H {{ v, |={∅,m}=> Φ v}}.
  Proof.
    iIntros (Hexec) "Hwpi Hinv". rewrite -wpi_clear_mask. iMod "Hwpi".
    iApply (wpi_adequate_ind with "[Hwpi] Hinv"); [done|done| |].
    - by iApply wpi_tp_intro.
    - by iIntros (?) "$".
  Qed.
End wpi_adequate.

Section wpi_adequate_pure.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGpreS Σ}.

  Theorem wpi_adequate_pure hlc n m (EH : eHandler E E R) t s C Ψ:
    exec EH t s C →
    (∀ Hinv : invGS_gen hlc Σ,
      ⊢ £ n -∗ |={⊤, m}=> ∃ (H : iHandler Σ E) (A : eHandlerAdequate H EH) (Φ : R → iProp Σ),
       WPi t @ H;m {{Φ}} ∗
       A.(ehandler_inv) s [] ∗
       (∀ t' s' Ms' M', ⌜C t' s'⌝ -∗
         A.(ehandler_inv) s' Ms' -∗
         bi_close (eutt eq) (λ t', (∀ P, M' P ={∅}=∗ P t')) t' ∗
         WPi_tp (M'::Ms') @ H {{v, |={∅,m}=> Φ v}} ={∅}=∗ ⌜Ψ⌝)) → Ψ.
  Proof.
    move => Hexec Hwp.
    eapply (pure_soundness (PROP:=uPredI _)).
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
Notation "H1 ⊕ₑ H2" := (sumEH H1 H2)
  (at level 59, right associativity) : type_scope.

Global Instance sumEH_inEH_l {GE R E1 E2 E3} `{E1 -< E2} (EH1 : eHandler E1 GE R) (EH2 : eHandler E2 GE R) (EH3 : eHandler E3 GE R) f1 f2:
  inEH EH1 EH2 f1 f2 →
  inEH EH1 (EH2 ⊕ₑ EH3) (f1 ∘ fst) (λ s1 s, (f2 s1 s.1, s.2)).
Proof. move => Hin ????? /=. by apply: Hin. Qed.
Global Instance sumEH_inEH_r {GE R E1 E2 E3} `{E1 -< E3} (EH1 : eHandler E1 GE R) (EH2 : eHandler E2 GE R) (EH3 : eHandler E3 GE R) f1 f2:
  inEH EH1 EH3 f1 f2 →
  inEH EH1 (EH2 ⊕ₑ EH3) (f1 ∘ snd) (λ s1 s, (s.1, f2 s1 s.2)).
Proof. move => Hin ????? /=. by apply: Hin. Qed.

Global Program Instance eHandlerBind_sum E1 E2 E R S
  (EH1 : eHandler E1 E R) (EH2 : eHandler E2 E R)
  (EHb1 : eHandler E1 E S) (EHb2 : eHandler E2 E S)
  `{!eHandlerBind EH1 EHb1} `{!eHandlerBind EH2 EHb2}
  :
  eHandlerBind (EH1 ⊕ₑ EH2) (EHb1 ⊕ₑ EHb2) := {|
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
    eHandlerAdequate (H1 ⊕ H2) (EH1 ⊕ₑ EH2) := {|
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
Notation "H1 ⊕ₑₛ H2" := (sumSEH H1 H2)
  (at level 59, right associativity) : type_scope.


Global Instance sumSEH_inEH_l {GE R E1 E2 E3} `{E1 -< E2} (EH1 : seHandler E1) (EH2 : seHandler E2) (EH3 : seHandler E3) f1 f2:
  inEH EH1 EH2 f1 f2 →
  inEH (GE:=GE) (R:=R) EH1 (EH2 ⊕ₑₛ EH3) (f1 ∘ fst) (λ s1 s, (f2 s1 s.1, s.2)).
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
  inEH (GE:=GE) (R:=R) EH1 (EH2 ⊕ₑₛ EH3) (f1 ∘ snd) (λ s1 s, (s.1, f2 s1 s.2)).
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
    seHandlerAdequate (H1 ⊕ H2) (EH1 ⊕ₑₛ EH2) := {|
      sehandler_inv s := (A1.(sehandler_inv) s.1 ∗ A2.(sehandler_inv) s.2)%I |}.
  Next Obligation.
    iIntros (???????????????) "HH [Hs1 Hs2]". simpl in *. case_match.
    - iMod (A1.(sehandler_adequate) with "[$] [$]") as (??) "Hwp"; [done|].
      iDestruct "Hwp" as (?) "[? $]". iModIntro. iExists (_, _) => /=. by iFrame.
    - iMod (A2.(sehandler_adequate) with "[$] [$]") as (??) "Hwp"; [done|].
      iDestruct "Hwp" as (?) "[? $]". iModIntro. iExists (_, _) => /=. by iFrame.
  Qed.
End handler_adequate.

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
