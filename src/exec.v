From ITree Require Import ITree.
From ITree Require Import Eqit.
From ITree Require Import TranslateFacts InterpFacts RecursionFacts.
From Paco Require Import paco.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import adequacy.
From iris.itree Require Import itree wpi handler ub state choice halt later.
From iris.itree.threadpool Require Import handler.

Record eHandler (E : Type → Type) := EHandler {
  eh_state : Type;
  ehandle :> ∀ A, E A → eh_state → (A → eh_state → Prop) → Prop;
  ehandler_mono : ∀ A e s C C',
    (∀ a s', C a s' → C' a s') →
    ehandle A e s C → ehandle A e s C';
}.
Arguments EHandler {_} _ _ _.
Arguments eh_state {_}.

Class inEH {E1 E2} `{!E1 -< E2} (EH1 : eHandler E1) (EH2 : eHandler E2)
  (f1 : EH2.(eh_state) → EH1.(eh_state)) (f2 : EH1.(eh_state) → EH2.(eh_state) → EH2.(eh_state)) :=
  is_inEH : ∀ A e s2 C, EH1 A e (f1 s2) (λ a s1', C a (f2 s1' s2)) → EH2 A (subevent A e) s2 C.
Global Hint Mode inEH + + ! - ! - - : typeclass_instances.

(* TODO: Put this somewhere more global? *)
Local Unset Program Cases.
Program Definition sumEH {E1 E2} (EH1 : eHandler E1) (EH2 : eHandler E2)
  : eHandler (E1 +' E2) :=
  EHandler (EH1.(eh_state) * EH2.(eh_state)) (λ A e s C,
    match e with
    | inl1 e1 => EH1 A e1 s.1 (λ a s', C a (s', s.2))
    | inr1 e2 => EH2 A e2 s.2 (λ a s', C a (s.1, s'))
    end
  ) _.
Next Obligation.
  move => /= ????????? Hmono Hp. case_match; (apply: ehandler_mono; [|done]) => /= ??; apply Hmono.
Qed.
Notation "H1 ⊕ₚ H2" := (sumEH H1 H2)
  (at level 59, right associativity) : type_scope.

Global Instance inEH_reflexivity {E} (EH : eHandler E) :
  inEH EH EH id (λ x _, x).
Proof. move => ?????. done. Qed.

Global Instance sumEH_inEH_l {E1 E2 E3} `{E1 -< E2} (EH1 : eHandler E1) (EH2 : eHandler E2) (EH3 : eHandler E3) f1 f2:
  inEH EH1 EH2 f1 f2 →
  inEH EH1 (EH2 ⊕ₚ EH3) (f1 ∘ fst) (λ s1 s, (f2 s1 s.1, s.2)).
Proof. move => Hin ????? /=. by apply Hin. Qed.
Global Instance sumEH_inEH_r {E1 E2 E3} `{E1 -< E3} (EH1 : eHandler E1) (EH2 : eHandler E2) (EH3 : eHandler E3) f1 f2:
  inEH EH1 EH3 f1 f2 →
  inEH EH1 (EH2 ⊕ₚ EH3) (f1 ∘ snd) (λ s1 s, (s.1, f2 s1 s.2)).
Proof. move => Hin ????? /=. by apply Hin. Qed.

Section exec.
  Context {E : Type → Type} {R : Type}.
  Context (EH : eHandler E).

  Variant execF
    (exec : itree E R → EH.(eh_state) → (itree E R → EH.(eh_state) → Prop) → Prop)
    : itree' E R
    → EH.(eh_state)
    → (itree E R → EH.(eh_state) → Prop)
    → Prop :=
  | ExecStop s t C t':
    go t ≈ t' →
    C t' s →
    execF exec t s C
  | ExecTau s t C :
    exec t s C →
    execF exec (TauF t) s C
  | ExecVis s A e k C :
    EH A e s (λ a s', exec (k a) s' C) →
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
    constructor. apply: ehandler_mono; [|done]. eauto with iris_itree.
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

  Global Instance exec_proper_unilateral b1 b2 :
    Proper (eqit (=) b1 b2 ==> (=) ==> (=) ==> impl) exec.
  Proof.
    intros t1 t2 Ht s ? <- C ? <- Hwpi.
    have {}Ht: t1 ≈ t2. { apply: eqit_mon; [..|by apply Ht]; naive_solver. }
    move: t1 t2 s Ht Hwpi.
    pcofix CIH.
    move => t1 t2 s Ht Hwpi.
    punfold Ht. punfold Hwpi.
    rewrite (itree_eta_ t1) in Hwpi. rewrite (itree_eta_ t2).
    elim: Ht Hwpi => //.
    - move => ??? Hwpi. inv Hwpi. pfold. by apply: ExecStop.
    - move => ?? REL Hwpi. pclearbot. inv Hwpi.
      + pfold. apply: ExecStop; [|done]. rewrite -H /= eutt_Tau. done.
      + pfold. apply: ExecTau. right. eapply CIH; [done| ]. by destruct H0.
    - move => ?? k1 k2 REL Hwpi.
      inv Hwpi.
      + pfold. apply: ExecStop; [|done]. symmetry. rewrite -H /=.
        pfold. by econstructor.
      + simplify_K. pfold. apply: ExecVis. apply: ehandler_mono; [|done].
        move => /= ?? [?|//]. right. eapply CIH; [|done]. by edestruct REL.
    - move => ???? IH Hwpi. apply IH. inv Hwpi.
      + apply: ExecStop; [|done]. by rewrite /= -H /= tau_eutt -itree_eta_.
      + destruct H0 => //. punfold H.
    - move => ???? IH Hwpi. pfold. apply: ExecTau. left.
      rewrite -itree_eta_ in IH. by apply IH.
  Qed.

  Global Instance exec_proper b1 b2 :
    Proper (eqit (=) b1 b2 ==> (=) ==> (=) ==> (↔)) exec.
  Proof.
    intros t1 t2 Ht ?? -> ?? ->.
    have {}Ht: t1 ≈ t2. { apply: eqit_mon; [..|by apply Ht]; naive_solver. }
    by split; rewrite -Ht.
  Qed.

  Lemma exec_dup t s C :
    exec t s (λ t' s', exec t' s' C) →
    exec t s C.
  Proof.
    revert t s. pcofix CIH.
    move => t s He. punfold He.
    inv He.
    - rewrite -H -itree_eta_ in H0. by eapply paco3_mon.
    - rewrite (itree_eta_ t) -H. pfold. apply ExecTau. pclearbot.
      right. by apply CIH.
    - rewrite (itree_eta_ t) -H. pfold. apply ExecVis.
      apply: ehandler_mono; [|done]. move => /= ???. pclearbot.
      right. by apply CIH.
  Qed.

End exec.
Global Hint Resolve exec__mono : paco.

Section exec.
  Lemma exec_bind_post E R S EH (t : itree E S) s (k : S → itree E R) C :
    exec EH t s (λ t' s', C (ITree.bind t' k) s') →
    exec EH (ITree.bind t k) s C.
  Proof.
    revert t s. pcofix CIH.
    move => t s He. punfold He.
    inv He.
    - rewrite -itree_eta_ in H. pfold. apply: ExecStop; [|done].
      by rewrite -H -itree_eta_.
    - rewrite (itree_eta_ t) -H. pfold. rewrite bind_tau. apply ExecTau. right. apply CIH. by pclearbot.
    - rewrite (itree_eta_ t) -H. pfold. rewrite bind_vis. apply ExecVis.
      apply: ehandler_mono; [|done] => ?? /= ?. right. apply CIH. by pclearbot.
  Qed.

  Lemma exec_bind E R S EH (t : itree E S) s (k : S → itree E R) C :
    exec EH t s (λ t' s', exec EH (ITree.bind t' k) s' C) →
    exec EH (ITree.bind t k) s C.
  Proof. move => ?. by apply exec_dup, exec_bind_post. Qed.

  Lemma exec_stop E R EH (t : itree E R) s C :
    C t s →
    exec EH t s C.
  Proof. move => ?. pfold. apply: ExecStop; [|done]. by rewrite -itree_eta_. Qed.

  Lemma exec_vis A E1 E R (e : E1 A) `{!E1 -< E} (EH : eHandler E) EH1 (k : A → itree E R) f1 f2 `{!inEH EH1 EH f1 f2} s C :
    EH1 A e (f1 s) (λ a s', exec EH (k a) (f2 s' s) C) →
    exec EH (vis e k) s C.
  Proof.
    move => H1. pfold. apply: ExecVis. apply is_inEH. apply: ehandler_mono; [|done].
    move => /= ???. by left.
  Qed.

  Lemma exec_trigger A E1 E (e : E1 A) `{!E1 -< E} (EH : eHandler E) EH1 f1 f2 `{!inEH EH1 EH f1 f2} s C :
    EH1 A e (f1 s) (λ a s', C (Ret a) (f2 s' s)) →
    exec EH (trigger e) s C.
  Proof.
    move => ?. rewrite /ITree.trigger. apply: exec_vis. apply: ehandler_mono; [|done].
    move => /= ???. by apply exec_stop.
  Qed.
End exec.

Class HandlerAdequate {Σ E} (H : iHandler Σ E) (EH : eHandler E) `{!invGS_gen hlc Σ} := {
  handler_inv : EH.(eh_state) → iProp Σ;
  handler_adequate : ∀ A e s C Φ1 Φ2,
      EH A e s C →
      H A e Φ1 Φ2 -∗
      handler_inv s -∗
      |={∅}=> ∃ a s', ⌜C a s'⌝ ∗ handler_inv s' ∗ Φ1 a
}.

Section wpi_adequate.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGS_gen hlc Σ}.

  Theorem wpi_adequate (H : iHandler Σ E) (EH : eHandler E) (A : HandlerAdequate H EH) t s C (Φ : R → iProp Σ) :
    exec EH t s C →
    WPi t @ H;∅ {{Φ}} -∗
    A.(handler_inv) s -∗
    |={∅}=> ∃ t' s', ⌜C t' s'⌝ ∗ A.(handler_inv) s' ∗ WPi t' @ H;∅ {{Φ}}.
  Proof.
    move => Hpure.
    pose (G := (λ (t : leibnizO (itree E R)) (Φ : R -d> iPropO Σ), (∀ s,
                 ⌜exec EH t s C⌝ -∗
                 A.(handler_inv) s -∗
                 |={∅}=> ∃ t' s', ⌜C t' s'⌝ ∗ A.(handler_inv) s' ∗ WPi t' @ H;∅ {{Φ}})%I)).
    iIntros "Hwp".
    iApply (wpi_ind G with "[] Hwp [//]"); clear. { solve_proper. }
    iIntros "!>" (t Φ) "Hwp". iIntros (s Hpure) "Hs".
    punfold Hpure. inv Hpure.
    - iModIntro. iExists _, _. iFrame. iSplit; [done|]. rewrite -H0 -itree_eta_.
      rewrite wpi_unfold. iApply (wpiF_mono with "[] Hwp").
      by iIntros "!>" (??) "[_ $]".
    - pclearbot. destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]; simplify_eq/=.
      rewrite /wpiF/=. iMod "Hwp". iApply ("Hwp" with "[//] Hs").
    - destruct (itree_match t) as [[??]|[[??]|[?[?[??]]]]]. 1, 2: by simplify_eq/=.
      subst. simpl in *. do 2 simplify_K.
      rewrite /wpiF/=. iMod "Hwp".
      iMod (handler_adequate with "Hwp Hs") as (??) "Hwp"; [done|].
      iDestruct "Hwp" as (?) "[Hs Hwp]". pclearbot.
      iApply ("Hwp" with "[//] Hs").
  Qed.

End wpi_adequate.

Section wpi_adequate_pure.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGpreS Σ}.

  Theorem wpi_adequate_pure hlc n (EH : eHandler E) t s C Ψ:
    exec EH t s C →
    (∀ Hinv : invGS_gen hlc Σ,
      ⊢ £ n -∗ |={⊤, ∅}=> ∃ (H : iHandler Σ E) (A : HandlerAdequate H EH) (Φ : R → iProp Σ),
       WPi t @ H;∅ {{Φ}} ∗
       A.(handler_inv) s ∗
       (∀ t' s', ⌜C t' s'⌝ -∗ A.(handler_inv) s' -∗ WPi t' @ H;∅ {{Φ}} ={∅}=∗ ⌜Ψ⌝)) → Ψ.
  Proof.
    move => Hexec Hwp.
    eapply uPred.pure_soundness.
    eapply (step_fupdN_soundness_gen _ hlc 0 n) => ?/=.
    iIntros "Hlc". iMod (Hwp with "Hlc") as (H A Φ) "[Hwp [Hs Hc]]".
    iMod (wpi_adequate with "Hwp Hs") as (??) "[Hp [??]]"; [done|].
    iApply ("Hc" with "[$] [$] [$]").
  Qed.
End wpi_adequate_pure.

Section handler_adequate.
  Context {Σ : gFunctors} `{!invGS_gen hlc Σ}.

  Global Program Instance sumEH_adequate {E1 E2} (H1 : iHandler Σ E1) EH1 (H2 : iHandler Σ E2) EH2
    (A1 : HandlerAdequate H1 EH1) (A2 : HandlerAdequate H2 EH2) :
    HandlerAdequate (H1 ⊕ H2) (EH1 ⊕ₚ EH2) := {|
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
    HandlerAdequate ubH ubEH := {| handler_inv s := True%I |}.
Next Obligation. move => ??????????. by iIntros (?). Qed.

Lemma exec_some_or_ub E R (EH : eHandler E) `{!ubE -< E} f1 f2 `{!inEH ubEH EH f1 f2} (o : option R) s C:
  (∀ x, o = Some x → C (Ret x) s) →
  exec EH (o?) s C.
Proof. move => ?. destruct o => /=; [apply exec_stop; naive_solver|]. by apply: exec_vis. Qed.

Lemma exec_assert E (EH : eHandler E) `{!ubE -< E} f1 f2 `{!inEH ubEH EH f1 f2} P `{!Decision P} s C:
  (P → C (Ret tt) s) →
  exec EH (assert P) s C.
Proof. move => ?. rewrite /assert. case_decide; [apply exec_stop; naive_solver|]. by apply: exec_vis. Qed.

Program Definition stateEH S : eHandler (stateE S) :=
  EHandler S (λ A e s,
      match e with
      | EGetState    => λ C, C s s
      | ESetState s' => λ C, C tt s'
      end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance stateEH_adequate {Σ} `{!invGS_gen hlc Σ} S `{!stateInterp Σ S} :
    HandlerAdequate (stateH S) (stateEH S) := {| handler_inv s := state_interp s |}.
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
    HandlerAdequate demonicH demonicEH := {| handler_inv s := True%I |}.
Next Obligation.
  move => ????????? HP. iIntros "Hwp _".
  rewrite /demonicH/=. case_match => /=. simplify_eq/=. destruct HP as [??].
  iModIntro. iExists _, _. iSplit; [done|]. iSplit; [done|]. iApply "Hwp".
Qed.


Program Definition haltEH : eHandler haltE :=
  EHandler unit (λ A e s C, False) _.
Next Obligation. done. Qed.

Global Program Instance haltEH_adequate {Σ} `{!invGS_gen hlc Σ} :
    HandlerAdequate haltH haltEH := {| handler_inv s := True%I |}.
Next Obligation. move => ????????? HP. done. Qed.

Lemma exec_assume E (EH : eHandler E) `{!haltE -< E} f1 f2 `{!inEH haltEH EH f1 f2} P `{!Decision P} s C:
  P →
  (∀ HP, C (Ret HP) s) →
  exec EH (assume P) s C.
Proof. move => ??. rewrite /assume. case_decide; [apply exec_stop; naive_solver|done]. Qed.


Program Definition laterEH lat : eHandler laterE :=
  EHandler nat (λ A e s, match e with | ELater =>
     λ C, ∃ s', s = S s' ∧ C tt (if lat is Later then s' else s) end) _.
Next Obligation. move => /= *. case_match; naive_solver. Qed.

Global Program Instance laterEH_adequate {Σ} `{!invGS Σ} lat :
  HandlerAdequate (laterH lat) (laterEH lat) := {| handler_inv s := £ s |}.
Next Obligation.
  move => /= ?? lat ?????? HP.
  iIntros "Hp Hs". case_match.
  destruct HP as [? [??]]; subst.
  destruct lat => /=.
  - iModIntro. by iFrame.
  - rewrite lc_succ. iDestruct "Hs" as "[Hl $]". iApply (lc_fupd_elim_later with "[$]").
    iModIntro. by iFrame.
Qed.

Lemma tac_exec_norm {E R} EH p (t : itree E R) t' s C :
  NormalizeITree p t t' →
  exec EH t' s C →
  exec EH t s C.
Proof. by move => [->]. Qed.

Ltac exec_norm :=
  notypeclasses refine (tac_exec_norm _ _ _ _ _ _ _ _); [solve_normalize_itree|].
Tactic Notation "exec_norm/=" :=
  repeat (simpl; exec_norm).
