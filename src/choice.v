From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import axioms.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.bi Require Import fixpoint.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import Basics.Monad.

(* TODO: Use syntactic sugar such as stdpp's Equiv (≡) and (>>=). *)

Variant choiceE : Type → Type :=
  | EDemonic (A : Type) : choiceE A
  | EAngelic (A : Type) : choiceE A.

(* TODO: Define choiceMO. *)
CoInductive choiceM (T : Type) : Type :=
  | Demonic (A : Type) (k : A → choiceM T) : choiceM T
  | Angelic (A : Type) (k : A → choiceM T) : choiceM T
  | Always (x : T).

Arguments Demonic {_} _ _.
Arguments Angelic {_} _ _.
Arguments Always {_} _.

Section monad.
  Global Instance Monad_Prop : Monad choiceM :=
    {|
    ret := λ _ x, Always x;
    bind := cofix bind _ _ c f :=
      match c with
      | Demonic _ k => Demonic _ (λ a, bind _ _ (k a) f)
      | Angelic _ k => Angelic _ (λ a, bind _ _ (k a) f)
      | Always x => f x
      end
    |}.

  Variant eq_choiceMF {T} (eq_T : T → T → Prop) (eq_choiceM : choiceM T → choiceM T → Prop)
    : choiceM T → choiceM T → Prop :=
  | DemonicDemonic A k k' :
    (∀ a, eq_choiceM (k a) (k' a)) →
    eq_choiceMF eq_T eq_choiceM (Demonic A k) (Demonic A k')
  | AngelicAngelic A k k' :
    (∀ a, eq_choiceM (k a) (k' a)) →
    eq_choiceMF eq_T eq_choiceM (Angelic A k) (Angelic A k')
  | AlwaysAlways x y :
    eq_T x y →
    eq_choiceMF eq_T eq_choiceM (Always x) (Always y).
  Hint Constructors eq_choiceMF : iris_itree.

  Lemma eq_choiceMF_monotone {T} (eq_T : T → T → Prop) :
    monotone2 (eq_choiceMF eq_T).
  Proof.
    intros m m' r r' Heq Hrel. destruct Heq; eauto with iris_itree.
  Qed.
  Definition eq_choiceM {T} (eq_T : T → T → Prop) : choiceM T → choiceM T → Prop :=
    paco2 (eq_choiceMF eq_T) bot2.

  Global Instance choiceM_Eq1 : Eq1 choiceM := λ _, eq_choiceM (=).

  Global Instance eq_choiceM_equivalence {T} (eq_T : relation T) `{!Equivalence eq_T} :
    Equivalence (eq_choiceM eq_T).
  Proof.
    constructor.
    - pcofix CIH. intros x. destruct x; pfold; constructor.
      * by right.
      * by right.
      * done.
    - pcofix CIH. intros x y Heq. punfold Heq.
      destruct Heq as [A k k' Heq|A k k' Heq|x].
      * pfold. constructor. right. pclearbot. apply CIH. apply Heq.
      * pfold. constructor. right. pclearbot. apply CIH. apply Heq.
      * pfold. by constructor.
      * apply eq_choiceMF_monotone.
    - pcofix CIH. intros x y z Hxy Hyz. punfold Hxy. punfold Hyz.
      * pfold.
        destruct Hxy; inversion Hyz; simplify_K.
        + constructor. right. pclearbot. apply CIH with (y := k' a).
          ++ apply H.
          ++ apply H3.
        + constructor. right. pclearbot. apply CIH with (y := k' a).
          ++ apply H.
          ++ apply H3.
        + constructor. by etrans.
      * apply eq_choiceMF_monotone.
      * apply eq_choiceMF_monotone.
  Qed.

  Global Instance choiceM_equiv `{Equiv T} : Equiv (choiceM T) := eq_choiceM (≡).

  Definition choiceM_id {T : Type} (x : choiceM T) : choiceM T :=
    match x with
    | Demonic _ k => Demonic _ k
    | Angelic _ k => Angelic _ k
    | Always x => Always x
    end.
  Lemma choiceM_id_id {T : Type} (x : choiceM T) :
    x = choiceM_id x.
  Proof.
    by destruct x.
  Qed.

  Global Instance ret_proper {T : Type} equiv :
    Proper (equiv ==> eq_choiceM (T:=T) equiv) ret.
  Proof.
    intros t1 t2 Heq. pfold. by constructor.
  Qed.
  Global Instance bind_proper {A B} equiv1 equiv2 :
    Proper (eq_choiceM equiv1 ==> (equiv1 ==> eq_choiceM equiv2) ==> eq_choiceM equiv2)
           (bind : choiceM A → (A → choiceM B) → choiceM B).
  Proof.
    pcofix CIH. intros ma1 ma2 Heqma f1 f2 Heqf. punfold Heqma; last apply eq_choiceMF_monotone.
    pfold. destruct Heqma as [X k k' Heq|X k k' Heq|x y Heq].
    - setoid_rewrite choiceM_id_id. constructor. right. apply CIH; last done. pclearbot. apply Heq.
    - setoid_rewrite choiceM_id_id. constructor. right. apply CIH; last done. pclearbot. apply Heq.
    - setoid_rewrite choiceM_id_id. specialize (Heqf x y Heq). punfold Heqf. simpl. destruct Heqf.
      * constructor. left. pclearbot. eapply paco2_mon; done.
      * constructor. left. pclearbot. eapply paco2_mon; done.
      * by constructor.
      * apply eq_choiceMF_monotone.
  Qed.

  Lemma eq_choiceM_mono {T} (f : T → T → Prop) (g : T → T → Prop) (x y : choiceM T) :
    (∀ x' y', f x' y' → g x' y') →
    eq_choiceM f x y → eq_choiceM g x y.
  Proof.
    intros Himply. generalize x y. clear x y. pcofix CIH. intros x y Heqf.
    pfold. punfold Heqf; last apply eq_choiceMF_monotone.
    destruct Heqf as [A k k' Heq|A k k' Heq|x]; constructor; pclearbot.
    - right. apply CIH. apply Heq.
    - right. apply CIH. apply Heq.
    - by apply Himply.
  Qed.
  Local Instance eq_choiceM_proper {T} :
    Proper (((=) ==> (=) ==> (↔)) ==> (=) ==> (=) ==> (↔)) (eq_choiceM (T:=T)).
  Proof.
    intros eq_T eq_T' Heq_T x x' <- y y' <-. split.
    - intros Heq. eapply eq_choiceM_mono; last done. intros. eapply Heq_T; done.
    - intros Heq. eapply eq_choiceM_mono; last done. intros. eapply Heq_T; done.
  Qed.
  Lemma forall_eq_choiceM {I T} (eq_T : I → T → T → Prop) x y `{Inhabited I} :
    (∀ i, eq_choiceM (eq_T i) x y) ↔ (eq_choiceM (λ x' y', ∀ i, eq_T i x' y') x y).
  Proof.
    split.
    - generalize x y. clear x y. pcofix CIH. intros x y Heq. pfold.
      specialize (Heq inhabitant) as Heqi. punfold Heqi. destruct Heqi; constructor.
      * intros a. right. apply CIH. intros i. specialize (Heq i).
        punfold Heq; last apply eq_choiceMF_monotone.
        inversion Heq as [A2 k2 k'2 Heq2| |]; simplify_K.
        pclearbot. apply Heq2.
      * intros a. right. apply CIH. intros i. specialize (Heq i).
        punfold Heq; last apply eq_choiceMF_monotone.
        inversion Heq as [|A2 k2 k'2 Heq2|]; simplify_K.
        pclearbot. apply Heq2.
      * intros i. specialize (Heq i). punfold Heq; last apply eq_choiceMF_monotone.
        by inversion Heq.
      * apply eq_choiceMF_monotone.
    - intros Heq. intros i. eapply eq_choiceM_mono; last done. done.
  Qed.

  Global Instance MonadLawsE_choiceM : MonadLawsE choiceM.
  Proof.
    constructor.
    - intros T U f a. rewrite /eq1/eq_choiceM/choiceM_Eq1 /ret/Monad_Prop /bind.
      pfold. setoid_rewrite choiceM_id_id. simpl. rewrite -choiceM_id_id.
      destruct (f a); constructor; last done; left; apply reflexivity.
    - intros T. pcofix CIH. intros x. setoid_rewrite choiceM_id_id.
      destruct x; pfold; constructor; last done; right; apply CIH.
    - intros T1 T2 T3 x f g. generalize x. clear x. pcofix CIH. intros x.
      setoid_rewrite choiceM_id_id. destruct x; pfold.
      * constructor. right. apply CIH.
      * constructor. right. apply CIH.
      * simpl. destruct (f x) as [ | |x'].
        + constructor. left. eapply paco2_mon.
          ++ apply reflexivity.
          ++ by intros ???.
        + constructor. left. eapply paco2_mon.
          ++ apply reflexivity.
          ++ by intros ???.
        + destruct (g x').
          ++ constructor. left. eapply paco2_mon.
            +++ apply reflexivity.
            +++ by intros ???.
          ++ constructor. left. eapply paco2_mon.
            +++ apply reflexivity.
            +++ by intros ???.
          ++ by constructor.
    - intros T1 T2. pcofix CIH. intros x y Hxy f g Hfg. punfold Hxy.
      * destruct Hxy as [A k k' Heq|A k k' Heq|x y Heq]; pclearbot; setoid_rewrite choiceM_id_id.
        + pfold. constructor. right. apply CIH.
          ++ apply Heq.
          ++ apply Hfg.
        + pfold. constructor. right. apply CIH.
          ++ apply Heq.
          ++ apply Hfg.
        + pfold. destruct Heq. specialize (Hfg x). punfold Hfg; last apply eq_choiceMF_monotone.
          simpl. destruct Hfg; pclearbot; constructor.
          ++ left. eapply paco2_mon.
            +++ apply H.
            +++ by intros ???.
          ++ left. eapply paco2_mon.
            +++ apply H.
            +++ by intros ???.
          ++ assumption.
      * apply eq_choiceMF_monotone.
  Qed.
End monad.

Section choiceMO.
  Context (T : ofe).

  Local Instance choiceM_dist : Dist (choiceM T) := λ n, eq_choiceM (dist n).

  Definition choiceM_ofe_mixin : OfeMixin (choiceM T).
  Proof.
    split.
    - intros x y. rewrite forall_eq_choiceM. apply eq_choiceM_proper; try done.
      intros a a' <- b b' <-. apply equiv_dist.
    - apply _.
    - intros n m x y Hdist Hleq. eapply eq_choiceM_mono; last done.
      intros x' y' Hdist'. eapply dist_lt; done.
  Qed.
  Canonical Structure choiceMO : ofe := Ofe (choiceM T) choiceM_ofe_mixin.

  Global Instance internal_eq_proper_strict {Σ} :
    Proper (eq_choiceM (=) ==> eq_choiceM (=) ==> (⊣⊢))
           (internal_eq : choiceM T → choiceM T → iProp Σ).
  Proof.
    intros x1 x2 Hx y1 y2 Hy. apply eq_choiceM_mono with (g:=(≡)) in Hx, Hy.
    - rewrite Hx Hy //.
    - by intros ? ? ->.
    - by intros ? ? ->.
  Qed.
End choiceMO.

Section choiceA.
  Context {Σ : gFunctors}.

  Definition choiceAF (choiceA : choiceMO (iProp Σ) -> iProp Σ)
    : choiceMO (iProp Σ) -> iProp Σ := λ x,
    match x with
    | Demonic _ k => (∀ a, choiceA (k a))%I
    | Angelic _ k => (∃ a, choiceA (k a))%I
    | Always x => x
    end.
  Global Instance choiceAF_ne n :
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) choiceAF.
  Proof.
    intros choiceA1 choiceA2 Hchoiceeq x1 x2 Hxeq.
    punfold Hxeq. destruct Hxeq as [A k k' Heq|A k k' Heq|x].
    - simpl. f_equiv. intros a. pclearbot. specialize (Heq a). apply Hchoiceeq. apply Heq.
    - simpl. f_equiv. intros a. pclearbot. specialize (Heq a). apply Hchoiceeq. apply Heq.
    - done.
    - apply eq_choiceMF_monotone.
  Qed.
  Global Instance choiceAF_proper :
    Proper (((≡) ==> (≡)) ==> (≡) ==> (≡)) choiceAF.
  Proof.
    intros choiceA1 choiceA2 Hchoiceeq x1 x2 Hxeq.
    punfold Hxeq. destruct Hxeq as [A k k' Heq|A k k' Heq|x].
    - simpl. f_equiv. intros a. pclearbot. specialize (Heq a). apply Hchoiceeq. apply Heq.
    - simpl. f_equiv. intros a. pclearbot. specialize (Heq a). apply Hchoiceeq. apply Heq.
    - done.
    - apply eq_choiceMF_monotone.
  Qed.
  Lemma choiceAF_rew choiceA mΦ mΨ :
    NonExpansive choiceA →
    mΦ ≡ mΨ -∗
    choiceAF choiceA mΦ -∗
    choiceAF choiceA mΨ.
  Proof.
    iIntros (Hne) "Heq Hchoice". by iRewrite -"Heq".
  Qed.

  Lemma choiceAF_mono f g :
    (∀ x, f x -∗ g x) -∗ ∀ x, choiceAF f x -∗ choiceAF g x.
  Proof.
    iIntros "Hwand" (x) "Hchoice". destruct x.
    - iIntros (a). by iApply "Hwand".
    - iDestruct "Hchoice" as "[%a Hchoice]". iExists _. iApply "Hwand". iApply "Hchoice".
    - done.
  Qed.
  Local Instance choiceAF_monotone :
    BiMonoPred choiceAF.
  Proof.
    constructor.
    - iIntros (choiceA1 choiceA2 Hne1 Hne2) "#Hchoicewand". by iApply choiceAF_mono.
    - solve_proper.
  Qed.

  Definition choiceA : choiceM (iProp Σ) → iProp Σ :=
    bi_greatest_fixpoint choiceAF.
  
  Global Instance choiceA_ne : NonExpansive choiceA.
  Proof. solve_proper. Qed.
  Global Instance choiceA_proper :
    Proper ((≡) ==> (⊣⊢)) choiceA.
  Proof. solve_proper. Qed.
  Global Instance choiceA_proper_strict :
    Proper (eq_choiceM (=) ==> (⊣⊢)) choiceA.
  Proof.
    intros Φ1 Φ2 HΦ. apply eq_choiceM_mono with (g:=(≡)) in HΦ.
    - by rewrite HΦ.
    - by intros ? ? ->.
  Qed.

  Lemma choiceA_id x :
    choiceA (ret x) ≡ x.
  Proof.
    rewrite /choiceA greatest_fixpoint_unfold //.
  Qed.

  Lemma choiceA_associative_dir1 :
    ∀ z, (∃ x, choiceA (bind x id) ∧ (bind x (λ y, ret (choiceA y)) ≡ z)) -∗ choiceA z.
  Proof.
    iApply (greatest_fixpoint_coiter choiceAF); first solve_proper. iModIntro.
    iIntros (z) "[%x [Hchoice Heq]]". iApply (choiceAF_rew with "Heq"); first solve_proper.
    destruct x.
    - iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
      rewrite /choiceAF /bind/Monad_Prop. iIntros (a). iExists (k a). iSplit.
      * iApply "Hchoice".
      * done.
    - iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
      rewrite /choiceAF /bind/Monad_Prop. iDestruct "Hchoice" as "[%a Hchoice]". iExists a.
      iExists (k a). iSplit.
      * iApply "Hchoice".
      * done.
    - iEval (rewrite bind_ret_l) in "Hchoice". iApply (choiceAF_rew _ (Always (choiceA x))); first solve_proper.
      * rewrite bind_ret_l //.
      * done.
  Qed.    

  Lemma choiceA_associative_dir2 :
    ∀ z, (∃ x, choiceA (bind x (λ y, ret (choiceA y))) ∧ (bind x id ≡ z)) -∗ choiceA z.
  Proof.
    iApply (greatest_fixpoint_coiter choiceAF); first solve_proper.
    iModIntro. iIntros (z) "[%x [Hchoice Heq]]".
    iApply (choiceAF_rew with "Heq"); first solve_proper.
    clear z. destruct x.
    - iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
      rewrite /choiceAF /bind/Monad_Prop. iIntros (a). iExists (k a). iSplit.
      * iApply "Hchoice".
      * done.
    - iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
      rewrite /choiceAF /bind/Monad_Prop. iDestruct "Hchoice" as "[%a Hchoice]". iExists a.
      iExists (k a). iSplit.
      * iApply "Hchoice".
      * done.
    - iEval (rewrite bind_ret_l choiceA_id /choiceA greatest_fixpoint_unfold) in "Hchoice".
      iApply bi_mono_pred; last done; first solve_proper. clear x.
      iModIntro. iIntros (x) "Hchoice". iExists (ret x). iSplit.
      * rewrite bind_ret_l. rewrite choiceA_id //.
      * rewrite bind_ret_l //.
  Qed.
  Lemma choiceA_associative x :
    choiceA (bind x id) ≡ choiceA (bind x (λ y, ret (choiceA y))).
  Proof.
    iSplit.
    - iIntros "Hchoice". iApply choiceA_associative_dir1. iExists x. eauto.
    - iIntros "Hchoice". iApply choiceA_associative_dir2. iExists x. eauto.
  Qed.

  Lemma choiceA_monotone' {R} (Φ : R → iProp Σ) (Ψ : R → iProp Σ) :
    ∀ z, ((∃ x, choiceA (bind x (λ r, ret (Φ r))) ∗ (∀ r, Φ r -∗ Ψ r) ∗ (bind x (λ r, ret (Ψ r)) ≡ z)) -∗ choiceA z).
  Proof.
    iApply (greatest_fixpoint_coiter choiceAF); first solve_proper. iModIntro.
    iIntros (mΦ) "[%mr [Hchoice [Hwand #Heq]]]". iApply (choiceAF_rew with "Heq"); first solve_proper.
    iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
    destruct mr as [A k|A k|r].
    - iIntros (a). iExists (k a). iSpecialize ("Hchoice" $! a). by iFrame.
    - iDestruct "Hchoice" as "[%a Hchoice]". iExists a. iExists (k a). by iFrame.
    - by iApply "Hwand".
  Qed.
  Lemma choiceA_monotone {R} (mr : choiceM R) Φ Ψ :
    (∀ r, Φ r -∗ Ψ r) -∗
    choiceA (bind mr (λ r, ret (Φ r))) -∗
    choiceA (bind mr (λ r, ret (Ψ r))).
  Proof.
    iIntros "Hwand Hchoice". iApply choiceA_monotone'. iExists mr. by iFrame.
  Qed.
End choiceA.
