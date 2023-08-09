From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import handler.
From iris.itree Require Import wpi.
From iris.bi Require Import fixpoint.
From Paco Require Import paco.
From Paco Require Import paco2.
From ITree Require Import Basics.Monad.

Variant choiceE : Type → Type :=
  | EDemonic (A : Type) : choiceE A
  | EAngelic (A : Type) : choiceE A.

CoInductive choiceM (T : Type) : Type :=
  | Demonic {A : Type} (k : A → choiceM T) : choiceM T
  | Angelic {A : Type} (k : A → choiceM T) : choiceM T
  | Always (x : T).

Arguments Demonic {_ _} _.
Arguments Angelic {_ _} _.
Arguments Always {_} _.

Section monad.
  Global Instance Monad_Prop : Monad choiceM :=
    {|
    ret := λ _ x, Always x;
    bind := cofix bind _ _ c f :=
      match c with
      | Demonic k => Demonic (λ a, bind _ _ (k a) f)
      | Angelic k => Angelic (λ a, bind _ _ (k a) f)
      | Always x => f x
      end
    |}.

  Variant eq_choiceMF {T} (eq_choiceM : choiceM T → choiceM T → Prop)
    : choiceM T → choiceM T → Prop :=
  | DemonicDemonic A k k' :
    (∀ a, eq_choiceM (k a) (k' a)) →
    eq_choiceMF eq_choiceM (Demonic (A:=A) k) (Demonic k')
  | AngelicAngelic A k k' :
    (∀ a, eq_choiceM (k a) (k' a)) →
    eq_choiceMF eq_choiceM (Angelic (A:=A) k) (Angelic k')
  | AlwaysAlways x :
    eq_choiceMF eq_choiceM (Always x) (Always x).
  Hint Constructors eq_choiceMF : iris_itree.
  Lemma eq_choiceMF_monotone {T} :
    monotone2 (eq_choiceMF (T:=T)).
  Proof.
    intros m m' r r' Heq Hrel. destruct Heq; eauto with iris_itree.
  Qed.
  Definition eq_choiceM {T} : choiceM T → choiceM T → Prop :=
    paco2 eq_choiceMF bot2.

  Global Instance choiceM_Eq1 : Eq1 choiceM := λ T, eq_choiceM.

  Require Import Coq.Program.Equality.
  Global Instance choiceM_Equivalence {T : Type} : Equivalence (choiceM_Eq1 T).
  Proof.
    constructor.
    - pcofix CIH. intros x. destruct x; pfold; constructor; by right.
    - pcofix CIH. intros x y Heq. punfold Heq.
      destruct Heq as [B k k' Heq|B k k' Heq|x]; pfold; constructor; right.
      * pclearbot. apply CIH. apply Heq.
      * pclearbot. apply CIH. apply Heq.
      * apply eq_choiceMF_monotone.
    - pcofix CIH. intros x y z Hxy Hyz. punfold Hxy. punfold Hyz.
      * pfold. dependent destruction Hxy; dependent destruction Hyz; constructor; right.
        + pclearbot. apply CIH with (y := k' a).
          ++ apply H.
          ++ apply H0.
        + pclearbot. apply CIH with (y := k' a).
          ++ apply H.
          ++ apply H0.
      * apply eq_choiceMF_monotone.
      * apply eq_choiceMF_monotone.
  Qed.

  Definition choiceM_id {T : Type} (x : choiceM T) : choiceM T :=
    match x with
    | Demonic k => Demonic k
    | Angelic k => Angelic k
    | Always x => Always x
    end.
  Lemma choiceM_id_id {T : Type} (x : choiceM T) :
    x = choiceM_id x.
  Proof.
    by destruct x.
  Qed.

  Global Instance MonadLawsE_choiceM : MonadLawsE choiceM.
  Proof.
    constructor.
    - intros T U f a. rewrite /eq1/eq_choiceM/choiceM_Eq1 /ret/Monad_Prop /bind.
      pfold. setoid_rewrite choiceM_id_id. simpl. rewrite -choiceM_id_id.
      destruct (f a); constructor; left; apply reflexivity.
    - intros T. pcofix CIH. intros x. setoid_rewrite choiceM_id_id.
      destruct x; pfold; constructor; right; apply CIH.
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
          ++ constructor.
    - intros T1 T2. pcofix CIH. intros x y Hxy f g Hfg. punfold Hxy.
      * destruct Hxy; pclearbot; setoid_rewrite choiceM_id_id.
        + pfold. constructor. right. apply CIH.
          ++ apply H.
          ++ apply Hfg.
        + pfold. constructor. right. apply CIH.
          ++ apply H.
          ++ apply Hfg.
        + pfold. simpl. specialize (Hfg x). punfold Hfg.
          destruct Hfg; pclearbot; constructor; left.
          ++ eapply paco2_mon.
            +++ apply H.
            +++ by intros ???.
          ++ eapply paco2_mon.
            +++ apply H.
            +++ by intros ???.
          ++ apply eq_choiceMF_monotone.
      * apply eq_choiceMF_monotone.
  Qed.
End monad.

Section choiceA.
  Context {Σ : gFunctors}.

  Definition choiceAF (choiceA : leibnizO (choiceM (iProp Σ)) -d> iProp Σ)
    : choiceM (iProp Σ) -d> iProp Σ := λ x,
    match x with
    | Demonic k => (∀ a, choiceA (k a))%I
    | Angelic k => (∃ a, choiceA (k a))%I
    | Always x => x
    end.

  Local Instance choiceAF_monotone :
    BiMonoPred choiceAF.
  Proof.
    constructor.
    - iIntros (choiceA1 choiceA2 Hne1 Hne2) "#Hchoicewand". iIntros (x) "Hchoice".
      destruct x.
      * iIntros (a). by iApply "Hchoicewand".
      * iDestruct "Hchoice" as "[%a Hchoice]". iExists _. iApply "Hchoicewand". iApply "Hchoice".
      * done.
    - intros choiceA Hne. intros n x y Heq. by rewrite Heq.
  Qed.

  Definition choiceA : choiceM (iProp Σ) → iProp Σ :=
    bi_greatest_fixpoint choiceAF.

  Global Instance choiceAF_proper_ent :
    Proper ((eq_choiceM ==> (⊢)) ==> eq_choiceM ==> (⊢)) choiceAF.
  Proof.
    intros choiceA1 choiceA2 Hchoiceent x y Hxy.
    iIntros "Hchoice1". punfold Hxy. destruct Hxy as [A k k' Heq|A k k' Heq|x].
    - pclearbot. iIntros (a). rewrite -Hchoiceent.
      * iApply "Hchoice1".
      * apply Heq.
    - pclearbot. iDestruct "Hchoice1" as "[%a Hchoice1]". rewrite Hchoiceent.
      * iExists a. iApply "Hchoice1".
      * apply Heq.
    - done.
    - apply eq_choiceMF_monotone.
  Qed.
  Global Instance choiceAF_proper :
    Proper ((eq_choiceM ==> (≡)) ==> eq_choiceM ==> (≡)) choiceAF.
  Proof.
    intros choiceA1 choiceA2 Hchoiceeq x y Hxy.
    iSplit.
    - iApply choiceAF_proper_ent.
      * intros x' y' Hx'y'. rewrite Hchoiceeq //.
      * done.
    - iApply choiceAF_proper_ent.
      * intros x' y' Hx'y'. rewrite Hchoiceeq //.
      * done.
  Qed.
  Global Instance choiceA_proper_ent :
    Proper (eq_choiceM ==> (⊢)) choiceA.
  Proof.
    intros x y Hxy.
    iAssert (∀ y, (∃ x, choiceA x ∧ ⌜eq_choiceM x y⌝) -∗ choiceA y)%I as "Hwand".
    - clear x y Hxy. iApply (greatest_fixpoint_coiter choiceAF). iModIntro.
      iIntros (y) "[%x [Hchoice %Hxy]]".
      iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
      iApply choiceAF_proper_ent; last done.
      * iIntros (x' y' Hx'y') "Hgoal". iExists x'. by iSplit.
      * apply Hxy.
    - iIntros "Hx". iApply "Hwand". iExists x. iFrame. iPureIntro. apply Hxy.
  Qed.
  Global Instance choiceA_proper :
    Proper (eq_choiceM ==> (≡)) choiceA.
  Proof.
    intros x y Hxy.
    iSplit.
    - by iApply choiceA_proper_ent.
    - by iApply choiceA_proper_ent.
  Qed.

  Lemma choiceA_id x :
    choiceA (ret x) ≡ x.
  Proof.
    rewrite /choiceA greatest_fixpoint_unfold //.
  Qed.

  Lemma choiceA_associative_dir1 :
    ∀ z, (∃ x, choiceA (bind x id) ∧ ⌜bind x (λ y, ret (choiceA y)) = z⌝) -∗ choiceA z.
  Proof.
    iApply (greatest_fixpoint_coiter choiceAF). iModIntro. iIntros (z) "[%x [Hchoice %Heq]]".
    destruct Heq. destruct x.
    - iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
      rewrite /choiceAF /bind/Monad_Prop. iIntros (a). iExists (k a). iSplit.
      * iApply "Hchoice".
      * done.
    - iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
      rewrite /choiceAF /bind/Monad_Prop. iDestruct "Hchoice" as "[%a Hchoice]". iExists a.
      iExists (k a). iSplit.
      * iApply "Hchoice".
      * done.
    - rewrite bind_ret_l. iApply "Hchoice".
  Qed.
  Lemma choiceA_associative_dir2 :
    ∀ z, (∃ x, choiceA (bind x (λ y, ret (choiceA y))) ∧ ⌜eq_choiceM (bind x id) z⌝) -∗ choiceA z.
  Proof.
    iApply (greatest_fixpoint_coiter choiceAF). iModIntro. iIntros (z) "[%x [Hchoice %Heq]]".
    iApply (choiceAF_proper
      (λ z, (∃ x, choiceA (bind x (λ y, ret (choiceA y))) ∧ ⌜eq_choiceM (bind x id) z⌝)%I)
      _ _ (bind x id) z
    ). Unshelve.
    - done.
    - clear z Heq. destruct x.
      * iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
        rewrite /choiceAF /bind/Monad_Prop. iIntros (a). iExists (k a). iSplit.
        + iApply "Hchoice".
        + done.
      * iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
        rewrite /choiceAF /bind/Monad_Prop. iDestruct "Hchoice" as "[%a Hchoice]". iExists a.
        iExists (k a). iSplit.
        + iApply "Hchoice".
        + done.
      * iEval (rewrite bind_ret_l choiceA_id /choiceA greatest_fixpoint_unfold) in "Hchoice".
        iApply choiceAF_proper_ent; last done.
        + clear x. iIntros (x y Hxy) "Hchoice". iExists (ret x).
          rewrite !bind_ret_l choiceA_id. eauto.
        + rewrite bind_ret_l //.
    - clear x z Heq. intros x y Hxy. iSplit.
      + iIntros "H". iDestruct "H" as "[%y' H]". iExists y'. rewrite Hxy //.
      + iIntros "H". iDestruct "H" as "[%y' H]". iExists y'. rewrite Hxy //.
  Qed.
  Lemma choiceA_associative x :
    choiceA (bind x id) ≡ choiceA (bind x (λ y, ret (choiceA y))).
  Proof.
    iSplit.
    - iIntros "Hchoice". iApply choiceA_associative_dir1. iExists x. eauto.
    - iIntros "Hchoice". iApply choiceA_associative_dir2. iExists x. eauto.
  Qed.
End choiceA.
