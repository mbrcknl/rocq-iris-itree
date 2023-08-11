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
  Context {T : ofe}.

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
End choiceMO.

(* TODO: Add this if necessary.
Section eq_iProp.
  Context {Σ : gFunctors}.

  Import EqNotations.
  (* TODO: Fix OFE structure. *)
  Definition eq_choiceM_iPropF
    (eq_choiceM_iProp : prodO (leibnizO (choiceM (iProp Σ))) (leibnizO (choiceM (iProp Σ))) -d> iProp Σ)
    : prodO (leibnizO (choiceM (iProp Σ))) (leibnizO (choiceM (iProp Σ))) -d> iProp Σ := λ p,
    match p with
    | (@Demonic _ A k, @Demonic _ A' k') =>
        (∃ eq : A = A', ∀ a, eq_choiceM_iProp (k a, k' (rew eq in a)))%I
    | (@Angelic _ A k, @Angelic _ A' k') =>
        (∃ eq : A = A', ∀ a, eq_choiceM_iProp (k a, k' (rew eq in a)))%I
    | (Always Φ, Always Ψ) => (Φ ≡ Ψ)%I
    | _ => False%I
    end.

  Local Instance eq_choiceM_iPropF_mono :
    BiMonoPred eq_choiceM_iPropF.
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
End eq_iProp.
*)

Section choiceA.
  Context {Σ : gFunctors}.

  (* TODO: Fix OFE structure. *)
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

  Lemma choiceA_monotone' {R} (Φ : R → iProp Σ) (Ψ : R → iProp Σ) :
    (∀ r, Φ r -∗ Ψ r) -∗
    ∀ z, ((∃ x, choiceA (bind x (λ r, ret (Φ r))) ∧ ⌜z = bind x (λ r, ret (Φ r))⌝) -∗ choiceA z).
  Proof.
    iIntros "Hwand". iApply (greatest_fixpoint_coiter choiceAF). iModIntro.
    iIntros (x) "[%y [Hchoice %Heq]]". destruct Heq.
    iEval (rewrite /choiceA greatest_fixpoint_unfold) in "Hchoice".
    iApply choiceAF_proper_ent; last done.
    - clear x y. iIntros (x y Heq) "Hchoice". iExists
  Lemma choiceA_monotone {R} (x : choiceM R) Φ Ψ :
    (∀ r, Φ r -∗ Ψ r) -∗
    choiceA (bind x (λ r, ret (Φ r))) -∗
    choiceA (bind x (λ r, ret (Ψ r))).
  Proof.
End choiceA.
