From ITree Require Import ITree Eqit Recursion RecursionFacts TranslateFacts.
From iris.proofmode Require Import proofmode.
From iris.itree Require Import exec.
From iris.itree.threadpool Require Import handler.


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
  ([∗ list] t;M∈omap id l;Ms, P t M) -∗
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
    rewrite insert_app_r_alt length_take_le // ?Nat.sub_diag/= ?omap_app; csimpl.
    2,3:lia.
    iApply (big_sepL2_app with "Hs1"). iFrame.
Qed.

Lemma big_sepL2_omap_id_delete {Σ A B} x (l : list (option A)) (Ms : list B) (P : A → B → iProp Σ) i:
  l !! i = Some (Some x) →
  ([∗ list] t;M∈omap id l;Ms, P t M) -∗
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
    rewrite insert_app_r_alt length_take_le // ?Nat.sub_diag/= ?omap_app; csimpl.
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
    * iPureIntro. rewrite list_lookup_insert // length_insert.
      move: Hl => /(lookup_lt_Some _ _ _). by rewrite length_insert.
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
