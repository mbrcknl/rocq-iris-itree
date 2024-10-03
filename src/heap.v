From iris.itree Require Import wpi choice ub handler itree step.
From iris.itree Require Export state.
From iris.heap_lang Require Export locations.
From ITree Require Import ITree.
From ITree Require Import TranslateFacts InterpFacts RecursionFacts.
From stdpp Require Import gmap.
From iris Require Import ghost_map.
From iris Require Import invariants.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.

(** A heap, represented as a [gmap] of [option val]s, with [None] representing
deallocated locations. *)
Notation heap V := (gmap loc (option V)).
(** [HeapE V] is the event type for manipulating a heap. *)
Notation heapE V := (stateE (heap V)).

(** Store [x] at memory cell [l] and return the old value. It exhibits UB if
the memory cell at [l] is currently free. If [x = None], [l] gets
deallocated. *)
Definition store' `{!heapE V -< E} (l : loc) (x : option V) : itree E (option V) :=
  σ ← trigger EGetState;
  trigger (ESetState (<[l:=x]> σ));;
  Ret match σ !! l with
  | Some (Some v) => Some v
  | _ => None
  end.
(** Store [x] at memory cell [l] and return the old value. *)
Definition store `{!heapE V -< E} (l : loc) (x : V) : itree E (option V) :=
  store' l (Some x).
(** Load memory cell [l]. *)
Definition load `{!heapE V -< E} (l : loc) : itree E (option V) :=
  σ ← trigger EGetState;
  Ret match σ !! l with
  | Some (Some v) => Some v
  | _ => None
  end.

Lemma store'_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (Hin : E1 -< E2) l x :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (store' l x) Hin (store' l x).
Proof.
  move => ?. rewrite /store'.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  by apply Ret_to_translate.
Qed.
Global Hint Resolve store'_to_translate : itree_auto.
Lemma store_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (Hin : E1 -< E2) l x :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (store l x) Hin (store l x).
Proof. apply store'_to_translate. Qed.
Global Hint Resolve store_to_translate : itree_auto.
Lemma load_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (Hin : E1 -< E2) l :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (load l) Hin (load l).
Proof.
  move => ?. rewrite /store'.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  by apply Ret_to_translate.
Qed.
Global Hint Resolve load_to_translate : itree_auto.

(** A version of [store'] that exhibits UB if overwriting a free memory cell. *)
Definition store'_or_ub `{!heapE V -< E} `{ubE -< E} l x : itree E V :=
  v ← store' l x;
  some_or_ub v.
(** A version of [store] that exhibits UB if overwriting a free memory cell. *)
Definition store_or_ub `{!heapE V -< E} `{ubE -< E} l x : itree E V :=
  store'_or_ub l (Some x).
(** A version of [load] that exhibits UB if loading a free memory cell. *)
Definition load_or_ub `{!heapE V -< E} `{ubE -< E} l : itree E V :=
  v ← load l;
  some_or_ub v.

Lemma store'_or_ub_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (HE1' : ubE -< E1) (HE2' : ubE -< E2) (Hin : E1 -< E2) l x :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin HE1' HE2' →
  ITreeToTranslate (store'_or_ub l x) Hin (store'_or_ub l x).
Proof.
  move => Hresum [Heq]. rewrite /store'_or_ub.
  apply bind_to_translate; [by apply store'_to_translate|]. move => ?.
  by apply some_or_ub_to_translate.
Qed.
Global Hint Resolve store'_or_ub_to_translate : itree_auto.
Lemma store_or_ub_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (HE1' : ubE -< E1) (HE2' : ubE -< E2) (Hin : E1 -< E2) l x :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin HE1' HE2' →
  ITreeToTranslate (store_or_ub l x) Hin (store_or_ub l x).
Proof. apply store'_or_ub_to_translate. Qed.
Global Hint Resolve store_or_ub_to_translate : itree_auto.
Lemma load_or_ub_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (HE1' : ubE -< E1) (HE2' : ubE -< E2) (Hin : E1 -< E2) l :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin HE1' HE2' →
  ITreeToTranslate (load_or_ub l) Hin (load_or_ub l).
Proof.
  move => [Heq1 Heq2]. rewrite /load_or_ub.
  apply bind_to_translate; [by apply load_to_translate|]. move => ?.
  by apply some_or_ub_to_translate.
Qed.
Global Hint Resolve load_or_ub_to_translate : itree_auto.

Section free_locations.
  (** If [P i] is decidable for all [i], then whether it holds in a finite range
  is also decidable. *)
  Lemma Decision_range P n :
    (∀ i, Decision (P i)) →
    Decision (∀ i, 0 ≤ i → i < n → P i).
  Proof.
    intros HPdec.
    induction n.
    - left. intros i Hlower Hupper. lia.
    - destruct (decide (P n)) as [Heq|Hneq].
      * destruct (decide (∀ i : nat, 0 ≤ i → i < n → P i)) as [HP|HP].
        + left. intros i Hlower Hupper.
          destruct (decide (i = n)) as [->|Hi]; first done.
          apply HP; lia.
        + right. intros HP'.
          apply HP. intros i Hlower Hupper.
          destruct (decide (i = n)) as [->|Hi]; first done.
          apply HP'; lia.
      * right. intros HP. apply Hneq. apply HP; lia.
  Qed.

  (** Whether a range of the heap is free is decidable. *)
  Instance free_locations_dec {V} n l (σ : heap V) :
    Decision (∀ i, 0 ≤ i → i < n → (σ !! (l +ₗ i) = None)).
  Proof. apply Decision_range. apply _. Qed.
  (** Available locations in heap [σ] for allocating a block of [n] adjacent
  memory cells. *)
  Definition free_locations {V} n (σ : heap V) : Set :=
    {l : loc | bool_decide (∀ i, 0 ≤ i → i < n → (σ !! (l +ₗ i) = None))}.
  Global Hint Transparent free_locations : itree_auto.
  (** The heap always has more space. *)
  Global Instance free_locations_Inhabited {V} n (σ : heap V) :
    Inhabited (free_locations n σ).
  Proof.
    constructor. apply exist with (x := Loc.fresh (dom σ)).
    apply bool_decide_pack.
    intros i Hlower Hupper.
    rewrite -not_elem_of_dom. apply Loc.fresh_fresh. lia.
  Defined.
  Instance free_locations_EqDecision {V} n (σ : heap V) :
    EqDecision (free_locations n σ).
  Proof.
    intros l1 l2.
    destruct (decide (`l1 = `l2)) as [Heq|Hneq].
    - apply dsig_eq in Heq. by left.
    - right. intros Heq. apply Hneq. by apply dsig_eq.
  Qed.
End free_locations.

Fixpoint heap_array {V} (l : loc) (vs : list V) : heap V :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := Some v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton {V} l (v : V) :
    heap_array l [v] = {[l := Some v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup {V} l vs (ow : option V) k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = Some w ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite Loc.add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite Loc.add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite Loc.add_0; eauto. }
    right. split.
    { rewrite -{1}(Loc.add_0 l). intros ?%(inj (Loc.add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite Loc.add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint {V} (h : gmap loc (option V)) (l : loc) (vs : list V) :
  (∀ (i : nat), 0 ≤ i → i < length vs → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?.
  replace j with (Z.of_nat (Z.to_nat j)) by lia. rewrite Hdisj //; lia.
Qed.

Definition allocN `{!heapE V -< E} (n : nat) (v : V) : itree E loc :=
  (* Read the entire heap. *)
  σ ← trigger EGetState;
  (* Deterministically pick a free location on the heap. *)
  let l : free_locations n σ := inhabitant in
    (* Write the evaluated value [v] to every memory cell in that segment. *)
    trigger (ESetState ((heap_array (`l) (replicate n v)) ∪ σ));;
    Ret (`l).

Lemma allocN_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (Hin : E1 -< E2) n v :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (allocN n v) Hin (allocN n v).
Proof.
  move => [Heq]. rewrite /allocN.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  apply Ret_to_translate.
Qed.
Global Hint Resolve allocN_to_translate : itree_auto.

Definition allocN_nondet `{!heapE V -< E} `{demonicE -< E} (n : nat) (v : V) : itree E loc :=
  (* Read the entire heap. *)
  σ ← trigger EGetState;
  (* Demonically pick a free location of the heap. *)
  l ← demonic_choice (free_locations n σ);
  (* Write the evaluated value [v] to every memory cell in that segment. *)
  trigger (ESetState ((heap_array (`l) (replicate n v)) ∪ σ));;
  Ret (`l).

Lemma allocN_nondet_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (HE1' : demonicE -< E1) (HE2' : demonicE -< E2) (Hin : E1 -< E2) n v :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin HE1' HE2' →
  ITreeToTranslate (allocN_nondet n v) Hin (allocN_nondet n v).
Proof.
  move => [Heq] [Heq']. rewrite /allocN_nondet.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  apply bind_to_translate; [by apply trigger_to_translate|]. move => ?.
  apply Ret_to_translate.
Qed.
Global Hint Resolve allocN_nondet_to_translate : itree_auto.

Definition alloc `{!heapE V -< E} (v : V) : itree E loc :=
  allocN 1 v.

Lemma alloc_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (Hin : E1 -< E2) v :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (alloc v) Hin (alloc v).
Proof. apply allocN_to_translate. Qed.
Global Hint Resolve alloc_to_translate : itree_auto.

Definition alloc_nondet `{!heapE V -< E} `{demonicE -< E} (v : V) : itree E loc :=
  allocN_nondet 1 v.

Lemma alloc_nondet_to_translate {E1 E2 V} (HE1 : heapE V -< E1) (HE2 : heapE V -< E2) (HE1' : demonicE -< E1) (HE2' : demonicE -< E2) (Hin : E1 -< E2) v :
  TranslateReSum Hin HE1 HE2 →
  TranslateReSum Hin HE1' HE2' →
  ITreeToTranslate (alloc_nondet v) Hin (alloc_nondet v).
Proof. apply allocN_nondet_to_translate. Qed.
Global Hint Resolve alloc_nondet_to_translate : itree_auto.

Class heapHGpreS (Σ : gFunctors) (V : Type) := HeapHGpreS {
  heapH_ghost_varG :> ghost_mapG Σ loc (option V);
}.
Local Existing Instances heapH_ghost_varG.
Class heapHGS (Σ : gFunctors) (V : Type) := HeapHGS {
  heapH_inG : heapHGpreS Σ V;
  heapH_heap_name : gname;
  heapH_inv_name : namespace;
}.
Local Existing Instances heapH_inG.

Definition pointsto `{!heapHGS Σ V} (l : loc) (v : option V) (dq : dfrac) : iProp Σ :=
  l ↪[ heapH_heap_name ]{dq} v.

Global Notation "l ↦? v" := (pointsto l v (DfracOwn 1))
  (at level 20, format "l  ↦?  v") : bi_scope.
Global Notation "l ↦{ dq }? v" := (pointsto l v dq)
  (at level 20, format "l  ↦{ dq }?  v") : bi_scope.
Global Notation "l ↦ v" := (pointsto l (Some v) (DfracOwn 1))
  (at level 20, format "l  ↦  v") : bi_scope.
Global Notation "l ↦{ dq } v" := (pointsto l (Some v) dq)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.

Section handler.
  Context (V : Type) {Σ} `{!invGS_gen hlc Σ} `{!heapHGS Σ V}.

  (** We put half of the authoritative view of the current heap into an
  invariant so that we can know that someone else won't change it while we have
  control. *)
  Definition heap_inv : iProp Σ :=
    inv heapH_inv_name (∃ σ, ghost_map_auth heapH_heap_name (1 / 2) σ).
  (** We put the other half in the state interpretation. *)
  Global Instance stateInterp_heap : stateInterp Σ (heap V) := (λ σ,
    ghost_map_auth heapH_heap_name (1 / 2) σ
    (** To not have to manually thread through knowledge of the invariant,
    we put it inside the state interpretation. *)
    ∧ heap_inv)%I.

  (** The handler for [heapE]. *)
  Definition heapH : iHandler Σ (heapE V) :=
    stateH (heap V).
End handler.

Lemma heapH_init V `{!invGS_gen hlc Σ} `{!heapHGpreS Σ V} σ :
  ⊢ |={∅}=> ∃ _ : heapHGS Σ V, heap_inv V ∗ state_interp σ ∗ [∗ map] k↦v ∈ σ, k ↦? v.
Proof.
  iDestruct (ghost_map_alloc (K := loc) (V := option V) σ) as "Hgmap".
  iMod "Hgmap" as "[%γ [[Hauth' Hauth] Hfrag]]".
  iDestruct (inv_alloc (nroot .@ "heaplangH") (∅) ((∃ σ, ghost_map_auth γ (1 / 2) σ)%I)) as "Hinv".
  iSpecialize ("Hinv" with "[Hauth]"). { iNext. by iExists σ. }
  iMod "Hinv" as "#Hinv". iModIntro.
  iExists (HeapHGS Σ V _ γ (nroot .@ "heaplangH")).
  iFrame "Hinv". iFrame.
Qed.

Section wp.
  Context {V : Type} {E : Type → Type} `{H : iHandler Σ E} `{heapE V -< E}.
  Context `{!invGS_gen hlc Σ} `{!heapHGS Σ V} `{inH Σ (heapE V) E (heapH V) H}.

  Lemma wpi_load M l v dq Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ (Some v)) -∗
    WPi load l @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    iApply wpi_bind. iApply @wpi_get.
    iIntros (s) "[Hauth #Hinv]".
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %Hlu.
    iFrame. iFrame "Hinv".
    iApply wpi_ret. rewrite Hlu. iModIntro. wpi_norm. iApply wpi_ret. by iApply "Hwand".
  Qed.

  Lemma wpi_store' M l v v' Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦? v -∗
    (l ↦? v' -∗ Φ v) -∗
    WPi store' l v' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand". iApply wpi_clear_mask.
    iApply @wpi_bind. iApply @wpi_get.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iIntros (σ) "[Hauth' #Hinv]". iMod "Hfupd" as "_".
    iMod (inv_acc_timeless _ with "Hinv") as "[[%σ' Hauth] Hclose]"; first done.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %->.
    iFrame "Hinv Hauth'". iApply wpi_ret.
    iDestruct (ghost_map_lookup with "Hauth Hpointsto") as %Heq. rewrite Heq.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "[Hauth' _]".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    iDestruct (ghost_map_update v' with "Hauth Hpointsto") as ">[[Hauth Hauth'] Hpointsto]".
    iFrame "Hauth". iFrame "Hinv". repeat iApply wpi_ret. iModIntro.
    iMod "Hfupd". iMod ("Hclose" with "[Hauth']"); first by iExists _.
    case_match; by iApply "Hwand".
  Qed.

  Lemma wpi_store M l v v' Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦? v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi store l v' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    iApply (wpi_store' with "Hpointsto"); first done.
    by iApply "Hwand".
  Qed.

  Lemma big_sep_map_list_heap_array l n m v :
    ([∗ map] k↦v0 ∈ heap_array (l +ₗ Z.of_nat m) (replicate n v), k ↦? v0) -∗
    [∗ list] i ∈ seq m n, (l +ₗ Z.of_nat i) ↦ v.
  Proof.
    iIntros "Hsep".
    iInduction n as [|n'] "IH" forall (m).
    - done.
    - simpl.
      iDestruct (big_sepM_union with "Hsep") as "[Hfirst Hsep]".
      { symmetry. apply heap_array_map_disjoint. intros i Hnz Hlt. rewrite lookup_singleton_None.
        rewrite Loc.eq_spec. simpl. lia. }
      rewrite big_sepM_singleton. iFrame.
      iApply "IH".
      replace (l +ₗ S m) with (l +ₗ m +ₗ 1); last first. { rewrite Loc.add_assoc. f_equiv. lia. }
      done.
  Qed.

  Lemma wpi_allocN M n v Φ :
    ↑heapH_inv_name ⊆ M →
    (∀ l, ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v) -∗ Φ l) -∗
    WPi allocN n v @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hwand". iApply wpi_clear_mask.
    iApply wpi_bind. iApply wpi_get.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iIntros (σ) "[Hauth #Hinv]". iMod "Hfupd" as "_".
    iMod (inv_acc_timeless _ with "Hinv") as "[[%σ' Hauth'] Hclose]"; first done.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iFrame "Hauth' Hinv".
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply wpi_ret. iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "[Hauth' _]".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    destruct (inhabitant : free_locations n σ) as [l Hfree].
    simpl. apply bool_decide_unpack in Hfree.
    iMod (ghost_map_insert_big (heap_array l (replicate n v)) with "Hauth") as "[Hauth Hpointsto]".
    { apply heap_array_map_disjoint. destruct l as [l Hl]. intros i Hnz Hlt.
      rewrite length_replicate in Hlt.
      apply Hfree; first done. lia.
    }
    iDestruct "Hauth" as "[Hauth Hauth']".
    iFrame "Hinv".
    replace (Z.to_nat n) with n by lia. iFrame.
    repeat iApply wpi_ret. iApply "Hwand". iModIntro. iMod "Hfupd".
    iMod ("Hclose" with "[Hauth]") as "_".
    { by iExists _. }
    iApply big_sep_map_list_heap_array. rewrite Loc.add_0 //.
  Qed.

  Lemma wpi_alloc M v Φ :
    ↑heapH_inv_name ⊆ M →
    (∀ l, l ↦ v -∗ Φ l) -∗
    WPi alloc v @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hwand". iApply wpi_allocN; first done.
    simpl. iIntros (l) "[Hpointsto _]". rewrite Loc.add_0. by iApply "Hwand".
  Qed.
End wp.

Section wp_nondet.
  Context {V : Type} {E : Type → Type} `{H : iHandler Σ E} `{heapE V -< E}.
  Context `{!invGS_gen hlc Σ} `{!heapHGS Σ V} `{inH Σ (heapE V) E (heapH V) H}.
  Context `{demonicE -< E} `{inH Σ demonicE E demonicH H}.

  Lemma wpi_allocN_nondet M n v Φ :
    ↑heapH_inv_name ⊆ M →
    (∀ l, ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v) -∗ Φ l) -∗
    WPi allocN_nondet n v @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hwand". iApply wpi_clear_mask.
    iApply wpi_bind. iApply wpi_get.
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iIntros (σ) "[Hauth #Hinv]". iMod "Hfupd" as "_".
    iMod (inv_acc_timeless _ with "Hinv") as "[[%σ' Hauth'] Hclose]"; first done.
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iFrame "Hauth' Hinv".
    iApply fupd_mask_intro; first apply empty_subseteq. iIntros "Hfupd".
    iApply wpi_ret. iApply wpi_bind. iApply @wpi_demonic. iIntros ([l Hfree]).
    iApply wpi_bind. iApply @wpi_set. iIntros (σ'') "[Hauth' _]".
    iDestruct (ghost_map_auth_agree with "Hauth Hauth'") as %<-.
    iCombine "Hauth Hauth'" as "Hauth".
    simpl. apply bool_decide_unpack in Hfree.
    iMod (ghost_map_insert_big (heap_array l (replicate n v)) with "Hauth") as "[Hauth Hpointsto]".
    { apply heap_array_map_disjoint. destruct l as [l Hl]. intros i Hnz Hlt.
      rewrite length_replicate in Hlt.
      apply Hfree; first done. lia.
    }
    iDestruct "Hauth" as "[Hauth Hauth']".
    iFrame "Hinv".
    replace (Z.to_nat n) with n by lia. iFrame.
    repeat iApply wpi_ret. iApply "Hwand". iModIntro. iMod "Hfupd".
    iMod ("Hclose" with "[Hauth]") as "_".
    { by iExists _. }
    iApply big_sep_map_list_heap_array. rewrite Loc.add_0 //.
  Qed.

  Lemma wpi_alloc_nondet M v Φ :
    ↑heapH_inv_name ⊆ M →
    (∀ l, l ↦ v -∗ Φ l) -∗
    WPi alloc_nondet v @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hwand". iApply wpi_allocN_nondet; first done.
    simpl. iIntros (l) "[Hpointsto _]". rewrite Loc.add_0. by iApply "Hwand".
  Qed.
End wp_nondet.

Section wp_or_ub.
  Context {V : Type} {E : Type → Type} `{H : iHandler Σ E} `{heapE V -< E} `{ubE -< E}.
  Context `{!invGS_gen hlc Σ} `{!heapHGS Σ V} `{inH Σ (heapE V) E (heapH V) H}.

  Lemma wpi_load_or_ub M l v dq Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ v) -∗
    WPi load_or_ub l @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    iApply wpi_bind. iApply (wpi_load with "Hpointsto"); first done.
    iIntros "Hpointsto". iApply wpi_ret. by iApply "Hwand".
  Qed.

  Lemma wpi_store'_or_ub M l v v' Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦ v -∗
    (l ↦? v' -∗ Φ v) -∗
    WPi store'_or_ub l v' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    iApply wpi_bind. iApply (wpi_store' with "Hpointsto"); first done.
    iIntros "Hpointsto". iApply wpi_ret. by iApply "Hwand".
  Qed.

  Lemma wpi_store_or_ub M l v v' Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦? v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi store l v' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    by iApply (wpi_store with "Hpointsto").
  Qed.
End wp_or_ub.
