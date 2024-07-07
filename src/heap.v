From iris.itree Require Import wpi choice ub state handler itree later.
From iris.heap_lang Require Export locations.
From ITree Require Import ITree.
From stdpp Require Import gmap.
From iris Require Import ghost_map.
From iris Require Import invariants.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.

(** A heap, represented as a [gmap] of [option val]s, with [None] representing
deallocated locations. *)
Definition heap V : Type := (gmap loc (option V)).
(** [HeapE V] is the event type for manipulating a heap. *)
Definition heapE V : Type → Type := stateE (heap V).

(** Store [x] at memory cell [l] and return the old value. It exhibits UB if
the memory cell at [l] is currently free. If [x = None], [l] gets
deallocated. *)
Definition store' `{!heapE V -< E} (l : loc) (x : option V) : itree E (option V) :=
  σ ← trigger EGetState;
  match σ !! l with
  | Some (Some v) =>
    trigger (ESetState (<[l:=x]> σ));;
    Ret (Some v)
  | _ => Ret None
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

Section free_locations.
  (** Version of [Decision_range] using [Z] inequalities instead of [nat]
  inequalities. *)
  Lemma Decision_range_Z P n :
    (∀ i, Decision (P i)) →
    Decision (∀ i, (0 ≤ i)%Z → (i < Z.of_nat n)%Z → P i).
  Proof.
    intros HPdec.
    induction n.
    - left. intros i Hlower Hupper. lia.
    - destruct (decide (P n)) as [Heq|Hneq].
      * destruct (decide (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → P i)) as [HP|HP].
        + left. intros i Hlower Hupper.
          destruct (decide (i = n)) as [->|Hi]; first done.
          apply HP; lia.
        + right. intros HP'.
          apply HP. intros i Hlower Hupper.
          destruct (decide (i = n)) as [->|Hi]; first done.
          apply HP'; lia.
      * right. intros HP. apply Hneq. apply HP; lia.
  Qed.
  (** If [P i] is decidable for all [i], then whether it holds in a finite range
  is also decidable. *)
  Lemma Decision_range P n :
    (∀ i, Decision (P i)) →
    Decision (∀ i, (0 ≤ i)%Z → (i < n)%Z → P i).
  Proof.
    intros HP.
    destruct (decide (n < 0)%Z) as [Hleq|Hleq].
    * left. intros i Hlower Hupper. lia.
    * replace n with (Z.of_nat (Z.to_nat n)); first by apply Decision_range_Z.
      lia.
  Qed.

  (** Whether a range of the heap is free is decidable. *)
  Instance free_locations_dec {V} n l (σ : heap V) :
    Decision (∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ !! (l +ₗ i) = None)).
  Proof. apply Decision_range. apply _. Qed.
  (** Available locations in heap [σ] for allocating a block of [n] adjacent
  memory cells. *)
  Definition free_locations {V} n (σ : heap V) : Set :=
    {l : loc | bool_decide (∀ i, (0 ≤ i)%Z → (i < n)%Z → (σ !! (l +ₗ i) = None))}.
  Global Hint Transparent free_locations : itree_auto.
  (** The heap always has more space. *)
  Global Instance free_locations_Inhabited {V} n (σ : heap V) :
    Inhabited (free_locations n σ).
  Proof.
    constructor. apply exist with (x := Loc.fresh (dom σ)).
    apply bool_decide_pack.
    intros i Hlower Hupper.
    rewrite -not_elem_of_dom. by apply Loc.fresh_fresh.
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

Definition alloc `{!heapE V -< E} (v : V) : itree E loc :=
  (* Read the entire heap. *)
  σ ← trigger EGetState;
  (* Deterministically pick a free location on the heap. *)
  let l : free_locations 1 σ := inhabitant in
    (* Write the evaluated value [v] to every memory cell in that segment. *)
    store (`l) v ;;
    Ret (`l).

Definition alloc_nondet `{!heapE V -< E} `{demonicE -< E} (v : V) : itree E loc :=
  (* Read the entire heap. *)
  σ ← trigger EGetState;
  (* Demonically pick a free location of the heap. *)
  l ← trigger (EDemonic (free_locations 1 σ));
  (* Write the evaluated value [v] to every memory cell in that segment. *)
  store (`l) v ;;
  Ret (`l).

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

Definition pointsto `{!heapHGS Σ V} (l : loc) (v : V) (dq : dfrac) : iProp Σ :=
  l ↪[ heapH_heap_name ]{dq} (Some v).

Global Notation "l ↦ v" := (pointsto l v (DfracOwn 1))
  (at level 20, format "l  ↦  v") : bi_scope.
Global Notation "l ↦{ dq } v" := (pointsto l v dq)
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
  ⊢ |={∅}=> ∃ _ : heapHGS Σ V, heap_inv V ∗ state_interp σ ∗ [∗ map] k↦v ∈ σ, k ↪[heapH_heap_name] v.
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
    l ↦ v -∗
    (match v' with Some v' => l ↦ v' | None => True end -∗ Φ (Some v)) -∗
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
    iApply "Hwand". by case_match.
  Qed.

  Lemma wpi_store M l v v' Φ :
    ↑heapH_inv_name ⊆ M →
    l ↦ v -∗
    (l ↦ v' -∗ Φ (Some v)) -∗
    WPi store l v' @ H; M {{ Φ }}.
  Proof.
    iIntros (Hmask) "Hpointsto Hwand".
    iApply (wpi_store' with "Hpointsto"); first done.
    by iApply "Hwand".
  Qed.
End wp.
