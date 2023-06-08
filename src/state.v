From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic.lib Require Import ghost_var.
From iris.base_logic.lib Require Export fancy_updates.
From iris.itree Require Import handler.

Class stateHPreG (Σ : gFunctors) (S : Type) := StateHPreG {
  stateH_pre_ghost_varG :> ghost_varG Σ S;
}.
Class stateHGS (Σ : gFunctors) (S : Type) := StateHGS {
  stateH_ghost_varG :> ghost_varG Σ S;
  stateH_name : gname;
}.
Definition stateHΣ S : gFunctors :=
  #[ ghost_varΣ S ].
Global Instance subG_stateHΣ Σ S :
  subG (stateHΣ S) Σ → stateHPreG Σ S.
Proof. solve_inG. Qed.

(** An event type for stateful programs with concurrency. *)
Inductive stateE (S : Type) : Type → Type :=
  (** Get the global state. *)
  | EGetState : stateE S S
  (** Set the global state. *)
  | ESetState (x : S) : stateE S unit
  (** Yield control to another (demonically chosen) thread in the thread-pool. *)
  | EYield : stateE S unit
  (** Split the thread into two threads corresponding to the answers [true]
  and [false]. *)
  | EFork : stateE S bool.
Arguments EGetState {_}.
Arguments ESetState {_} _.
Arguments EYield {_}.
Arguments EFork {_}.

(** State interpretation predicate which is enforced at every [EYield]. *)
Class stateInterp (Σ : gFunctors) (S : Type) := state_interp : S → iProp Σ.

(* TODO: Switch to some kind of authoritative thing. *)
Definition state_is {Σ S} `{!stateHGS Σ S} (s : S) : iProp Σ :=
  ∃ q, ghost_var stateH_name q s.
(** Asserts writable access to the state.

From the poitn of view of the weakest precondition, ownership corresponds to
the fraction 1/2 since at any given moment the adequacy proof also holds 1/2 of
the state. *)
Definition state_own {Σ S} `{!stateHGS Σ S} (s : S) : iProp Σ :=
  ghost_var stateH_name (1/2) s.

(* Handlers for [stateE]. *)
Definition get_stateH {Σ} (S : Type) `{!stateHGS Σ S} : iHandler Σ (stateE S) :=
  IHandlerT (λ e Φ,
      ∃ s, ⌜e = EGetState⌝ ∗ state_is s ∗ (state_is s -∗ Φ s))%I.
Definition set_stateH {Σ} (S : Type) `{!stateHGS Σ S} : iHandler Σ (stateE S) :=
  IHandlerT (λ e Φ,
      ∃ s s', ⌜e = ESetState s'⌝ ∗ state_own s ∗ (state_own s' -∗ Φ tt))%I.
(** At each [EYield], we re-assert all invariants as well as the [state_interp]. *)
Definition yieldH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HasNoLc Σ} : iHandler Σ (stateE S) :=
  IHandlerT (λ e Φ,
      ∃ s, ⌜e = EYield⌝ ∗ state_is s ∗ |={∅, ⊤}=> (state_interp s ∗
                  (∀ s', state_is s' -∗ state_interp s' ={⊤,∅}=∗ Φ tt)))%I.
Definition forkH {Σ} (S : Type) `{!stateHGS Σ S} : iHandler Σ (stateE S) :=
  IHandlerT (λ e Φ, Φ true ∗ Φ false)%I.

Definition stateH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HasNoLc Σ} : iHandler Σ (stateE S) :=
  get_stateH S ∪ set_stateH S ∪ yieldH S ∪ forkH S.
