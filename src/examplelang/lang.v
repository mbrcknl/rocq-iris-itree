From ITree Require Import ITree.
From stdpp Require Import strings binders.

From iris.itree Require Import wpi choice ub heap handler itree.
From iris.itree.threadpool Require Import handler.

Inductive base_lit : Set :=
  | LitInt (n : Z)
  | LitLoc (l : loc).

Inductive expr :=
  | Val (v : val)
  | Var (x : string)
  | Lam (x : binder) (e : expr)
  | App (e1 e2 : expr)
  | Plus (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | Ref (e : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | PickInt
  | Spawn (e : expr)
with val :=
  | LitV (l : base_lit)
  | LamV (x : binder) (e : expr).

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Lam y e =>
     Lam y $ if decide (BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | Plus e1 e2 => Plus (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Ref e => Ref (subst x v e)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | PickInt => PickInt
  | Spawn e => Spawn (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

Definition exampleE : Type → Type := threadpoolE +' ubE +' heapE val +' demonicE.
Global Hint Transparent exampleE : itree_auto.

(** Cast a value to [LamV]. *)
Definition val_to_LamV (v : val) : option (binder * expr) :=
  match v with
  | LamV x_ e => Some (x_, e)
  | _ => None
  end.
(** Cast a value to [LitInt]. *)
Definition val_to_int (v : val) : option Z :=
  match v with
  | LitV (LitInt n) => Some n
  | _ => None
  end.
(** Cast a value to [LitLoc]. *)
Definition val_to_loc (v : val) : option loc :=
  match v with
  | LitV (LitLoc l) => Some l
  | _ => None
  end.

Definition yield_if_not_val (e : expr) {E} `{threadpoolE -< E} : itree E () :=
  match e with
  | Val _ => Ret ()
  | _ => yield
  end.
Arguments yield_if_not_val !_ / _.

Lemma yield_if_not_val_to_translate {E1 E2} (e : expr) (HE1 : threadpoolE -< E1) (HE2 : threadpoolE -< E2) (Hin : E1 -< E2) :
  TranslateReSum Hin HE1 HE2 →
  ITreeToTranslate (yield_if_not_val e) Hin (yield_if_not_val e).
Proof. move => ?. by destruct e => /=; try apply Ret_to_translate; apply yield_to_translate. Qed.
Global Hint Resolve yield_if_not_val_to_translate : itree_auto.

Fixpoint compile_expr' (e : expr) : itree (callE expr val +' exampleE) val :=
  let compile_expr_yield e := (v ← compile_expr' e ; yield_if_not_val e ;; Ret v)%itree in
  match e with
  | Var _ => ub
  | Val v => Ret v
  | Lam x e => Ret (LamV x e)
  | App e1 e2 =>
      f ← compile_expr_yield e1;
      v ← compile_expr_yield e2;
      '(x_, e) ← (val_to_LamV f)?;
      let body := subst' x_ v e in
      yield_if_not_val body;;
      call body
  | Plus e1 e2 =>
      v1 ← compile_expr_yield e1;
      v2 ← compile_expr_yield e2;
      n1 ← (val_to_int v1)?;
      n2 ← (val_to_int v2)?;
      Ret (LitV (LitInt (n1 + n2)))
  | If e0 e1 e2 =>
      v ← compile_expr_yield e0;
      n ← (val_to_int v)?;
      if decide (n ≠ 0) then
        yield_if_not_val e1;;
        compile_expr' e1
      else
        yield_if_not_val e2;;
        compile_expr' e2
  | Ref e =>
      v ← compile_expr_yield e;
      l ← alloc v;
      Ret (LitV (LitLoc l))
  | Load e =>
      l' ← compile_expr_yield e;
      l ← (val_to_loc l')?;
      v ← load_or_ub l;
      Ret v
  | Store e1 e2 =>
      l' ← compile_expr_yield e1;
      v ← compile_expr_yield e2;
      l ← (val_to_loc l')?;
      store_or_ub l v
  | PickInt =>
      n ← demonic_choice Z;
      Ret (LitV (LitInt n))
  | Spawn e =>
      spawn (compile_expr_yield e ;; Ret ()) ;;
      Ret (LitV (LitInt 0))
  end%itree.

Definition compile_expr : expr → itree exampleE val := rec compile_expr'.
