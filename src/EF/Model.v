From CRM Require Import EF.Def.
From CRM Require Import HOL.Base.
From Stdlib Require Import PeanoNat List Bool Equality.
Import ListNotations.
From Equations Require Import Equations.

Section Interp.

  Variable ℰ : EFData.

  Fixpoint sem (s : st) : Type :=
    match s with
    | ℕₛ => nat
    | 𝔹ₛ => bool
    | 𝕃ₛ s' => list (sem s')
    | ℙₛ => Φ ℰ
    | 𝟙ₛ => unit
    | 𝟘ₛ => Empty_set
    | s' →ₛ s'' => (sem s') -> (sem s'')
    | s' ×ₛ s'' => (sem s') * (sem s'')
    | s' +ₛ s'' => (sem s') + (sem s'')
    end.

  Fixpoint code (s : st) : sem s -> Φ ℰ :=
    match s with
    | ℕₛ => code_nat ℰ
    | 𝔹ₛ => code_bool ℰ
    | 𝕃ₛ s' => code_list ℰ (code s')
    | ℙₛ => fun _ => p_top ℰ
    | 𝟙ₛ => fun _ => p_top ℰ
    | 𝟘ₛ => fun _ => p_bot ℰ
    | s →ₛ s' => code_fun ℰ (code s) (code s')
    | s ×ₛ s' => code_prod ℰ (code s) (code s')
    | s +ₛ s' => fun _ => p_top ℰ
    end.

  Fixpoint sem_recN (A : Type) (x0 : A) (xs : nat -> A -> A) (n : nat) : A :=
    match n with
    | 0 => x0
    | S m => xs m (sem_recN A x0 xs m)
    end.

  Definition sem_recB (A : Type) (xt : A) (xf : A) (b : bool) : A :=
    match b with
    | true => xt
    | false => xf
    end.

  Fixpoint sem_recL (A B : Type) (xn : B) (xc : A -> list A -> B -> B)
    (l : list A) : B :=
    match l with
    | nil => xn
    | cons a l' => xc a l' (sem_recL A B xn xc l')
    end.

  Derive NoConfusion for tm.
  Derive NoConfusion for st.
  
  Inductive vec_sem : HOL_ctx -> Type :=
  | sem_nil : vec_sem []
  | sem_cons : forall {Γ : HOL_ctx} {s : st},
      sem s -> vec_sem Γ -> vec_sem (s :: Γ).

  Equations fetch_ctx (Γ : HOL_ctx) (s : st) (v : s ∈ˢ Γ) (ve : vec_sem Γ) :
    sem s :=
    fetch_ctx (s :: Γ) s (s >>₀ Γ) (sem_cons x ve) := x ;
    fetch_ctx (s :: Γ) s' (s >>ₛ v) (sem_cons _ ve) := fetch_ctx Γ s' v ve.

  Print Empty_set. Search Empty_set.

  Equations sem_tm (Γ : HOL_ctx) (s : st) (t : Γ ⊢ₛ s) (ve : vec_sem Γ) :
    sem s :=
  sem_tm Γ s ⟦ v ⟧ₛ ve := fetch_ctx Γ s v ve ;
  sem_tm Γ _ (ƛₛ s t) ve :=
    fun (z : sem s) => sem_tm (s :: Γ) s' t (sem_cons z ve) ;
  sem_tm Γ s' (t @ₛ u) ve := (sem_tm Γ (_ →ₛ s') t ve) (sem_tm Γ _ u ve) ;
  sem_tm Γ _ ⟨⟩ₛ ve := tt ;
  sem_tm Γ _ ⟨ t , u ⟩ₛ ve := (sem_tm Γ _ t ve, sem_tm Γ _ u ve) ;
  sem_tm Γ s (π¹ₛ t) ve := fst (sem_tm Γ (s ×ₛ _) t ve) ;
  sem_tm Γ s' (π²ₛ t) ve := snd (sem_tm Γ (_ ×ₛ s') t ve) ;
  sem_tm Γ _ (empty_tm s) ve := Empty_set_rect (fun _ => sem s);
  sem_tm Γ _ (κ¹ₛ s' t) ve := inl (sem_tm Γ _ t ve) ;
  sem_tm Γ _ (κ²ₛ s t) ve := inr (sem_tm Γ _ t ve) ;
  sem_tm Γ s (δₛ t u v) ve :=
    match sem_tm Γ _ t ve with
    | inl x => sem_tm Γ _ u ve x | inr x => sem_tm Γ _ v ve x end ;
  sem_tm Γ _ 0ₛ ve := 0 ;
  sem_tm Γ _ (Sₛ t) ve := S (sem_tm Γ ℕₛ t ve) ;
  sem_tm Γ s (recℕₛ t u v) ve :=
      sem_recN (sem s) (sem_tm Γ s t ve) (sem_tm Γ (ℕₛ →ₛ s →ₛ s) u ve)
        (sem_tm Γ ℕₛ v ve) ;
  sem_tm Γ _ ⊤ₛ ve := true ;
  sem_tm Γ _ ⊥ₛ ve := false ;
  sem_tm Γ s (rec𝔹ₛ t u v) ve :=
      sem_recB (sem s) (sem_tm Γ s t ve) (sem_tm Γ s u ve)
        (sem_tm Γ 𝔹ₛ v ve) ;
  sem_tm Γ _ []ₛ ve := [] ;
  sem_tm Γ _ (t ::ₛ u) ve := (sem_tm Γ _ t ve) :: (sem_tm Γ (𝕃ₛ _) u ve) ;
  sem_tm Γ s (rec𝕃ₛ t u v) ve :=
      sem_recL (sem _) (sem s) (sem_tm Γ s t ve)
        (sem_tm Γ (_ →ₛ 𝕃ₛ _ →ₛ s →ₛ s) u ve) (sem_tm Γ (𝕃ₛ _) v ve) ;
  sem_tm Γ _ (φ ⇒ₛ ψ) ve := p_imp ℰ (sem_tm Γ ℙₛ φ ve) (sem_tm Γ ℙₛ ψ ve) ;
  sem_tm Γ _ (∀ₛ s φ) ve :=
    push_in_powerset ℰ (fun a => sem_tm (s :: Γ) ℙₛ φ (sem_cons a ve)).

  Definition sem_cl {s : st} (t : nil ⊢ₛ s) : sem s := sem_tm nil s t sem_nil.

  Notation "⟦ t ⟧ₛₑₘ" := (sem_cl t).
  
  Definition forcing (e : E ℰ) (Γ : HOL_ctx) (φ : Γ ⊢ₛ ℙₛ) (ve : vec_sem Γ) :
    Prop :=
    rel ℰ e (p_top ℰ) (sem_tm Γ ℙₛ φ ve).

  Notation "e ⊩⟨ Γ , ve ⟩ φ" := (forcing e Γ φ ve) (at level 65).

  Definition is_forced (Γ : HOL_ctx) (φ : Γ ⊢ₛ ℙₛ) (ve : vec_sem Γ) : Prop :=
    exists e : E ℰ, e ⊩⟨ Γ, ve ⟩ φ.

  Notation "⊩⟨ Γ , ve ⟩ φ" := (is_forced Γ φ ve) (at level 65).

(*  Definition eq_obs (s : st) (x y : sem s) : Prop.
    induction s.
    - exact (x = y).
    - exact (x = y).
    - revert y; induction x; intro y.
      + induction y.
        ++ exact True.
        ++ exact False.
      + induction y.
        ++ exact False.
        ++ exact ((IHs a a0) /\ IHx y).
    - exact (log_eq ℰ x y).
    - exact (forall z : sem s1, IHs2 (x z) (y z)).
    - exact (IHs1 (fst x) (fst y) /\ IHs2 (snd x) (snd y)).
  Qed.*)

End Interp.
