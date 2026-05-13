From CRM Require Import EF.Def.
From CRM Require Import HOL.Base HOL.Typing HOL.Theorie HOL.Reduction.
From CRM Require Import HOL.fintype.
Import CombineNotations.
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
    | s' →ₛ s'' => (sem s') -> (sem s'')
    | s' ×ₛ s'' => (sem s') * (sem s'')
    end.

  Fixpoint code (s : st) : sem s -> Φ ℰ :=
    match s with
    | ℕₛ => code_nat ℰ
    | 𝔹ₛ => code_bool ℰ
    | 𝕃ₛ s' => code_list ℰ (code s')
    | ℙₛ => id
    | s →ₛ s' => code_fun ℰ (code s) (code s')
    | s ×ₛ s' => code_prod ℰ (code s) (code s')
    end.

  Axiom sem_tm : forall {n : nat} (Γ : HOL_ctx n) (t : tm n) (s : st),
      Γ ⊢⟨ n ⟩ t ~: s -> (forall f, sem (Γ f)) -> sem s.

  Definition eq_obs (s : st) (x y : sem s) : Prop.
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
  Qed.

  Definition aux_app {n : nat} (Γ : HOL_ctx n) (s : st)
    (v : forall f, sem (Γ f)) (x : sem s) : forall f, sem ((s .: Γ) f) :=
    fun f => match f with
             | None => x
             | Some f' => v f'
             end.

  Fixpoint sem_recN (A : Type) (x0 : A) (xs : nat -> A -> A) (n : nat) : A :=
    match n with
    | 0 => x0
    | S m => xs m (sem_recN A x0 xs m)
    end.

  Fixpoint sem_recB (A : Type) (xt : A) (xf : A) (b : bool) : A :=
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
  
  Equations sem_tm {n : nat} (Γ : HOL_ctx n) (t : tm n) (s : st) :
    Γ ⊢⟨ n ⟩ t ~: s -> (forall f, sem (Γ f)) -> sem s :=
  sem_tm Γ (var_tm f) _ typ_var v := v f ;
  sem_tm Γ (ƛ t) (s →ₛ s') (typ_lam x) v :=
      fun (z : sem s) => sem_tm (s .: Γ) t s' x (aux_app Γ s v z) ;
  sem_tm Γ (t @ₛ u) s' (typ_app s xt xu) v :=
      (sem_tm Γ t (s →ₛ s') xt v) (sem_tm Γ u s xu v) ;
  sem_tm Γ Zₛ ℕₛ typ_z v := 0 ;
  sem_tm Γ (Sₛ t) ℕₛ (typ_s x) v := S (sem_tm Γ t ℕₛ x v) ;
  sem_tm Γ (recℕₛ t u v) s (typ_recN xt xu xv) w :=
      sem_recN (sem s)
        (sem_tm Γ t s xt w)
        (sem_tm Γ u (ℕₛ →ₛ s →ₛ s) xu w)
        (sem_tm Γ v ℕₛ xv w) ;
  sem_tm Γ ttₛ 𝔹ₛ typ_tt v := true ;
  sem_tm Γ ffₛ 𝔹ₛ typ_ff v := false ;
  sem_tm Γ (rec𝔹ₛ t u v) s (typ_recB xt xu xv) w :=
      sem_recB (sem s)
        (sem_tm Γ t s xt w)
        (sem_tm Γ u s xu w)
        (sem_tm Γ v 𝔹ₛ xv w) ;
  sem_tm Γ []ₛ (𝕃ₛ s) typ_nil v := [] ;
  sem_tm Γ (t ::ₛ u) (𝕃ₛ s) (typ_cons xt xu) v :=
      (sem_tm Γ t s xt v) :: (sem_tm Γ u (𝕃ₛ s) xu v) ;
  sem_tm Γ (rec𝕃ₛ t u v) s (typ_recL s' xt xu xv) w :=
      sem_recL (sem s') (sem s)
        (sem_tm Γ t s xt w)
        (sem_tm Γ u (s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s) xu w)
        (sem_tm Γ v (𝕃ₛ s') xv w) ;
  sem_tm Γ ⟨ t , u ⟩ₛ (s ×ₛ s') (typ_pair xt xu) v :=
      ((sem_tm Γ t s xt v), (sem_tm Γ u s' xu v)) ;
  sem_tm Γ (π¹ₛ t) s (typ_proj1 s' xt) v :=
      fst (sem_tm Γ t (s ×ₛ s') xt v) ;
  sem_tm Γ (π²ₛ t) s' (typ_proj2 s xt) v :=
      snd (sem_tm Γ t (s ×ₛ s') xt v) ;
  sem_tm Γ (φ ⇒ₛ ψ) ℙₛ (typ_imp xφ xψ) v :=
      p_imp ℰ (sem_tm Γ φ ℙₛ xφ v) (sem_tm Γ ψ ℙₛ xψ v) ;
  sem_tm Γ (∀ₛ s φ) ℙₛ (typ_forall s xφ) v :=
       push_in_powerset ℰ
        (fun a =>
           sem_tm (s .: Γ) φ ℙₛ xφ (aux_app Γ s v a));
  sem_tm Γ (𝕊 s t) ℙₛ (typ_sort xt) v :=
       code s (sem_tm Γ t s xt v).

  Equations sem_ctx {n : nat} (Γ : HOL_ctx n) (Ξ : proof_ctx n) :
    (wt_ctx Γ Ξ) (forall f, sem (Γ f)) : list (Φ ℰ) :=
  | sem_ctx Γ nil forall_nil H := nil ;
  | sem_ctx Γ (φ :: Ξ) (forall_cons Hφ HΞ) H :=
      sem_tm Γ φ ℙₛ Hφ H :: sem_ctx Γ Ξ HΞ H.

End Interp.
