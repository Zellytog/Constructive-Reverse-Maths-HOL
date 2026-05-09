From CRM Require Import EF.Def.
From CRM Require Import HOL.Base HOL.Typing HOL.Theorie HOL.Reduction.
Require Import PeanoNat List Bool Equality.
Import ListNotations.
(*From Equations Require Import Equations.*)

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
    
(*  Equation sem_tm {n : nat} (Γ : HOL_ctx n) (t : tm n) (s : st) :
    Γ ⊢⟨ n ⟩ t ~: s -> (forall f, sem (Γ f)) -> sem s :=
  | sem_tm Γ f (Γ f) typ_var v := f v ;
  | sem_tm Γ (ƛ t) (s →ₛ s') (typ_lam x) v :=
      fun (z : semant s) => sem_tm (s .: Γ) t s' x ;
  | sem_tm Γ (t @ₛ u) s' (typ_app s xt xu) v :=
      (sem_tm Γ t (s →ₛ s') xt v) (sem_tm Γ u s xu v) ;
  | sem_tm Γ Zₛ ℕₛ typ_z v := 0 ;
  | sem_tm Γ (Sₛ t) ℕₛ (typ_s x) v := S (sem_tm Γ t ℕₛ x v) ;
  | sem_tm Γ (recℕₛ t u v) s (typ_recN xt xu xv) w :=
      nat_rec (fun _ => sem s)
        (sem_tm Γ t s xt w)
        (sem_tm Γ u (ℕₛ →ₛ s →ₛ s) xu w)
        (sem_tm Γ v ℕₛ xv w) ;
  | sem_tm Γ ttₛ 𝔹ₛ typ_tt v := true ;
  | sem_tm Γ ffₛ 𝔹ₛ typ_ff v := false ;
  | sem_tm Γ (rec𝔹ₛ t u v) s (typ_recB xt xu xv) w :=
      bool_rec (fun _ => sem s)
        (sem_tm Γ t s xt w)
        (sem_tmΓ u s xu w)
        (sem_tm Γ v 𝔹ₛ xv w) ;
  | sem_tm Γ []ₛ (𝕃ₛ s) typ_nil v := [] ;
  | sem_tm Γ (t ::ₛ u) (𝕃ₛ s) (typ_cons xt xu) v :=
      (sem_tm Γ t s xt v) :: (sem_tm Γ u (𝕃ₛ s) xu v) ;
  | sem_tm Γ (rec𝕃ₛ t u v) s (typ_recL s' xt xu xv) w :=
      list_rec (sem s') (fun _ => sem s)
        (sem_tm Γ t s xt w)
        (sem_tm Γ u (s' →ₛ s' → 𝕃ₛ s →ₛ s) xu w)
        (sem_tm Γ v (𝕃ₛ s') xv w) ;
  | sem_tm Γ ⟨ t , u ⟩ₛ (s ×ₛ s') (typ_pair xt xu) v :=
      ((sem_tm Γ t s xt v), (sem_tm Γ u s xu v)) ;
  | sem_tm Γ (π¹ₛ t) s (typ_proj1 s' xt) v :=
      fst (sem_tm Γ t (s ×ₛ s') xt v) ;
  | sem_tm Γ (π²ₛ t) s' (typ_proj2 s xt) v :=
      snd (sem_tm Γ t (s ×ₛ s') xt v) ;
  | sem_tm Γ (φ ⇒ₛ ψ) ℙₛ (typ_imp xφ xψ) v :=
      eimp E (sem_tm Γ φ ℙₛ xφ v) (sem_tm Γ ψ ℙₛ xψ v) ;
  | sem_tm Γ (∀ₛ s φ) ℙₛ (typ_forall s xφ) v :=
       push_in_powerset ℰ
        (fun a =>
        sem_tm (s .: Γ) φ ℙₛ xφ (a .: v)) ;
  | interp Γ (𝕊 s t) ℙₛ (typ_sort xt) v :=
       code s (sem_tm Γ t s xt v)

  Equations sem_ctx {n : nat} (Γ : HOL_ctx n) (Ξ : proof_ctx n) :
    (wt_ctx Γ Ξ) (forall f, sem (Γ f)) : list (Φ ℰ) :=
  | sem_ctx Γ nil forall_nil H := nil ;
  | sem_ctx Γ (φ :: Ξ) (forall_cons Hφ HΞ) H :=
      sem_tm Γ φ ℙₛ Hφ H :: sem_ctx Γ Ξ HΞ H.
 *)
End Interp.
