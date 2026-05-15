From Stdlib Require Import Nat List.
Import ListNotations.
(*Require Import fintype.
Import CombineNotations.*)
From Equations Require Import Equations.
From Stdlib Require Import Wellfounded.Lexicographic_Exponentiation.
From Stdlib Require Import Program.Equality.

Inductive st : Type :=
| nat_st : st
| bool_st : st
| list_st : st -> st
| prop_st : st
| unit_st : st
| empty_st : st
| fun_st : st -> st -> st
| prod_st : st -> st -> st
| coprod_st : st -> st -> st.

Notation ℕₛ := nat_st.
Notation 𝔹ₛ := bool_st.
Notation 𝕃ₛ := list_st.
Notation ℙₛ := prop_st.
Notation "𝟙ₛ" := unit_st.
Notation "𝟘ₛ" := empty_st.
Notation "s →ₛ s'" := (fun_st s s') (at level 60, right associativity).
Notation "s ×ₛ s'" := (prod_st s s') (at level 53, right associativity).
Notation "s +ₛ s'" := (coprod_st s s') (at level 55, right associativity).

Definition HOL_ctx : Type := list st.

Inductive HOL_var : st -> HOL_ctx -> Type :=
| vz_tm : forall (s : st) (Γ : HOL_ctx), HOL_var s (s :: Γ)
| vs_tm : forall {s : st} {Γ : HOL_ctx} (s' : st),
    HOL_var s Γ -> HOL_var s (s' :: Γ).

Notation "s ∈ˢ Γ" := (HOL_var s Γ) (at level 65).
Notation "s >>₀ Γ" := (vz_tm s Γ) (at level 55).
Notation "s >>ₛ v" := (vs_tm s v) (at level 55, right associativity).

Inductive tm : HOL_ctx -> st -> Type :=
| var_tm : forall {Γ : HOL_ctx} {s : st}, s ∈ˢ Γ -> tm Γ s
| lam_tm : forall {Γ : HOL_ctx} (s : st) {s' : st},
    tm (s :: Γ) s' -> tm Γ (s →ₛ s')
| app_tm : forall {Γ : HOL_ctx} {s s' : st},
    tm Γ (s →ₛ s') -> tm Γ s -> tm Γ s'
| unit_tm : forall {Γ : HOL_ctx}, tm Γ 𝟙ₛ
| pair_tm : forall {Γ : HOL_ctx} {s s' : st},
    tm Γ s -> tm Γ s' -> tm Γ (s ×ₛ s')
| proj1_tm : forall {Γ : HOL_ctx} {s s' : st},
    tm Γ (s ×ₛ s') -> tm Γ s
| proj2_tm : forall {Γ : HOL_ctx} {s s' : st},
    tm Γ (s ×ₛ s') -> tm Γ s'
| empty_tm : forall {Γ : HOL_ctx} (s : st), tm Γ (𝟘ₛ →ₛ s)
| coproj1_tm : forall {Γ : HOL_ctx} {s : st} (s' : st), tm Γ s -> tm Γ (s +ₛ s')
| coproj2_tm : forall {Γ : HOL_ctx} (s : st) {s': st}, tm Γ s' -> tm Γ (s +ₛ s')
| cases_tm : forall {Γ : HOL_ctx} {s s' : st} {s'' : st},
    tm Γ (s +ₛ s') -> tm Γ (s →ₛ s'') -> tm Γ (s' →ₛ s'') -> tm Γ s''
| z_tm : forall {Γ : HOL_ctx}, tm Γ ℕₛ
| s_tm : forall {Γ : HOL_ctx}, tm Γ ℕₛ -> tm Γ ℕₛ
| recN_tm : forall {Γ : HOL_ctx} {s : st},
    tm Γ s -> tm Γ (ℕₛ →ₛ s →ₛ s) -> tm Γ ℕₛ -> tm Γ s
| tt_tm : forall {Γ : HOL_ctx}, tm Γ 𝔹ₛ
| ff_tm : forall {Γ : HOL_ctx}, tm Γ 𝔹ₛ
| recB_tm : forall {Γ : HOL_ctx} {s : st},
    tm Γ s -> tm Γ s -> tm Γ 𝔹ₛ -> tm Γ s
| nil_tm : forall {Γ : HOL_ctx} {s : st}, tm Γ (𝕃ₛ s)
| cons_tm : forall {Γ : HOL_ctx} {s : st},
    tm Γ s -> tm Γ (𝕃ₛ s) -> tm Γ (𝕃ₛ s)
| recL_tm : forall {Γ : HOL_ctx} {s : st} {s' : st},
    tm Γ s -> tm Γ (s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s) -> tm Γ (𝕃ₛ s') -> tm Γ s
| imp_tm : forall {Γ : HOL_ctx}, tm Γ ℙₛ -> tm Γ ℙₛ -> tm Γ ℙₛ
| forall_tm : forall {Γ : HOL_ctx} (s : st), tm (s :: Γ) ℙₛ -> tm Γ ℙₛ.

Notation "Γ ⊢ₛ s" := (tm Γ s) (at level 63).
Notation "⟦ v ⟧ₛ" := (var_tm v).
Notation ƛₛ := lam_tm.
Notation "t @ₛ u" := (app_tm t u) (at level 50).
Notation "⟨⟩ₛ" := (unit_tm).
Notation "⟨ t , u ⟩ₛ" := (pair_tm t u).
Notation "π¹ₛ" := proj1_tm.
Notation "π²ₛ" := proj2_tm.
Notation "κ¹ₛ" := coproj1_tm.
Notation "κ²ₛ" := coproj2_tm.
Notation δₛ := (cases_tm).
Notation "0ₛ" := z_tm.
Notation Sₛ := s_tm.
Notation recℕₛ := recN_tm.
Notation "⊤ₛ" := tt_tm.
Notation "⊥ₛ" := ff_tm.
Notation rec𝔹ₛ := recB_tm.
Notation "[]ₛ" := nil_tm.
Notation "t ::ₛ u" := (cons_tm t u) (at level 55, right associativity).
Notation rec𝕃ₛ := recL_tm.
Notation "φ ⇒ₛ ψ" := (imp_tm φ ψ) (at level 61, right associativity).
Notation "∀ₛ" := forall_tm.

Equations lift_var (Γ₀ Δ Γ₁ : HOL_ctx) (s : st) (v : HOL_var s (Γ₀ ++ Γ₁)) :
  HOL_var s (Γ₀ ++ Δ ++ Γ₁) by wf (length Γ₀ + length Δ) lt :=
  lift_var []        []       Γ₁ s v           := v ;
  lift_var []        (δ :: Δ) Γ₁ s v           :=
    δ >>ₛ lift_var [] Δ Γ₁ s v ;
  lift_var (γ :: Γ₀) Δ        Γ₁ γ (γ >>₀ Γ) := γ >>₀ (Γ₀ ++ Δ ++ Γ₁) ;
  lift_var (γ :: Γ₀) Δ        Γ₁ s (γ >>ₛ v) :=
    γ >>ₛ (lift_var Γ₀ Δ Γ₁ s v).

Equations lift_tm (Γ₀ Δ Γ₁ : HOL_ctx) (s : st) (t : Γ₀ ++ Γ₁ ⊢ₛ s) :
  Γ₀ ++ Δ ++ Γ₁ ⊢ₛ s :=
  lift_tm Γ₀ Δ Γ₁ s ⟦ v ⟧ₛ := ⟦ lift_var Γ₀ Δ Γ₁ s v ⟧ₛ ;
  lift_tm Γ₀ Δ Γ₁ _ (ƛₛ s' t) :=
    ƛₛ s' (lift_tm (s' :: Γ₀) Δ Γ₁ _ t) ;
  lift_tm Γ₀ Δ Γ₁ s' (t @ₛ u) :=
    (lift_tm Γ₀ Δ Γ₁ _ t) @ₛ (lift_tm Γ₀ Δ Γ₁ _ u) ;
  lift_tm Γ₀ Δ Γ₁ _ ⟨⟩ₛ := ⟨⟩ₛ ;
  lift_tm Γ₀ Δ Γ₁ _ ⟨ t , u ⟩ₛ :=
    ⟨ lift_tm Γ₀ Δ Γ₁ _ t, lift_tm Γ₀ Δ Γ₁ _ u ⟩ₛ ;
  lift_tm Γ₀ Δ Γ₁ _ (π¹ₛ t) :=
    π¹ₛ (lift_tm Γ₀ Δ Γ₁ _ t) ;
  lift_tm Γ₀ Δ Γ₁ _ (π²ₛ t) :=
    π²ₛ (lift_tm Γ₀ Δ Γ₁ _ t) ;
  lift_tm Γ₀ Δ Γ₁ _ (empty_tm s) := empty_tm s ;
  lift_tm Γ₀ Δ Γ₁ _ (κ¹ₛ s' t) :=
    κ¹ₛ s' (lift_tm Γ₀ Δ Γ₁ _ t) ;
  lift_tm Γ₀ Δ Γ₁ _ (κ²ₛ s t) :=
    κ²ₛ s (lift_tm Γ₀ Δ Γ₁ _ t) ;
  lift_tm Γ₀ Δ Γ₁ _ (δₛ t u v) :=
    δₛ (lift_tm Γ₀ Δ Γ₁ _ t) (lift_tm Γ₀ Δ Γ₁ _ u) (lift_tm Γ₀ Δ Γ₁ _ v);
  lift_tm Γ₀ Δ Γ₁ _ 0ₛ := 0ₛ ;
  lift_tm Γ₀ Δ Γ₁ _ (Sₛ t) := Sₛ (lift_tm Γ₀ Δ Γ₁ _ t) ;
  lift_tm Γ₀ Δ Γ₁ _ (recℕₛ t u v) :=
    recℕₛ (lift_tm Γ₀ Δ Γ₁ _ t) (lift_tm Γ₀ Δ Γ₁ _ u) (lift_tm Γ₀ Δ Γ₁ _ v);
  lift_tm Γ₀ Δ Γ₁ _ ⊤ₛ := ⊤ₛ ;
  lift_tm Γ₀ Δ Γ₁ _ ⊥ₛ := ⊥ₛ ;
  lift_tm Γ₀ Δ Γ₁ _ (rec𝔹ₛ t u v) :=
    rec𝔹ₛ (lift_tm Γ₀ Δ Γ₁ _ t) (lift_tm Γ₀ Δ Γ₁ _ u) (lift_tm Γ₀ Δ Γ₁ _ v) ;
  lift_tm Γ₀ Δ Γ₁ _ []ₛ := []ₛ ;
  lift_tm Γ₀ Δ Γ₁ _ (t ::ₛ u) :=
    lift_tm Γ₀ Δ Γ₁ _ t ::ₛ lift_tm Γ₀ Δ Γ₁ _ u ;
  lift_tm Γ₀ Δ Γ₁ _ (rec𝕃ₛ t u v) :=
    rec𝕃ₛ (lift_tm Γ₀ Δ Γ₁ _ t) (lift_tm Γ₀ Δ Γ₁ _ u) (lift_tm Γ₀ Δ Γ₁ _ v) ;
  lift_tm Γ₀ Δ Γ₁ _ (φ ⇒ₛ ψ) := lift_tm Γ₀ Δ Γ₁ ℙₛ φ ⇒ₛ lift_tm Γ₀ Δ Γ₁ ℙₛ ψ ;
  lift_tm Γ₀ Δ Γ₁ _ (∀ₛ s' φ) := ∀ₛ s' (lift_tm (s' :: Γ₀) Δ Γ₁ ℙₛ φ).

Inductive HOL_ren : HOL_ctx -> HOL_ctx -> Type :=
| ren_nil : forall (Γ : HOL_ctx), HOL_ren Γ []
| ren_cons : forall {Γ Δ : HOL_ctx} {s : st},
     s ∈ˢ Γ -> HOL_ren Γ Δ -> HOL_ren Γ (s :: Δ).

Notation "Γ ⇝ Δ" := (HOL_ren Γ Δ) (at level 65).
Notation εᵣ := (ren_nil).
Notation "v ::ᵣ vs" := (ren_cons v vs) (at level 60).

Equations HOL_lift (Γ₀ Δ Γ₁ Δ' : HOL_ctx) (vars : Γ₀ ++ Γ₁ ⇝ Δ') :
  Γ₀ ++ Δ ++ Γ₁ ⇝ Δ' :=
  HOL_lift Γ₀ Δ Γ₁ Δ' (εᵣ _)   := εᵣ (Γ₀ ++ Δ ++ Γ₁) ;
  HOL_lift Γ₀ Δ Γ₁ _  (v ::ᵣ vs) :=
    lift_var Γ₀ Δ Γ₁ _ v ::ᵣ HOL_lift Γ₀ Δ Γ₁ _ vs.

Definition up_ren {Γ Δ : HOL_ctx} (ξ : Γ ⇝ Δ) (s : st) : (s :: Γ ⇝ s :: Δ) :=
  s >>₀ Γ ::ᵣ HOL_lift [] [s] Γ Δ ξ.

Definition up_tm {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s) (s' : st) : s' :: Γ ⊢ₛ s :=
  lift_tm [] [s'] Γ s t.

Notation "t ↑ₛ s" := (up_tm t s) (at level 55).
Notation "ξ ↑ᵣ s" := (up_ren ξ s) (at level 55).

Equations id_ren (Γ : HOL_ctx) : Γ ⇝ Γ :=
  id_ren [] := ren_nil [] ;
  id_ren (s :: Γ) := (id_ren Γ) ↑ᵣ s.

Equations ren_var (Γ Δ : HOL_ctx) (s : st) (ξ : Γ ⇝ Δ) (v : s ∈ˢ Δ) : s ∈ˢ Γ :=
  ren_var Γ (s :: Δ) s (ξ₀ ::ᵣ ξ) (s >>₀ Δ) := ξ₀ ;
  ren_var Γ (s :: Δ) _ (ξ₀ ::ᵣ ξ) (s >>ₛ v) := ren_var Γ Δ _ ξ v.

Equations ren_tm (Γ Δ : HOL_ctx) (s : st) (ξ : Γ ⇝ Δ) (t : Δ ⊢ₛ s) :
  Γ ⊢ₛ s :=
  ren_tm Γ Δ _ ξ ⟦ v ⟧ₛ := ⟦ ren_var Γ Δ _ ξ v ⟧ₛ ;
  ren_tm Γ Δ _ ξ (ƛₛ s' t) := ƛₛ s' (ren_tm (s' :: Γ) (s' :: Δ) _ (ξ ↑ᵣ s') t) ;
  ren_tm Γ Δ _ ξ (t @ₛ u) := (ren_tm Γ Δ _ ξ t) @ₛ (ren_tm Γ Δ _ ξ u) ;
  ren_tm Γ Δ _ ξ ⟨⟩ₛ := ⟨⟩ₛ ;
  ren_tm Γ Δ _ ξ ⟨ t , u ⟩ₛ :=
    ⟨ ren_tm Γ Δ _ ξ t, ren_tm Γ Δ _ ξ u ⟩ₛ ;
  ren_tm Γ Δ _ ξ (π¹ₛ t) := π¹ₛ (ren_tm Γ Δ _ ξ t) ;
  ren_tm Γ Δ _ ξ (π²ₛ t) := π²ₛ (ren_tm Γ Δ _ ξ t) ;
  ren_tm Γ Δ _ ξ (empty_tm s) := empty_tm s ;
  ren_tm Γ Δ _ ξ (κ¹ₛ _ t) := κ¹ₛ _ (ren_tm Γ Δ _ ξ t) ;
  ren_tm Γ Δ _ ξ (κ²ₛ _ t) := κ²ₛ _ (ren_tm Γ Δ _ ξ t) ;
  ren_tm Γ Δ _ ξ (δₛ t u v) :=
    δₛ (ren_tm Γ Δ _ ξ t) (ren_tm Γ Δ _ ξ u) (ren_tm Γ Δ _ ξ v) ;
  ren_tm Γ Δ _ ξ 0ₛ := 0ₛ ;
  ren_tm Γ Δ _ ξ (Sₛ t) := Sₛ (ren_tm Γ Δ _ ξ t) ;
  ren_tm Γ Δ _ ξ (recℕₛ t u v) :=
    recℕₛ (ren_tm Γ Δ _ ξ t) (ren_tm Γ Δ _ ξ u) (ren_tm Γ Δ _ ξ v) ;
  ren_tm Γ Δ _ ξ ⊤ₛ := ⊤ₛ ;
  ren_tm Γ Δ _ ξ ⊥ₛ := ⊥ₛ ;
  ren_tm Γ Δ _ ξ (rec𝔹ₛ t u v) :=
    rec𝔹ₛ (ren_tm Γ Δ _ ξ t) (ren_tm Γ Δ _ ξ u) (ren_tm Γ Δ _ ξ v) ;
  ren_tm Γ Δ _ ξ []ₛ := []ₛ ;
  ren_tm Γ Δ _ ξ (t ::ₛ u) := (ren_tm Γ Δ _ ξ t) ::ₛ (ren_tm Γ Δ _ ξ u) ;
  ren_tm Γ Δ _ ξ (rec𝕃ₛ t u v) :=
    rec𝕃ₛ (ren_tm Γ Δ _ ξ t) (ren_tm Γ Δ _ ξ u) (ren_tm Γ Δ _ ξ v) ;
  ren_tm Γ Δ _ ξ (φ ⇒ₛ ψ) := (ren_tm Γ Δ _ ξ φ) ⇒ₛ (ren_tm Γ Δ _ ξ ψ) ;
  ren_tm Γ Δ _ ξ (∀ₛ s' φ) := ∀ₛ s' (ren_tm (s' :: Γ) (s' :: Δ) _ (ξ ↑ᵣ s') φ).

Inductive HOL_vec : HOL_ctx -> HOL_ctx -> Type :=
| vec_nil : forall Γ, HOL_vec Γ []
| vec_cons : forall {Γ Δ : HOL_ctx} {s : st},
    Γ ⊢ₛ s -> HOL_vec Γ Δ -> HOL_vec Γ (s :: Δ).

Notation "Γ ⊢ᵥ Δ" := (HOL_vec Γ Δ) (at level 63).
Notation εᵥ := vec_nil.
Notation "t ::ᵥ v" := (vec_cons t v) (at level 60).

Fixpoint ren_to_vec {Γ Δ : HOL_ctx} (ξ : Γ ⇝ Δ) : Γ ⊢ᵥ Δ :=
  match ξ with
  | εᵣ _ => εᵥ _
  | v ::ᵣ vs => ⟦ v ⟧ₛ ::ᵥ (ren_to_vec vs)
  end.

Definition id_subst (Γ : HOL_ctx) : Γ ⊢ᵥ Γ := ren_to_vec (id_ren Γ).

Equations lift_vec (Γ₀ Δ Γ₁ Δ' : HOL_ctx) (v : Γ₀ ++ Γ₁ ⊢ᵥ Δ') :
  Γ₀ ++ Δ ++ Γ₁ ⊢ᵥ Δ' :=
  lift_vec Γ₀ Δ Γ₁ []         (εᵥ _)    := εᵥ (Γ₀ ++ Δ ++ Γ₁) ;
  lift_vec Γ₀ Δ Γ₁ (s' :: Δ') (t ::ᵥ v) :=
    lift_tm Γ₀ Δ Γ₁ s' t ::ᵥ lift_vec Γ₀ Δ Γ₁ Δ' v.

Definition lift1_vec {Γ Δ : HOL_ctx} (v : Γ ⊢ᵥ Δ) (s : st) : s :: Γ ⊢ᵥ Δ :=
  lift_vec [] [s] Γ Δ v.

Definition up_vec {Γ Δ : HOL_ctx} (t : Γ ⊢ᵥ Δ) (s : st) : s :: Γ ⊢ᵥ s :: Δ :=
  ⟦ s >>₀ Γ ⟧ₛ ::ᵥ lift1_vec t s.

Notation "v ↑ᵥ s" := (up_vec v s) (at level 55).

Equations get_subst_var {Γ Δ : HOL_ctx} {s : st} (ve : Γ ⊢ᵥ Δ) (v : s ∈ˢ Δ) :
  Γ ⊢ₛ s :=
  get_subst_var (t ::ᵥ ve) (_ >>₀ _) := t ;
  get_subst_var (t ::ᵥ ve) (_ >>ₛ v) := get_subst_var ve v.

Equations subst_tm {Γ Δ : HOL_ctx} {s : st} (ve : Γ ⊢ᵥ Δ) (t : Δ ⊢ₛ s) :
  Γ ⊢ₛ s :=
  subst_tm ve ⟦ v ⟧ₛ := get_subst_var ve v ;
  subst_tm ve (ƛₛ s' t) := ƛₛ s' (subst_tm (ve ↑ᵥ s') t) ;
  subst_tm ve (t @ₛ u) := (subst_tm ve t) @ₛ (subst_tm ve u) ;
  subst_tm ve ⟨⟩ₛ := ⟨⟩ₛ ;
  subst_tm ve ⟨ t, u ⟩ₛ := ⟨ subst_tm ve t, subst_tm ve u ⟩ₛ ;
  subst_tm ve (π¹ₛ t) := π¹ₛ (subst_tm ve t) ;
  subst_tm ve (π²ₛ t) := π²ₛ (subst_tm ve t) ;
  subst_tm ve (empty_tm _) := empty_tm _ ;
  subst_tm ve (κ¹ₛ _ t) := κ¹ₛ _ (subst_tm ve t) ;
  subst_tm ve (κ²ₛ _ t) := κ²ₛ _ (subst_tm ve t) ;
  subst_tm ve (δₛ t u v) :=
    δₛ (subst_tm ve t) (subst_tm ve u) (subst_tm ve v) ;
  subst_tm ve 0ₛ := 0ₛ ;
  subst_tm ve (Sₛ t) := Sₛ (subst_tm ve t) ;
  subst_tm ve (recℕₛ t u v) :=
    recℕₛ (subst_tm ve t) (subst_tm ve u) (subst_tm ve v) ;
  subst_tm ve ⊤ₛ := ⊤ₛ ;
  subst_tm ve ⊥ₛ := ⊥ₛ ;
  subst_tm ve (rec𝔹ₛ t u v) :=
    rec𝔹ₛ (subst_tm ve t) (subst_tm ve u) (subst_tm ve v) ;
  subst_tm ve []ₛ := []ₛ ;
  subst_tm ve (t ::ₛ u) := (subst_tm ve t) ::ₛ (subst_tm ve u) ;
  subst_tm ve (rec𝕃ₛ t u v) :=
    rec𝕃ₛ (subst_tm ve t) (subst_tm ve u) (subst_tm ve v) ;
  subst_tm ve (φ ⇒ₛ ψ) := (subst_tm ve φ) ⇒ₛ (subst_tm ve ψ) ;
  subst_tm ve (∀ₛ s' φ) := ∀ₛ s' (subst_tm (ve ↑ᵥ s') φ).

Notation "t ⟨[ v ]⟩" := (subst_tm v t) (at level 60).

Equations comp_vec {Γ₀ Γ₁ Γ₂ : HOL_ctx} (v : Γ₀ ⊢ᵥ Γ₁) (v' : Γ₁ ⊢ᵥ Γ₂) :
  Γ₀ ⊢ᵥ Γ₂ :=
  comp_vec v (εᵥ _) := εᵥ _ ;
  comp_vec v (t ::ᵥ v') := t ⟨[ v ]⟩ ::ᵥ comp_vec v v'.

Notation "v ∘ᵥ v'" := (comp_vec v' v) (at level 61).

Lemma subst_id :
  forall (Γ : HOL_ctx) (s : st) (t : Γ ⊢ₛ s),
    t ⟨[id_subst Γ]⟩ = t.
Proof.
  intros. induction t.
  - unfold id_subst.
    autorewrite with subst_tm.
    induction h.
    + autorewrite with id_ren. simpl. autorewrite with get_subst_var.
      reflexivity.
    + autorewrite with id_ren. simpl. autorewrite with get_subst_var.
Admitted.
         
Lemma id_comp_r :
  forall (Γ Δ : HOL_ctx) (v : Γ ⊢ᵥ Δ), v ∘ᵥ id_subst Γ = v.
Proof.
  intros. induction v.
  reflexivity.
  autorewrite with comp_vec. rewrite IHv. f_equal. apply subst_id.
Qed.

Lemma id_comp_l :
  forall (Γ Δ : HOL_ctx) (v : Γ ⊢ᵥ Δ), id_subst Δ ∘ᵥ v = v.
Proof.
  intros. induction v.
  reflexivity.
  autorewrite with comp_vec. unfold id_subst.
  autorewrite with id_ren.
Admitted.

Lemma subst_up :
  forall (Γ Δ : HOL_ctx) (s s' : st) (v : Γ ⊢ᵥ Δ) (t : Δ ⊢ₛ s),
    (t ↑ₛ s') ⟨[ v ↑ᵥ s' ]⟩ = t ⟨[ v ]⟩ ↑ₛ s'.
Admitted.

Lemma subst_subst :
  forall (Γ Δ Θ : HOL_ctx) (s : st) (v : Γ ⊢ᵥ Δ) (v' : Δ ⊢ᵥ Θ) (t : Θ ⊢ₛ s),
    t ⟨[ v' ]⟩ ⟨[ v ]⟩ = t ⟨[ v' ∘ᵥ v ]⟩.
Proof.
Admitted.
