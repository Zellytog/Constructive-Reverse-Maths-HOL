Require Import CRM.HOL.Base.

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Import ListNotations.

Definition HOL_ctx : Type := list st.

Inductive bind : nat -> st -> HOL_ctx -> Prop :=
| bind_z : forall {s : st} {Γ : HOL_ctx}, bind 0 s (s :: Γ)
| bind_s : forall {n : nat} {s s' : st} {Γ : HOL_ctx},
    bind n s Γ -> bind (S n) s (s' :: Γ).

Notation "⟪ n → s ⟫ ∈ˢ Γ" := (bind n s Γ) (at level 85).

Reserved Notation "Γ ⊢ t ~: s" (at level 87).

Inductive typing : HOL_ctx -> tm -> st -> Prop :=
| typ_var : forall {n : nat} {s : st} {Γ : HOL_ctx},
    ⟪ n → s ⟫ ∈ˢ Γ -> Γ ⊢ ⟦ n ⟧ₛ ~: s
| typ_lam : forall {t : tm} {s s' : st} {Γ : HOL_ctx},
    s :: Γ ⊢ t ~: s' -> Γ ⊢ ƛ t ~: s →ₛ s'
| typ_app : forall {t u : tm} {s s' : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s →ₛ s' -> Γ ⊢ u ~: s -> Γ ⊢ (app_tm t u) ~: s'
| typ_z : forall {Γ : HOL_ctx}, Γ ⊢ Zₛ ~: ℕₛ
| typ_s : forall {t : tm} {Γ : HOL_ctx},
    Γ ⊢ t ~: ℕₛ -> Γ ⊢ Sₛ t ~: ℕₛ
| typ_recN : forall {t u v : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s →ₛ ℕₛ →ₛ s -> Γ ⊢ v ~: ℕₛ ->
    Γ ⊢ recℕₛ t u v ~: s
| typ_tt : forall {Γ : HOL_ctx}, Γ ⊢ ttₛ ~: 𝔹ₛ
| typ_ff : forall {Γ : HOL_ctx}, Γ ⊢ ffₛ ~: 𝔹ₛ
| typ_recB : forall {t u v : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s -> Γ ⊢ v ~: 𝔹ₛ ->
    Γ ⊢ recℕₛ t u v ~: s
| typ_nil : forall {s : st} {Γ : HOL_ctx}, Γ ⊢ []ₛ ~: 𝕃ₛ s
| typ_cons : forall {t u : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: 𝕃ₛ s -> Γ ⊢ t ::ₛ u ~: 𝕃ₛ s
| typ_recL : forall {t u v : tm} {s s' : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s →ₛ s' →ₛ 𝕃ₛ s' →ₛ s -> Γ ⊢ v ~: 𝕃ₛ s' ->
    Γ ⊢ recℕₛ t u v ~: s
| typ_imp : forall {φ ψ : tm} {Γ : HOL_ctx},
    Γ ⊢ φ ~: ℙₛ -> Γ ⊢ ψ ~: ℙₛ -> Γ ⊢ φ ⇒ₛ ψ ~: ℙₛ
| typ_forall : forall {φ : tm} {s : st} {Γ : HOL_ctx},
    s :: Γ ⊢ φ ~: ℙₛ -> Γ ⊢ ∀ₛ φ ~: ℙₛ
| typ_sort : forall {t : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ 𝕊 t ~: ℙₛ
where "Γ ⊢ t ~: s" := (typing Γ t s).

Notation " n⊢ t ~: s" := (typing [] t s) (at level 87).

Proposition id_typed : forall (s : st), n⊢ ƛ ⟦ 0 ⟧ₛ ~: s →ₛ s.
Proof.
  intro. repeat constructor.
Qed.
