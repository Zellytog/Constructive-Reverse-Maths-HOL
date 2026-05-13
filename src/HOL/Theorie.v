Require Import Base.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Program.Equality.

Definition proof_ctx (Γ : HOL_ctx) : Type := list (Γ ⊢ₛ ℙₛ).

(* Standardity predicate are defined inductively :
ℕ(x) ≜ ∀ X : ℕ → ℙ, X 0 ⇒ (∀ n : ℕ, X n ⇒ X (n + 1)) ⇒ X x
𝔹(x) ≜ ∀ X : 𝔹 → ℙ, X ⊤ ⇒ X ⊥ ⇒ X x
(𝕃ₛ S)(x) ≜
  ∀ X : 𝕃ₛ S → ℙ, X [] ⇒ (∀ (s : S) (l : 𝕃ₛ), S(x) ⇒ X l ⇒ X (s :: l)) ⇒ X x
ℙ(φ) ≜ True
𝟙(x) ≜ ∀ X : 𝟙 → ℙ, X ⟨⟩ ⇒ X x
𝟘(x) ≜ ∀ X : 𝟘 → ℙ, X x
(S → T)(f) ≜ ∀ s : S, S(s) ⇒ T(f x)
(S × T)(x) ≜ S(π₁ x) ∧ S(π₂ x)
(S + T)(x) ≜
  ∀ X : S + T → ℙ, (∀ s : S, X(κ₁ s)) ⇒ (∀ t : T, X(κ₂ t)) ⇒ X x
*)

Notation vz := (vz_tm _ _).
Notation vs := (vs_tm _).

Equations Standardity (Γ : HOL_ctx) (s : st) : Γ ⊢ₛ s →ₛ ℙₛ :=
  Standardity Γ ℕₛ :=
    ƛₛ ℕₛ
      (∀ₛ (ℕₛ →ₛ ℙₛ)
        ((⟦ vz ⟧ₛ @ₛ 0ₛ) ⇒ₛ
           (∀ₛ ℕₛ (⟦ vs vz ⟧ₛ @ₛ ⟦ vz ⟧ₛ ⇒ₛ ⟦ vs vz ⟧ₛ @ₛ Sₛ ⟦ vz ⟧ₛ)) ⇒ₛ
           ⟦ vz ⟧ₛ @ₛ ⟦ vs vz ⟧ₛ)) ;
  Standardity Γ 𝔹ₛ :=
    ƛₛ 𝔹ₛ
      (∀ₛ (𝔹ₛ →ₛ ℙₛ)
        ((⟦ vz ⟧ₛ @ₛ ⊤ₛ) ⇒ₛ (⟦ vz ⟧ₛ @ₛ ⊥ₛ) ⇒ₛ (⟦ vz ⟧ₛ @ₛ ⟦ vs vz ⟧ₛ))) ;
  Standardity Γ (𝕃ₛ s) :=
    ƛₛ (𝕃ₛ s)
      (∀ₛ (𝕃ₛ s →ₛ ℙₛ)
        ((⟦ vz ⟧ₛ @ₛ []ₛ) ⇒ₛ
           (∀ₛ s ((Standardity _ s) @ₛ ⟦ vz ⟧ₛ ⇒ₛ
                    (∀ₛ (𝕃ₛ s)
                      (⟦ vs (vs vz) ⟧ₛ @ₛ ⟦ vz ⟧ₛ ⇒ₛ
                         ⟦ vs (vs vz) ⟧ₛ @ₛ (⟦ vs vz ⟧ₛ ::ₛ ⟦ vz ⟧ₛ))))) ⇒ₛ
           ⟦ vz ⟧ₛ @ₛ ⟦ vs vz ⟧ₛ)) ;
  Standardity Γ ℙₛ := ƛₛ ℙₛ (∀ₛ ℙₛ (⟦ vz ⟧ₛ ⇒ₛ ⟦ vz ⟧ₛ)) ;
  Standardity Γ 𝟙ₛ := ƛₛ 𝟙ₛ (∀ₛ (𝟙ₛ →ₛ ℙₛ) (⟦ vz ⟧ₛ @ₛ ⟨⟩ₛ ⇒ₛ ⟦ vz ⟧ₛ @ₛ ⟦ vs vz ⟧ₛ)) ;
  Standardity Γ 𝟘ₛ := ƛₛ 𝟘ₛ (∀ₛ (𝟘ₛ →ₛ ℙₛ) (⟦ vz ⟧ₛ @ₛ ⟦ vs vz ⟧ₛ)) ;
  Standardity Γ (s →ₛ t) :=
    ƛₛ (s →ₛ t) (∀ₛ s (Standardity _ s @ₛ ⟦ vz ⟧ₛ ⇒ₛ
                        Standardity _ t @ₛ (⟦ vs vz ⟧ₛ @ₛ ⟦ vz ⟧ₛ))) ;
  Standardity Γ (s ×ₛ t) :=
    ƛₛ (s ×ₛ t)
      (∀ₛ (s ×ₛ t →ₛ ℙₛ) (
           (∀ₛ s (Standardity _ s @ₛ ⟦ vz ⟧ₛ ⇒ₛ
                  (∀ₛ t (Standardity _ t @ₛ ⟦ vz ⟧ₛ ⇒ₛ
                          (⟦ vs (vs vz) ⟧ₛ @ₛ ⟨ ⟦ vs vz ⟧ₛ, ⟦ vz ⟧ₛ ⟩ₛ))))) ⇒ₛ
             ⟦ vz ⟧ₛ @ₛ ⟦ vs vz ⟧ₛ)) ;
  Standardity Γ (s +ₛ t) :=
    ƛₛ (s +ₛ t)
      (∀ₛ (s +ₛ t →ₛ ℙₛ) (
           (∀ₛ s (Standardity _ s @ₛ ⟦ vz ⟧ₛ ⇒ₛ ⟦ vs vz ⟧ₛ @ₛ κ¹ₛ _ ⟦ vz ⟧ₛ)) ⇒ₛ
             (∀ₛ t (Standardity _ t @ₛ ⟦ vz ⟧ₛ ⇒ₛ ⟦ vs vz ⟧ₛ @ₛ κ²ₛ _ ⟦ vz ⟧ₛ)) ⇒ₛ
             ⟦ vz ⟧ₛ @ₛ ⟦ vs vz ⟧ₛ)).

Inductive proof : forall (Γ : HOL_ctx), proof_ctx Γ -> Γ ⊢ₛ ℙₛ -> Prop :=
| pr_ax : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ} {φ : Γ ⊢ₛ ℙₛ},
    In φ Ξ -> proof Γ Ξ φ
| pr_imp_i : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ} {φ ψ : Γ ⊢ₛ ℙₛ},
    proof Γ (φ :: Ξ) ψ -> proof Γ Ξ (φ ⇒ₛ ψ)
| pr_imp_e : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ} (φ : Γ ⊢ₛ ℙₛ) {ψ : Γ ⊢ₛ ℙₛ},
    proof Γ Ξ (φ ⇒ₛ ψ) -> proof Γ Ξ φ -> proof Γ Ξ ψ
| pr_fora_i : forall {Γ : HOL_ctx} {s : st} {Ξ : proof_ctx Γ}
                     {φ : s :: Γ ⊢ₛ ℙₛ},
    proof (s :: Γ) (map (fun φ => φ ↑ₛ s) Ξ) φ -> proof Γ Ξ (∀ₛ s φ)
| pr_fora_e : forall {Γ : HOL_ctx} {s : st} {Ξ : proof_ctx Γ}
                     {φ : s :: Γ ⊢ₛ ℙₛ} (t : Γ ⊢ₛ s),
    proof Γ Ξ (∀ₛ s φ) -> proof Γ Ξ (φ ⟨[ t ::ᵥ id_subst Γ ]⟩)
| pr_stand : forall {Γ : HOL_ctx} (s : st) {Ξ : proof_ctx Γ},
    proof Γ Ξ (∀ₛ s (Standardity (s :: Γ) s @ₛ ⟦ vz ⟧ₛ)).

Notation "Γ ∣ Ξ ⊢ᴴᴼᴸ φ" := (proof Γ Ξ φ) (at level 65).

Lemma lift_proof :
  forall (Γ₀ Δ Γ₁ : HOL_ctx) (Ξ : proof_ctx (Γ₀ ++ Γ₁)) (φ : Γ₀ ++ Γ₁ ⊢ₛ ℙₛ),
    Γ₀ ++ Γ₁ ∣ Ξ ⊢ᴴᴼᴸ φ ->
    Γ₀ ++ Δ ++ Γ₁ ∣ map (lift_tm Γ₀ Δ Γ₁ ℙₛ) Ξ ⊢ᴴᴼᴸ lift_tm Γ₀ Δ Γ₁ ℙₛ φ.
Proof.
  intros. dependent induction H.
  - admit.
  - autorewrite with lift_tm.
    apply pr_imp_i.
    specialize (IHproof Γ₀ Γ₁ (φ0 :: Ξ) ψ). apply IHproof; reflexivity.
  - apply (pr_imp_e (lift_tm Γ₀ Δ Γ₁ _ φ0)).
    specialize (IHproof1 Γ₀ Γ₁ Ξ (φ0 ⇒ₛ φ)). apply IHproof1; reflexivity.
    apply IHproof2; reflexivity.
  - autorewrite with lift_tm. apply pr_fora_i.
    specialize (IHproof (s :: Γ₀) Γ₁ (map (fun φ => φ ↑ₛ s) Ξ)).
    rewrite map_map in IHproof.
    rewrite map_map.
    assert (map (fun x => lift_tm (s :: Γ₀) Δ Γ₁ ℙₛ (x ↑ₛ s)) Ξ =
              map (fun x => lift_tm Γ₀ Δ Γ₁ ℙₛ x ↑ₛ s) Ξ).
    apply map_ext. intro φ. admit.
    rewrite <- H0. apply IHproof; reflexivity.
  - specialize (IHproof Γ₀ Γ₁ Ξ (∀ₛ s φ0) JMeq_refl JMeq_refl JMeq_refl).
    autorewrite with lift_tm in IHproof.
    apply (pr_fora_e (lift_tm Γ₀ Δ Γ₁ s t)) in IHproof.
    admit.
  - admit.
Admitted.

