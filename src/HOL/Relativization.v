From CRM Require Import Base Reduction Theorie Relations.
From Stdlib Require Import List.
Import ListNotations.

(* A relativizing predicate is a family of predicate Γ ⊢ₛ s →ₛ ℙₛ for any
 Γ, s.*)

Definition relat_pred : Type := forall (Γ : HOL_ctx) (s : st), Γ ⊢ₛ s →ₛ ℙₛ.

Record admissible_pred (P : relat_pred) :=
  { adm_lam : forall {Γ : HOL_ctx} {s s' : st} {Ξ : proof_ctx Γ}
                     {t : s :: Γ ⊢ₛ s'},
      (s :: Γ) ∣ (P (s :: Γ) s @ₛ ⟦ vz ⟧ₛ) :: map (fun x => up_tm x s) Ξ ⊢ᴴᴼᴸ
        P (s :: Γ) s' @ₛ t ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s →ₛ s') @ₛ (ƛₛ s t)
  ; adm_app : forall {Γ : HOL_ctx} (s : st) {s' : st} {Ξ : proof_ctx Γ}
                     {t : Γ ⊢ₛ s →ₛ s'} {u : Γ ⊢ₛ s},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s →ₛ s') @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ u ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s' @ₛ (t @ₛ u)
  ; adm_unit : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ 𝟙ₛ @ₛ ⟨⟩ₛ
  ; adm_pair : forall {Γ : HOL_ctx} {s s' : st} {Ξ : proof_ctx Γ}
                      {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ s'},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s' @ₛ u ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s ×ₛ s') @ₛ ⟨ t, u ⟩ₛ
  ; adm_proj1 : forall {Γ : HOL_ctx} {s s' : st} {Ξ : proof_ctx Γ}
                       {t : Γ ⊢ₛ s ×ₛ s'},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s ×ₛ s') @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ (π¹ₛ t)
  ; adm_proj2 : forall {Γ : HOL_ctx} {s s' : st} {Ξ : proof_ctx Γ}
                       {t : Γ ⊢ₛ s ×ₛ s'},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s ×ₛ s') @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s' @ₛ (π²ₛ t)
  ; adm_empty : forall {Γ : HOL_ctx} (s : st) {Ξ : proof_ctx Γ},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (𝟘ₛ →ₛ s) @ₛ empty_tm s
  ; adm_coproj1 : forall {Γ : HOL_ctx} {s s' : st} {Ξ : proof_ctx Γ}
                         {t : Γ ⊢ₛ s},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s +ₛ s') @ₛ (κ¹ₛ s' t)
  ; adm_coproj2 : forall {Γ : HOL_ctx} {s s' : st} {Ξ : proof_ctx Γ}
                         {t : Γ ⊢ₛ s'},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s' @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s +ₛ s') @ₛ (κ²ₛ s t)
  ; adm_delta : forall {Γ : HOL_ctx} {s s' s'' : st} {Ξ : proof_ctx Γ}
                       {t : Γ ⊢ₛ s +ₛ s'}
                       {u : Γ ⊢ₛ s →ₛ s''} {v : Γ ⊢ₛ s' →ₛ s''},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s +ₛ s') @ₛ t ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s →ₛ s'') @ₛ u -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (s' →ₛ s'') @ₛ v ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s'' @ₛ (δₛ t u v)
  ; adm_Z : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ}, Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℕₛ @ₛ 0ₛ
  ; adm_S : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ} {t : Γ ⊢ₛ ℕₛ},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℕₛ @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℕₛ @ₛ (Sₛ t)
  ; adm_recN : forall {Γ : HOL_ctx} {s : st} {Ξ : proof_ctx Γ}
                      {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s} {v : Γ ⊢ₛ ℕₛ},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ _ @ₛ u -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℕₛ @ₛ v ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ (recℕₛ t u v)
  ; adm_T : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ}, Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ 𝔹ₛ @ₛ ⊤ₛ
  ; adm_F : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ}, Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ 𝔹ₛ @ₛ ⊥ₛ
  ; adm_recB : forall {Γ : HOL_ctx} {s : st} {Ξ : proof_ctx Γ}
                      {t u : Γ ⊢ₛ s} {v : Γ ⊢ₛ 𝔹ₛ},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ u -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ 𝔹ₛ @ₛ v ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ (rec𝔹ₛ t u v)
  ; adm_nil : forall {Γ : HOL_ctx} {s : st} {Ξ : proof_ctx Γ},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (𝕃ₛ s) @ₛ []ₛ
  ; adm_cons : forall {Γ : HOL_ctx} {s : st} {Ξ : proof_ctx Γ}
                      {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ 𝕃ₛ s},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (𝕃ₛ s) @ₛ u ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ (𝕃ₛ s) @ₛ (t ::ₛ u)
  ; adm_recL : forall {Γ : HOL_ctx} {s : st} (s' : st) {Ξ : proof_ctx Γ}
                      {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s}
                      {v : Γ ⊢ₛ 𝕃ₛ s'},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ t -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ _ @ₛ u -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ _ @ₛ v ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ s @ₛ (rec𝕃ₛ t u v)
  ; adm_imp : forall {Γ : HOL_ctx} {Ξ : proof_ctx Γ} {φ ψ : Γ ⊢ₛ ℙₛ},
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℙₛ @ₛ φ -> Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℙₛ @ₛ ψ ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℙₛ @ₛ (φ ⇒ₛ ψ)
  ; adm_fora : forall {Γ : HOL_ctx} {s : st} {Ξ : proof_ctx Γ}
                      {φ : s :: Γ ⊢ₛ ℙₛ},
      (s :: Γ) ∣ (P (s :: Γ) s @ₛ ⟦ vz ⟧ₛ) :: map (fun x => up_tm x s) Ξ ⊢ᴴᴼᴸ
        P (s :: Γ) ℙₛ @ₛ φ ->
      Γ ∣ Ξ ⊢ᴴᴼᴸ P Γ ℙₛ @ₛ (∀ₛ s φ)
  ; adm_lift : forall {Γ₀ Δ Γ₁ : HOL_ctx} {s : st},
      lift_tm Γ₀ Δ Γ₁ (s →ₛ ℙₛ) (P (Γ₀ ++ Γ₁) s) = P (Γ₀ ++ Δ ++ Γ₁) s
  ; adm_subst : forall {Γ Δ : HOL_ctx} {s : st} (v : Γ ⊢ᵥ Δ),
      P Δ s ⟨[ v ]⟩ = P Γ s
  }.

Fixpoint relat_add_ctx (P : relat_pred) (Γ : HOL_ctx) : proof_ctx Γ :=
  match Γ with
  | nil => nil
  | s :: Γ' =>
      P (s :: Γ') s @ₛ ⟦ vz ⟧ₛ :: map (fun x => up_tm x s) (relat_add_ctx P Γ')
  end.

Theorem adequacy_relat_tm :
  forall (P : relat_pred),
    admissible_pred P -> forall (Γ : HOL_ctx) (s : st) (t : Γ ⊢ₛ s),
      Γ ∣ relat_add_ctx P Γ ⊢ᴴᴼᴸ P Γ s @ₛ t.
Proof.
  intros. induction t;
    [ |
      apply adm_lam | apply adm_app | apply adm_unit | apply adm_pair |
      apply adm_proj1 | apply adm_proj2 | apply adm_empty | apply adm_coproj1 |
      apply adm_coproj2 | apply adm_delta | apply adm_Z | apply adm_S |
      apply adm_recN | apply adm_T | apply adm_F | apply adm_recB |
      apply adm_nil | apply adm_cons | apply adm_recL | apply adm_imp |
      apply adm_fora];
    try assumption.
  - apply pr_ax. induction h.
    + simpl. left; reflexivity.
    + right.
      assert (P (s' :: Γ) s @ₛ ⟦ vs h ⟧ₛ = P Γ s @ₛ ⟦ h ⟧ₛ ↑ₛ s').
      unfold up_tm. autorewrite with lift_tm lift_var.
      rewrite adm_lift. simpl. reflexivity. apply H.
      rewrite H0. apply (in_map _ _ _ IHh).
Qed.

Equations relat_tm (P : relat_pred) {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s) :
  Γ ⊢ₛ s :=
  relat_tm P ⟦ h ⟧ₛ := ⟦ h ⟧ₛ ;
  relat_tm P (ƛₛ s t) := ƛₛ s (relat_tm P t) ;
  relat_tm P (t @ₛ u) := (relat_tm P t) @ₛ (relat_tm P u) ;
  relat_tm P ⟨⟩ₛ := ⟨⟩ₛ ;
  relat_tm P ⟨ t, u ⟩ₛ := ⟨ relat_tm P t, relat_tm P u ⟩ₛ ;
  relat_tm P (π¹ₛ t) := π¹ₛ (relat_tm P t) ;
  relat_tm P (π²ₛ t) := π²ₛ (relat_tm P t) ;
  relat_tm P (empty_tm s) := empty_tm s ;
  relat_tm P (κ¹ₛ _ t) := κ¹ₛ _ (relat_tm P t) ;
  relat_tm P (κ²ₛ _ t) := κ²ₛ _ (relat_tm P t) ;
  relat_tm P (δₛ t u v) :=
    δₛ (relat_tm P t) (relat_tm P u) (relat_tm P v) ;
  relat_tm P 0ₛ := 0ₛ ;
  relat_tm P (Sₛ t) := Sₛ (relat_tm P t) ;
  relat_tm P (recℕₛ t u v) :=
    recℕₛ (relat_tm P t) (relat_tm P u) (relat_tm P v) ;
  relat_tm P ⊤ₛ := ⊤ₛ ;
  relat_tm P ⊥ₛ := ⊥ₛ ;
  relat_tm P (rec𝔹ₛ t u v) :=
    rec𝔹ₛ (relat_tm P t) (relat_tm P u) (relat_tm P v) ;
  relat_tm P []ₛ := []ₛ ;
  relat_tm P (t ::ₛ u) := (relat_tm P t) ::ₛ (relat_tm P u) ;
  relat_tm P (rec𝕃ₛ t u v) :=
    rec𝕃ₛ (relat_tm P t) (relat_tm P u) (relat_tm P v) ;
  relat_tm P (φ ⇒ₛ ψ) := (relat_tm P φ) ⇒ₛ (relat_tm P ψ) ;
  relat_tm P (∀ₛ s φ) := ∀ₛ s (P _ _ @ₛ ⟦ vz ⟧ₛ ⇒ₛ relat_tm P φ).

Definition relat_ctx (P : relat_pred) {Γ : HOL_ctx} :
  proof_ctx Γ -> proof_ctx Γ := map (relat_tm P).

Lemma eq_relat :
  forall (P : relat_pred) {Γ : HOL_ctx} {s : st} {t u : Γ ⊢ₛ s},
    t =ₛ u -> relat_tm P t =ₛ relat_tm P u.
Proof.
Admitted.

Lemma relat_subst :
  forall (P : relat_pred) {Γ Δ: HOL_ctx} {s : st} {v : Γ ⊢ᵥ Δ} {t : Δ ⊢ₛ s},
    relat_tm P (t ⟨[ v ]⟩) = relat_tm P t ⟨[ v ]⟩.
Proof.
Admitted.

Lemma stand_relat :
  forall (P : relat_pred) {Γ : HOL_ctx} {s : st},
    relat_tm P (Standardity Γ s) = Standardity Γ s.
Proof.
Admitted.

Theorem adequacy_relat :
  forall (P : relat_pred) {Γ : HOL_ctx} {Ξ : proof_ctx Γ} {φ : Γ ⊢ₛ ℙₛ},
    admissible_pred P ->
    Γ ∣ Ξ ⊢ᴴᴼᴸ φ -> Γ ∣ relat_add_ctx P Γ ++ relat_ctx P Ξ ⊢ᴴᴼᴸ relat_tm P φ.
Proof.
  intros P Γ Ξ φ aP H. induction H.
  - apply pr_ax. apply in_or_app. right. apply in_map. apply H.
  - apply (pr_red (relat_tm P φ)). apply eq_relat. apply H.
    apply IHproof.
  - autorewrite with relat_tm. apply pr_imp_i.
    simpl in IHproof. admit.
  - apply (pr_imp_e (relat_tm P φ)). apply IHproof1. apply IHproof2.
  - autorewrite with relat_tm. apply pr_fora_i. apply pr_imp_i.
    simpl in IHproof. admit.
  - assert (Γ ∣ relat_add_ctx P Γ ++ relat_ctx P Ξ ⊢ᴴᴼᴸ P Γ s @ₛ t).
    apply (pr_weaken (relat_add_ctx P Γ)).
    apply incl_appl. apply incl_refl.
    apply adequacy_relat_tm. apply aP.
    autorewrite with relat_tm in IHproof.
    apply (pr_fora_e t) in IHproof.
    autorewrite with subst_tm get_subst_var in IHproof.
    rewrite adm_subst in IHproof.
    apply (pr_imp_e (P Γ s @ₛ t)).
    rewrite relat_subst. apply IHproof.
    apply H0. apply aP.
  - autorewrite with relat_tm. apply pr_fora_i. apply pr_imp_i.
    rewrite stand_relat.
    specialize
      (@pr_stand Γ s (relat_add_ctx P Γ ++ relat_ctx P Ξ)) as stand.
    apply (pr_up _ s) in stand.
    apply (fun x => pr_weaken_1 x (P (s :: Γ) s @ₛ ⟦ vz ⟧ₛ)).
    unfold "↑ₛ" in stand.
    autorewrite with lift_tm lift_var in stand.
    rewrite stand_lift in stand.
    apply (pr_fora_e ⟦ vz ⟧ₛ) in stand.
    autorewrite with subst_tm in stand.
    rewrite stand_subst in stand.
    autorewrite with get_subst_var in stand.
    apply stand.
Admitted.

Corollary indep_relat : forall (P : relat_pred) (φ ψ : [] ⊢ₛ ℙₛ),
    admissible_pred P ->
    ~ ([] ∣ [ relat_tm P φ ] ⊢ᴴᴼᴸ relat_tm P ψ) -> ~ ([] ∣ [ φ ] ⊢ᴴᴼᴸ ψ).
Proof. intros. intro H1. apply H0. apply (adequacy_relat P H H1). Qed.

Lemma stand_is_admissible : admissible_pred Standardity.
Proof.
  split; intros; autorewrite with Standardity.
  - apply pr_imp_i in H.
    apply (pr_red (∀ₛ s (Standardity (s :: Γ) s @ₛ ⟦ vz ⟧ₛ
                           ⇒ₛ Standardity (s :: Γ) s' @ₛ t))).
    admit.
    apply pr_fora_i. apply H.
  - eapply pr_red in H.
    apply (pr_imp_e (Standardity Γ s @ₛ u)).
    apply H. apply H0.
    apply rst_r. apply to_compat_incl.
    admit.
  - admit.
  - admit.
Admitted.
