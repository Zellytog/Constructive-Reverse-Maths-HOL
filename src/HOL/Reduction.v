From CRM Require Import Base Relations.
From Stdlib Require Import List Program.Equality.
Import ListNotations.

Inductive b_red_immed : Rel_tm :=
| beta_lam : forall {Γ : HOL_ctx} {s s' : st} (t : s' :: Γ ⊢ₛ s) (u : Γ ⊢ₛ s'),
    b_red_immed _ _ ((ƛₛ s' t) @ₛ u) (t ⟨[ u ::ᵥ id_subst Γ ]⟩)
| beta_p1 : forall {Γ : HOL_ctx} {s s' : st} (t : Γ ⊢ₛ s) (u : Γ ⊢ₛ s'),
    b_red_immed _ _ (π¹ₛ ⟨ t , u ⟩ₛ) t
| beta_p2 : forall {Γ : HOL_ctx} {s s' : st} (t : Γ ⊢ₛ s) (u : Γ ⊢ₛ s'),
    b_red_immed _ _ (π²ₛ ⟨ t , u ⟩ₛ) u
| beta_c1 : forall {Γ : HOL_ctx} {s s' s'' : st} (t : Γ ⊢ₛ s)
                   (u : Γ ⊢ₛ s →ₛ s'') (v : Γ ⊢ₛ s' →ₛ s''),
    b_red_immed _ _ (δₛ (κ¹ₛ s' t) u v) (u @ₛ t)
| beta_c2 : forall {Γ : HOL_ctx} {s s' s'' : st} (t : Γ ⊢ₛ s')
                   (u : Γ ⊢ₛ s →ₛ s'') (v : Γ ⊢ₛ s' →ₛ s''),
    b_red_immed _ _ (δₛ (κ²ₛ s t) u v) (v @ₛ t)
| beta_recN_Z : forall {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s)
                       (u : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s),
    b_red_immed _ _ (recℕₛ t u 0ₛ) t
| beta_recN_S : forall {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s)
                       (u : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s) (v : Γ ⊢ₛ ℕₛ),
    b_red_immed _ _ (recℕₛ t u (Sₛ v)) (u @ₛ v @ₛ (recℕₛ t u v))
| beta_recB_T : forall {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s) (u : Γ ⊢ₛ s),
    b_red_immed _ _ (rec𝔹ₛ t u ⊤ₛ) t
| beta_recB_F : forall {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s) (u : Γ ⊢ₛ s),
    b_red_immed _ _ (rec𝔹ₛ t u ⊥ₛ) u
| beta_recL_N : forall {Γ : HOL_ctx} {s s' : st} (t : Γ ⊢ₛ s)
                       (u : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s)
                       (v : Γ ⊢ₛ s') (w : Γ ⊢ₛ 𝕃ₛ s'),
    b_red_immed _ _ (rec𝕃ₛ t u (v ::ₛ w)) (u @ₛ v @ₛ w @ₛ (rec𝕃ₛ t u w)).

Record compat_rel (R : Rel_tm) : Prop :=
  { compat_lam : forall {Γ : HOL_ctx} {s s' : st} {t u : s' :: Γ ⊢ₛ s},
      R _ _ t u -> R _ _ (ƛₛ s' t) (ƛₛ s' u)
  ; compat_app_1 : forall {Γ : HOL_ctx} {s s' : st} {t u : Γ ⊢ₛ s →ₛ s'}
                          (v : Γ ⊢ₛ s),
      R _ _ t u -> R _ _ (t @ₛ v) (u @ₛ v)
  ; compat_app_2 : forall {Γ : HOL_ctx} {s s' : st} (t : Γ ⊢ₛ s →ₛ s')
                          {u v : Γ ⊢ₛ s},
      R _ _ u v -> R _ _ (t @ₛ u) (t @ₛ v)
  ; compat_pair_1 : forall {Γ : HOL_ctx} {s s' : st} {t u : Γ ⊢ₛ s}
                           (v : Γ ⊢ₛ s'),
      R _ _ t u -> R _ _ ⟨ t, v ⟩ₛ ⟨ u, v ⟩ₛ
  ; compat_pair_2 : forall {Γ : HOL_ctx} {s s' : st} (t : Γ ⊢ₛ s)
                           (u v : Γ ⊢ₛ s'),
      R _ _ u v -> R _ _ ⟨ t, u ⟩ₛ ⟨ t, v ⟩ₛ
  ; compat_proj1 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s ×ₛ s'),
      R _ _ t u -> R _ _ (π¹ₛ t) (π¹ₛ u)
  ; compat_proj2 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s ×ₛ s'),
      R _ _ t u -> R _ _ (π²ₛ t) (π²ₛ u)
  ; compat_coproj1 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s),
      R _ _ t u -> R _ _ (κ¹ₛ s' t) (κ¹ₛ s' u)
  ; compat_coproj2 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s'),
      R _ _ t u -> R _ _ (κ²ₛ s t) (κ²ₛ s u)
  ; compat_delta_1 : forall {Γ : HOL_ctx} {s s' s'' : st}
                            {t u : Γ ⊢ₛ s +ₛ s'}
                            {v : Γ ⊢ₛ s →ₛ s''} {w : Γ ⊢ₛ s' →ₛ s''},
      R _ _ t u -> R _ _ (δₛ t v w) (δₛ u v w)
  ; compat_delta_2 : forall {Γ : HOL_ctx} {s s' s'' : st}
                            {t : Γ ⊢ₛ s +ₛ s'}
                            {u v : Γ ⊢ₛ s →ₛ s''} {w : Γ ⊢ₛ s' →ₛ s''},
      R _ _ u v -> R _ _ (δₛ t u w) (δₛ t v w)
  ; compat_delta_3 : forall {Γ : HOL_ctx} {s s' s'' : st}
                            {t : Γ ⊢ₛ s +ₛ s'}
                            {u : Γ ⊢ₛ s →ₛ s''} {v w : Γ ⊢ₛ s' →ₛ s''},
      R _ _ v w -> R _ _ (δₛ t u v) (δₛ t u w)
  ; compat_succ : forall {Γ : HOL_ctx} (t u : Γ ⊢ₛ ℕₛ),
      R _ _ t u -> R _ _ (Sₛ t) (Sₛ u)
  ; compat_recN_1 : forall {Γ : HOL_ctx} {s : st}
                           {t u : Γ ⊢ₛ s} {v : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s}
                           {w : Γ ⊢ₛ ℕₛ},
      R _ _ t u -> R _ _ (recℕₛ t v w) (recℕₛ u v w)
  ; compat_recN_2 : forall {Γ : HOL_ctx} {s : st}
                           {t : Γ ⊢ₛ s} {u v : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s}
                           {w : Γ ⊢ₛ ℕₛ},
      R _ _ u v -> R _ _ (recℕₛ t u w) (recℕₛ t v w)
  ; compat_recN_3 : forall {Γ : HOL_ctx} {s : st}
                           {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s}
                           {v w : Γ ⊢ₛ ℕₛ},
      R _ _ v w -> R _ _ (recℕₛ t u v) (recℕₛ t u w)
  ; compat_recB_1 : forall {Γ : HOL_ctx} {s : st}
                           {t u : Γ ⊢ₛ s} {v : Γ ⊢ₛ s} {w : Γ ⊢ₛ 𝔹ₛ},
      R _ _ t u -> R _ _ (rec𝔹ₛ t v w) (rec𝔹ₛ u v w)
  ; compat_recB_2 : forall {Γ : HOL_ctx} {s : st}
                           {t : Γ ⊢ₛ s} {u v : Γ ⊢ₛ s} {w : Γ ⊢ₛ 𝔹ₛ},
      R _ _ u v -> R _ _ (rec𝔹ₛ t u w) (rec𝔹ₛ t v w)
  ; compat_recB_3 : forall {Γ : HOL_ctx} {s : st}
                           {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ s} {v w : Γ ⊢ₛ 𝔹ₛ},
      R _ _ v w -> R _ _ (rec𝔹ₛ t u v) (rec𝔹ₛ t u w)
  ; compat_cons_1 : forall {Γ : HOL_ctx} {s : st}
                           {t u : Γ ⊢ₛ s} (v : Γ ⊢ₛ 𝕃ₛ s),
      R _ _ t u -> R _ _ (t ::ₛ v) (u ::ₛ v)
  ; compat_cons_2 : forall {Γ : HOL_ctx} {s : st}
                           (t : Γ ⊢ₛ s) {u v : Γ ⊢ₛ 𝕃ₛ s},
      R _ _ u v -> R _ _ (t ::ₛ u) (t ::ₛ v)
  ; compat_recL_1 : forall {Γ : HOL_ctx} {s s' : st}
                           {t u : Γ ⊢ₛ s}
                           {v : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s} {w : Γ ⊢ₛ 𝕃ₛ s'},
      R _ _ t u -> R _ _ (rec𝕃ₛ t v w) (rec𝕃ₛ u v w)
  ; compat_recL_2 : forall {Γ : HOL_ctx} {s s' : st}
                           {t : Γ ⊢ₛ s}
                           {u v : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s} {w : Γ ⊢ₛ 𝕃ₛ s'},
      R _ _ u v -> R _ _ (rec𝕃ₛ t u w) (rec𝕃ₛ t v w)
  ; compat_recL_3 : forall {Γ : HOL_ctx} {s s' : st}
                           {t : Γ ⊢ₛ s}
                           {u : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s} {v w : Γ ⊢ₛ 𝕃ₛ s'},
      R _ _ v w -> R _ _ (rec𝕃ₛ t u v) (rec𝕃ₛ t u w)
  ; compat_imp_1 : forall {Γ : HOL_ctx} {φ ψ : Γ ⊢ₛ ℙₛ} (χ : Γ ⊢ₛ ℙₛ),
      R _ _ φ ψ -> R _ _ (φ ⇒ₛ χ) (ψ ⇒ₛ χ)
  ; compat_imp_2 : forall {Γ : HOL_ctx} (φ : Γ ⊢ₛ ℙₛ) {ψ χ : Γ ⊢ₛ ℙₛ},
      R _ _ ψ χ -> R _ _ (φ ⇒ₛ ψ) (φ ⇒ₛ χ)
  ; compat_fora : forall {Γ : HOL_ctx} {s : st} {φ ψ : s :: Γ ⊢ₛ ℙₛ},
      R _ _ φ ψ -> R _ _ (∀ₛ s φ) (∀ₛ s ψ)
  }.

Inductive to_compat (R : Rel_tm) : Rel_tm :=
| to_compat_incl : forall {Γ : HOL_ctx} {s : st} (t u : Γ ⊢ₛ s),
    R _ _ t u -> to_compat R _ _ t u
| to_compat_lam : forall {Γ : HOL_ctx} {s s' : st} {t u : s' :: Γ ⊢ₛ s},
    to_compat R _ _ t u -> to_compat R _ _ (ƛₛ s' t) (ƛₛ s' u)
| to_compat_app_1 : forall {Γ : HOL_ctx} {s s' : st} {t u : Γ ⊢ₛ s →ₛ s'}
                           (v : Γ ⊢ₛ s),
    to_compat R _ _ t u -> to_compat R _ _ (t @ₛ v) (u @ₛ v)
| to_compat_app_2 : forall {Γ : HOL_ctx} {s s' : st} (t : Γ ⊢ₛ s →ₛ s')
                           {u v : Γ ⊢ₛ s},
    to_compat R _ _ u v -> to_compat R _ _ (t @ₛ u) (t @ₛ v)
| to_compat_pair_1 : forall {Γ : HOL_ctx} {s s' : st} {t u : Γ ⊢ₛ s}
                            (v : Γ ⊢ₛ s'),
    to_compat R _ _ t u -> to_compat R _ _ ⟨ t, v ⟩ₛ ⟨ u, v ⟩ₛ
| to_compat_pair_2 : forall {Γ : HOL_ctx} {s s' : st} (t : Γ ⊢ₛ s)
                            (u v : Γ ⊢ₛ s'),
    to_compat R _ _ u v -> to_compat R _ _ ⟨ t, u ⟩ₛ ⟨ t, v ⟩ₛ
| to_compat_proj1 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s ×ₛ s'),
    to_compat R _ _ t u -> to_compat R _ _ (π¹ₛ t) (π¹ₛ u)
| to_compat_proj2 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s ×ₛ s'),
    to_compat R _ _ t u -> to_compat R _ _ (π²ₛ t) (π²ₛ u)
| to_compat_coproj1 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s),
    to_compat R _ _ t u -> to_compat R _ _ (κ¹ₛ s' t) (κ¹ₛ s' u)
| to_compat_coproj2 : forall {Γ : HOL_ctx} {s s' : st} (t u : Γ ⊢ₛ s'),
    to_compat R _ _ t u -> to_compat R _ _ (κ²ₛ s t) (κ²ₛ s u)
| to_compat_delta_1 : forall {Γ : HOL_ctx} {s s' s'' : st}
                             {t u : Γ ⊢ₛ s +ₛ s'}
                             {v : Γ ⊢ₛ s →ₛ s''} {w : Γ ⊢ₛ s' →ₛ s''},
    to_compat R _ _ t u -> to_compat R _ _ (δₛ t v w) (δₛ u v w)
| to_compat_delta_2 : forall {Γ : HOL_ctx} {s s' s'' : st}
                             {t : Γ ⊢ₛ s +ₛ s'}
                             {u v : Γ ⊢ₛ s →ₛ s''} {w : Γ ⊢ₛ s' →ₛ s''},
    to_compat R _ _ u v -> to_compat R _ _ (δₛ t u w) (δₛ t v w)
| to_compat_delta_3 : forall {Γ : HOL_ctx} {s s' s'' : st}
                             {t : Γ ⊢ₛ s +ₛ s'}
                             {u : Γ ⊢ₛ s →ₛ s''} {v w : Γ ⊢ₛ s' →ₛ s''},
    to_compat R _ _ v w -> to_compat R _ _ (δₛ t u v) (δₛ t u w)
| to_compat_succ : forall {Γ : HOL_ctx} (t u : Γ ⊢ₛ ℕₛ),
    to_compat R _ _ t u -> to_compat R _ _ (Sₛ t) (Sₛ u)
| to_compat_recN_1 : forall {Γ : HOL_ctx} {s : st}
                            {t u : Γ ⊢ₛ s} {v : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s}
                            {w : Γ ⊢ₛ ℕₛ},
    to_compat R _ _ t u -> to_compat R _ _ (recℕₛ t v w) (recℕₛ u v w)
| to_compat_recN_2 : forall {Γ : HOL_ctx} {s : st}
                            {t : Γ ⊢ₛ s} {u v : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s}
                            {w : Γ ⊢ₛ ℕₛ},
    to_compat R _ _ u v -> to_compat R _ _ (recℕₛ t u w) (recℕₛ t v w)
| to_compat_recN_3 : forall {Γ : HOL_ctx} {s : st}
                            {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ ℕₛ →ₛ s →ₛ s}
                            {v w : Γ ⊢ₛ ℕₛ},
    to_compat R _ _ v w -> to_compat R _ _ (recℕₛ t u v) (recℕₛ t u w)
| to_compat_recB_1 : forall {Γ : HOL_ctx} {s : st}
                            {t u : Γ ⊢ₛ s} {v : Γ ⊢ₛ s} {w : Γ ⊢ₛ 𝔹ₛ},
    to_compat R _ _ t u -> to_compat R _ _ (rec𝔹ₛ t v w) (rec𝔹ₛ u v w)
| to_compat_recB_2 : forall {Γ : HOL_ctx} {s : st}
                            {t : Γ ⊢ₛ s} {u v : Γ ⊢ₛ s} {w : Γ ⊢ₛ 𝔹ₛ},
    to_compat R _ _ u v -> to_compat R _ _ (rec𝔹ₛ t u w) (rec𝔹ₛ t v w)
| to_compat_recB_3 : forall {Γ : HOL_ctx} {s : st}
                            {t : Γ ⊢ₛ s} {u : Γ ⊢ₛ s} {v w : Γ ⊢ₛ 𝔹ₛ},
    to_compat R _ _ v w -> to_compat R _ _ (rec𝔹ₛ t u v) (rec𝔹ₛ t u w)
| to_compat_cons_1 : forall {Γ : HOL_ctx} {s : st}
                            {t u : Γ ⊢ₛ s} (v : Γ ⊢ₛ 𝕃ₛ s),
    to_compat R _ _ t u -> to_compat R _ _ (t ::ₛ v) (u ::ₛ v)
| to_compat_cons_2 : forall {Γ : HOL_ctx} {s : st}
                            (t : Γ ⊢ₛ s) {u v : Γ ⊢ₛ 𝕃ₛ s},
    to_compat R _ _ u v -> to_compat R _ _ (t ::ₛ u) (t ::ₛ v)
| to_compat_recL_1 : forall {Γ : HOL_ctx} {s s' : st}
                            {t u : Γ ⊢ₛ s}
                            {v : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s} {w : Γ ⊢ₛ 𝕃ₛ s'},
    to_compat R _ _ t u -> to_compat R _ _ (rec𝕃ₛ t v w) (rec𝕃ₛ u v w)
| to_compat_recL_2 : forall {Γ : HOL_ctx} {s s' : st}
                            {t : Γ ⊢ₛ s}
                            {u v : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s} {w : Γ ⊢ₛ 𝕃ₛ s'},
    to_compat R _ _ u v -> to_compat R _ _ (rec𝕃ₛ t u w) (rec𝕃ₛ t v w)
| to_compat_recL_3 : forall {Γ : HOL_ctx} {s s' : st}
                            {t : Γ ⊢ₛ s}
                            {u : Γ ⊢ₛ s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s} {v w : Γ ⊢ₛ 𝕃ₛ s'},
    to_compat R _ _ v w -> to_compat R _ _ (rec𝕃ₛ t u v) (rec𝕃ₛ t u w)
| to_compat_imp_1 : forall {Γ : HOL_ctx} {φ ψ : Γ ⊢ₛ ℙₛ} (χ : Γ ⊢ₛ ℙₛ),
    to_compat R _ _ φ ψ -> to_compat R _ _ (φ ⇒ₛ χ) (ψ ⇒ₛ χ)
| to_compat_imp_2 : forall {Γ : HOL_ctx} (φ : Γ ⊢ₛ ℙₛ) {ψ χ : Γ ⊢ₛ ℙₛ},
    to_compat R _ _ ψ χ -> to_compat R _ _ (φ ⇒ₛ ψ) (φ ⇒ₛ χ)
| to_compat_fora : forall {Γ : HOL_ctx} {s : st} {φ ψ : s :: Γ ⊢ₛ ℙₛ},
    to_compat R _ _ φ ψ -> to_compat R _ _ (∀ₛ s φ) (∀ₛ s ψ).

Proposition to_compat_compat :
  forall R : Rel_tm, compat_rel (to_compat R).
Proof.
  intro R.
  split; intros;
    [apply to_compat_lam | apply to_compat_app_1 | apply to_compat_app_2 |
      apply to_compat_pair_1 | apply to_compat_pair_2 | apply to_compat_proj1 |
      apply to_compat_proj2 | apply to_compat_coproj1 | apply to_compat_coproj2 |
      apply to_compat_delta_1 | apply to_compat_delta_2 |
      apply to_compat_delta_3 | apply to_compat_succ |
      apply to_compat_recN_1 | apply to_compat_recN_2 | apply to_compat_recN_3 |
      apply to_compat_recB_1 | apply to_compat_recB_2 | apply to_compat_recB_3 |
      apply to_compat_cons_1 | apply to_compat_cons_2 |
      apply to_compat_recL_1 | apply to_compat_recL_2 | apply to_compat_recL_3 |
      apply to_compat_imp_1 | apply to_compat_imp_2 | apply to_compat_fora];
    assumption.
Qed.

Proposition rt_clot_compat :
  forall R : Rel_tm, compat_rel R -> compat_rel (rt_clot R).
Proof.
  intros R H. split; intros.
  - dependent induction H0; [constructor |].
    apply (rt_step R (ƛₛ s' u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_lam R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (u0 @ₛ v)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_app_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (t @ₛ u)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_app_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R ⟨ u, v ⟩ₛ).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_pair_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R ⟨ t, u ⟩ₛ).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_pair_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (π¹ₛ u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_proj1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (π²ₛ u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_proj2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (κ¹ₛ _ u)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_coproj1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (κ²ₛ _ u)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_coproj2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (δₛ u0 v w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_delta_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (δₛ t u0 w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_delta_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (δₛ t u u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_delta_3 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (Sₛ u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_succ R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (recℕₛ u v w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recN_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (recℕₛ t u0 w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recN_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (recℕₛ t u u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recN_3 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (rec𝔹ₛ u v w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recB_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (rec𝔹ₛ t u w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recB_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (rec𝔹ₛ t u u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recB_3 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (u ::ₛ v)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_cons_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (t ::ₛ u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_cons_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (rec𝕃ₛ u v w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recL_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (rec𝕃ₛ t u0 w)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recL_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (rec𝕃ₛ t u u0)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_recL_3 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (u ⇒ₛ χ)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_imp_1 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (φ ⇒ₛ u)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_imp_2 R H). assumption.
  - dependent induction H0; [constructor |].
    apply (rt_step R (∀ₛ _ u)).
    apply IHrt_clot; try assumption; try reflexivity.
    apply (compat_fora R H). assumption.
Qed.

Proposition s_clot_compat :
  forall R : Rel_tm, compat_rel R -> compat_rel (s_clot R).
Proof.
  intros R H. split; intros; dependent induction H0 ;
    [ apply s_step; apply compat_lam |
      apply s_unstep; apply compat_lam |
      apply s_step; apply compat_app_1 |
      apply s_unstep; apply compat_app_1 |
      apply s_step; apply compat_app_2 |
      apply s_unstep; apply compat_app_2 |
      apply s_step; apply compat_pair_1 |
      apply s_unstep; apply compat_pair_1 |
      apply s_step; apply compat_pair_2 |
      apply s_unstep; apply compat_pair_2 |
      apply s_step; apply compat_proj1 |
      apply s_unstep; apply compat_proj1 |
      apply s_step; apply compat_proj2 |
      apply s_unstep; apply compat_proj2 |
      apply s_step; apply compat_coproj1 |
      apply s_unstep; apply compat_coproj1 |
      apply s_step; apply compat_coproj2 |
      apply s_unstep; apply compat_coproj2 |
      apply s_step; apply compat_delta_1 |
      apply s_unstep; apply compat_delta_1 |
      apply s_step; apply compat_delta_2 |
      apply s_unstep; apply compat_delta_2 |
      apply s_step; apply compat_delta_3 |
      apply s_unstep; apply compat_delta_3 |
      apply s_step; apply compat_succ |
      apply s_unstep; apply compat_succ |
      apply s_step; apply compat_recN_1 |
      apply s_unstep; apply compat_recN_1 |
      apply s_step; apply compat_recN_2 |
      apply s_unstep; apply compat_recN_2 |
      apply s_step; apply compat_recN_3 |
      apply s_unstep; apply compat_recN_3 |
      apply s_step; apply compat_recB_1 |
      apply s_unstep; apply compat_recB_1 |
      apply s_step; apply compat_recB_2 |
      apply s_unstep; apply compat_recB_2 |
      apply s_step; apply compat_recB_3 |
      apply s_unstep; apply compat_recB_3 |
      apply s_step; apply compat_cons_1 |
      apply s_unstep; apply compat_cons_1 |
      apply s_step; apply compat_cons_2 |
      apply s_unstep; apply compat_cons_2 |
      apply s_step; apply compat_recL_1 |
      apply s_unstep; apply compat_recL_1 |
      apply s_step; apply compat_recL_2 |
      apply s_unstep; apply compat_recL_2 |
      apply s_step; apply compat_recL_3 |
      apply s_unstep; apply compat_recL_3 |
      apply s_step; apply compat_imp_1 |
      apply s_unstep; apply compat_imp_1 |
      apply s_step; apply compat_imp_2 |
      apply s_unstep; apply compat_imp_2 |
      apply s_step; apply compat_fora |
      apply s_unstep; apply compat_fora ]; try assumption.
Qed.

Proposition ext_compat : ext_prop_rel (compat_rel).
Proof.
  intros R R' [RR' R'R] cR.
  split; intros; apply RR'; apply cR; apply R'R; apply H.
Qed.

Definition b_red := to_compat b_red_immed.
Definition b_red_rt := rt_clot b_red.
Definition b_eq := rst_clot b_red.

Notation "t ▷ₛ u" := (b_red _ _ t u) (at level 60).
Notation "t ▷*ₛ u" := (b_red_rt _ _ t u) (at level 60).
Notation "t =ₛ u" := (b_eq _ _ t u) (at level 60).

Proposition compat_red : compat_rel b_red_rt.
Proof. apply rt_clot_compat. apply to_compat_compat. Qed.

Proposition compat_beq : compat_rel b_eq.
Proof.
  apply (prop_to_rst compat_rel ext_compat s_clot_compat rt_clot_compat).
  apply to_compat_compat.
Qed.
