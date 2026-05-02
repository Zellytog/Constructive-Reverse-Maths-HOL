From CRM Require Import Base Typing unscoped.

From Stdlib Require Import PeanoNat List.

Reserved Notation "Γ | Ξ ⊢ φ" (at level 85).

Definition eq_tm (t : tm) (u : tm) : tm :=
  ∀ₛ ((⟦ 0 ⟧ₛ @ₛ ren_tm shift t) ⇒ₛ (⟦ 0 ⟧ₛ @ₛ ren_tm shift t)).

Definition ex_tm (φ : tm) : tm :=
  ∀ₛ (∀ₛ (ren_tm shift φ ⇒ₛ ⟦ 1 ⟧ₛ) ⇒ₛ ⟦ 0 ⟧ₛ).

Lemma typ_eq_tm : forall (Γ : HOL_ctx) (s : st) (t : tm) (u : tm),
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s -> Γ ⊢ eq_tm t u ~: ℙₛ.
Proof.
  intros. apply (@HOL_typ_forall _ (s →ₛ ℙₛ)).
  constructor. apply (@HOL_typ_app _ _ s).
  constructor. constructor.
  admit.
  apply (@HOL_typ_app _ _ s). constructor. constructor.
  admit.
Admitted.

Lemma typ_ex_tm : forall (Γ : HOL_ctx) (s : st) (φ : tm),
    s :: Γ ⊢ φ ~: ℙₛ -> Γ ⊢ ex_tm φ ~: ℙₛ.
Proof.
  intros. apply (@HOL_typ_forall _ ℙₛ).
  constructor. apply (@HOL_typ_forall _ s). constructor.
  admit.
  constructor. constructor. constructor.
  constructor. constructor.
Admitted.
