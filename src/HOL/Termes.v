From CRM Require Import Base Typing Reduction Theorie Logical fintype.
Import CombineNotations SubstNotations.

Require Import PeanoNat List.

Fixpoint nat_to_tm {n : nat} (m : nat) : tm n :=
  match m with
  | 0 => Zₛ
  | S p => Sₛ (nat_to_tm p)
  end.

Lemma typ_nat_to_tm :
  forall {n : nat} (Γ : HOL_ctx n) (m : nat),
    Γ ⊢⟨ n ⟩ nat_to_tm m ~: ℕₛ.
Proof.
  intros. induction m. constructor.
  simpl. constructor. apply IHm.
Qed.

Definition restr_tm {n : nat} : tm n :=
  ƛ (ƛ
  (recℕₛ []ₛ
    (ƛ (ƛ
       ((⟦ (shift >> shift >> shift) var_zero ⟧ₛ @ₛ ⟦ shift var_zero ⟧ₛ)
       ::ₛ ⟦ var_zero ⟧ₛ))) ⟦ var_zero ⟧ₛ)).

Lemma typ_restr :
  forall {n : nat} {Γ : HOL_ctx n} {s : st},
    Γ ⊢⟨ n ⟩ restr_tm ~: (ℕₛ →ₛ s) →ₛ ℕₛ →ₛ 𝕃ₛ s.
Proof.
  intros. repeat constructor.
  apply (typ_app ℕₛ).
  repeat constructor. constructor.
Qed.

Definition length_tm {n : nat} : tm n :=
  ƛ (rec𝕃ₛ Zₛ (ƛ (ƛ (ƛ (Sₛ ⟦ var_zero ⟧ₛ)))) ⟦ var_zero ⟧ₛ).

Lemma typ_length :
  forall {n : nat} {Γ : HOL_ctx n} (s : st),
    Γ ⊢⟨ n ⟩ length_tm ~: (𝕃ₛ s) →ₛ ℕₛ.
Proof.
  intros. repeat constructor.
  apply (typ_recL s); repeat constructor.
Qed.

Definition concat_tm {n : nat} : tm n :=
  ƛ (rec𝕃ₛ (ƛ ⟦ var_zero ⟧ₛ)
       (ƛ (ƛ (ƛ (ƛ (⟦ shift_p 3 var_zero ⟧ₛ ::ₛ (⟦ shift var_zero ⟧ₛ @ₛ ⟦ var_zero ⟧ₛ))))))
       ⟦ var_zero ⟧ₛ).

Lemma typ_concat :
  forall {n : nat} {Γ : HOL_ctx n} {s : st},
    Γ ⊢⟨ n ⟩ concat_tm ~: 𝕃ₛ s →ₛ 𝕃ₛ s →ₛ 𝕃ₛ s.
Proof.
  intros. repeat constructor.
  apply (typ_recL s).
  repeat constructor.
  repeat constructor.
  apply (typ_app (𝕃ₛ s)); repeat constructor.
  constructor.
Qed.

Notation "t ++ₛ u" := (concat_tm @ₛ t @ₛ u) (at level 87).

Definition pref_tm {n : nat} (s : st) : tm n :=
  ƛ (ƛ (∃{𝕃ₛ s}
         (⟦ shift var_zero ⟧ₛ =⟨ 𝕃ₛ s ⟩
                                 (⟦ var_zero ⟧ₛ ++ₛ ⟦ shift_p 2 var_zero ⟧ₛ)))).

Lemma typ_pref :
  forall {n : nat} {Γ : HOL_ctx n} (s : st),
    Γ ⊢⟨ n ⟩ pref_tm s ~: 𝕃ₛ s →ₛ 𝕃ₛ s →ₛ ℙₛ.
Proof.
  intros. constructor. constructor.
  apply typ_relat_ex. apply typ_eq; repeat constructor.
  apply (typ_app (𝕃ₛ s)). apply (typ_app (𝕃ₛ s)).
  apply typ_concat.
  constructor. constructor.
Qed.

Definition is_Tree_tm {n : nat} (s : st) : tm n :=
  ƛ
   (∀ₛ (𝕃ₛ s)
     (∀ₛ (𝕃ₛ s)
       ((pref_tm s @ₛ ⟦ shift var_zero ⟧ₛ @ₛ ⟦ var_zero ⟧ₛ) ⇒ₛ
          ⟦ shift_p 2 var_zero ⟧ₛ @ₛ ⟦ var_zero ⟧ₛ ⇒ₛ
          ⟦ shift_p 2 var_zero ⟧ₛ @ₛ ⟦ shift var_zero ⟧ₛ))).

Lemma typ_is_Tree :
  forall {n : nat} {Γ : HOL_ctx n} (s : st),
    Γ ⊢⟨ n ⟩ is_Tree_tm s ~: ((𝕃ₛ s) →ₛ ℙₛ) →ₛ ℙₛ.
Proof.
  intros. repeat constructor.
  apply (typ_app (𝕃ₛ s)).
  apply (typ_app (𝕃ₛ s)).
  apply typ_pref. constructor. constructor.
  apply (typ_app (𝕃ₛ s)). constructor.
  constructor.
  apply (typ_app (𝕃ₛ s)). constructor.
  constructor.
Qed.

Definition WKL_tm {n : nat} : tm n :=
  ∀ₛ ((𝕃ₛ 𝔹ₛ) →ₛ ℙₛ)
   (is_Tree_tm 𝔹ₛ @ₛ ⟦ var_zero ⟧ₛ ⇒ₛ
      (∀{ ℕₛ }
        (∃{ 𝕃ₛ 𝔹ₛ }
          (((length_tm @ₛ ⟦ var_zero ⟧ₛ) =⟨ ℕₛ ⟩ ⟦ shift var_zero ⟧ₛ) ∧ₛ
             (⟦ shift_p 2 var_zero ⟧ₛ @ₛ ⟦ var_zero⟧ₛ)))) ⇒ₛ
      (∃{ ℕₛ →ₛ 𝔹ₛ }
        (∀{ ℕₛ }
          ((⟦ shift_p 2 var_zero ⟧ₛ @ₛ
             (restr_tm @ₛ ⟦ shift var_zero ⟧ₛ @ₛ
                ⟦ var_zero ⟧ₛ)))))).

Lemma typ_WKL :
  forall {n : nat} {Γ : HOL_ctx n},
    Γ ⊢⟨ n ⟩ WKL_tm ~: ℙₛ.
Proof.
  intros. constructor. constructor.
  apply (typ_app (𝕃ₛ 𝔹ₛ →ₛ ℙₛ)).
  apply typ_is_Tree. constructor.
  constructor.
  apply typ_relat_forall. apply typ_relat_ex.
  apply typ_and. apply (typ_eq ℕₛ).
  apply (typ_app (𝕃ₛ 𝔹ₛ)). apply typ_length.
  constructor. constructor.
  apply (typ_app (𝕃ₛ 𝔹ₛ)); constructor.
  apply typ_relat_ex. apply typ_relat_forall.
  apply (typ_app (𝕃ₛ 𝔹ₛ)).
  constructor.
  apply (typ_app ℕₛ).
  apply (typ_app (ℕₛ →ₛ 𝔹ₛ)).
  apply typ_restr. constructor. constructor.
Qed.

Definition is_Mono_tm {n : nat} (s : st) : tm n :=
  ƛ
   (∀ₛ (𝕃ₛ s)
     (∀ₛ (𝕃ₛ s)
       ((pref_tm s @ₛ ⟦ shift var_zero ⟧ₛ @ₛ ⟦ var_zero ⟧ₛ) ⇒ₛ
          ⟦ shift_p 2 var_zero ⟧ₛ @ₛ ⟦ shift var_zero ⟧ₛ ⇒ₛ
          ⟦ shift_p 2 var_zero ⟧ₛ @ₛ ⟦ var_zero ⟧ₛ))).

Lemma typ_is_Mono :
  forall {n : nat} {Γ : HOL_ctx n} (s : st),
    Γ ⊢⟨ n ⟩ is_Mono_tm s ~: ((𝕃ₛ s) →ₛ ℙₛ) →ₛ ℙₛ.
Proof.
  intros. repeat constructor.
  apply (typ_app (𝕃ₛ s)).
  apply (typ_app (𝕃ₛ s)).
  apply typ_pref. constructor. constructor.
  apply (typ_app (𝕃ₛ s)). constructor.
  constructor.
  apply (typ_app (𝕃ₛ s)). constructor.
  constructor.
Qed.

Definition FT_tm {n : nat} : tm n :=
  ∀ₛ ((𝕃ₛ 𝔹ₛ) →ₛ ℙₛ)
   (is_Mono_tm 𝔹ₛ @ₛ ⟦ var_zero ⟧ₛ ⇒ₛ
      (∀{ ℕₛ →ₛ 𝔹ₛ }
        (∃{ ℕₛ }
          (⟦ shift_p 2 var_zero ⟧ₛ @ₛ (restr_tm @ₛ ⟦ shift var_zero ⟧ₛ
                                         @ₛ ⟦ var_zero ⟧ₛ)))) ⇒ₛ
      (∃{ ℕₛ }
        (∀{ ℕₛ →ₛ 𝔹ₛ }
          (⟦ shift_p 2 var_zero ⟧ₛ @ₛ (restr_tm @ₛ ⟦ var_zero ⟧ₛ @ₛ
                                         ⟦ shift var_zero ⟧ₛ))))).

Lemma typ_FT :
  forall {n : nat} {Γ : HOL_ctx n},
    Γ ⊢⟨ n ⟩ FT_tm ~: ℙₛ.
Proof.
  intros. constructor. constructor.
  apply (typ_app ((𝕃ₛ 𝔹ₛ) →ₛ ℙₛ)).
  apply typ_is_Mono. constructor.
  constructor.
  apply typ_relat_forall. apply typ_relat_ex.
  apply (typ_app (𝕃ₛ 𝔹ₛ)).
  constructor.
  apply (typ_app ℕₛ). apply (typ_app (ℕₛ →ₛ 𝔹ₛ)). apply typ_restr.
  constructor. constructor.
  apply typ_relat_ex. apply typ_relat_forall.
  apply (typ_app (𝕃ₛ 𝔹ₛ)).
  constructor.
  apply (typ_app ℕₛ). apply (typ_app (ℕₛ →ₛ 𝔹ₛ)). apply typ_restr.
  constructor. constructor.
Qed.



(* Theorem FT_nprove_WKL :
  ~ (proving 0 (@False_rect st) (FT_tm :: nil) WKL_tm).*)
