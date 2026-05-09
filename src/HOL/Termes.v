From CRM Require Import Base Typing Reduction Theorie Logical fintype.
Import CombineNotations SubstNotations.
From CRM Require Import Prelude.ListCRM.

Require Import PeanoNat List Program.Equality.

Section Standardization.

  Fixpoint HOL_ctx_stand (n : nat) : HOL_ctx n -> proof_ctx n.
  Proof.
    intro Γ. induction n.
    - exact nil.
    - exact (𝕊 (Γ var_zero) ⟦ var_zero ⟧ₛ ::
               map (ren_tm shift) (HOL_ctx_stand n (shift >> Γ))).
  Defined.

  Lemma typ_stand :
    forall (n : nat) (Γ : HOL_ctx n), wt_ctx Γ (HOL_ctx_stand n Γ).
  Proof.
    intro n; induction n; intro Γ.
    - constructor.
    - simpl. constructor.
      constructor. constructor.
      specialize (IHn (shift >> Γ)).
      eapply map_forall.
      intros a Ha.
      apply (typ_ren _ _ shift Γ (shift >> Γ)).
      reflexivity.
      apply Ha.
      apply IHn.
  Qed.

  Inductive stand_tm : forall (n : nat), tm n -> Prop :=
  | st_var : forall (n : nat) (v : fin n),
      stand_tm n ⟦ v ⟧ₛ
  | st_lam : forall (n : nat) (t : tm (S n)),
      stand_tm (S n) t -> stand_tm n (ƛ t)
  | st_app : forall (n : nat) (t u : tm n),
      stand_tm n t -> stand_tm n u ->
      stand_tm n (t @ₛ u)
  | st_pair : forall (n : nat) (t u : tm n),
      stand_tm n t -> stand_tm n u ->
      stand_tm n ⟨ t, u ⟩ₛ
  | st_proj1 : forall (n : nat) (t : tm n),
      stand_tm n t -> stand_tm n (π¹ₛ t)
  | st_proj2 : forall (n : nat) (t u : tm n),
      stand_tm n t -> stand_tm n (π²ₛ t)
  | st_Z : forall (n : nat), stand_tm n Zₛ
  | st_S : forall (n : nat) (t : tm n),
      stand_tm n t -> stand_tm n (Sₛ t)
  | st_recN : forall (n : nat) (t u v : tm n),
      stand_tm n t -> stand_tm n u -> stand_tm n v ->
      stand_tm n (recℕₛ t u v)
  | st_T : forall (n : nat), stand_tm n ttₛ
  | st_F : forall (n : nat), stand_tm n ffₛ
  | st_recB : forall (n : nat) (t u v : tm n),
      stand_tm n t -> stand_tm n u -> stand_tm n v ->
      stand_tm n (rec𝔹ₛ t u v)
  | st_nil : forall (n : nat), stand_tm n []ₛ
  | st_cons : forall (n : nat) (t u : tm n),
      stand_tm n t -> stand_tm n u ->
      stand_tm n (t ::ₛ u)
  | st_recL : forall (n : nat) (t u v : tm n),
      stand_tm n t -> stand_tm n u -> stand_tm n v ->
      stand_tm n (rec𝕃ₛ t u v).

  Lemma stand_in_stand_ctx :
    forall {n : nat} {Γ : HOL_ctx n} (v : fin n),
      In (𝕊 (Γ v) ⟦ v ⟧ₛ) (HOL_ctx_stand n Γ).
  Proof.
    intros. induction n.
    + inversion v.
    + simpl. destruct v.
      ++ right. specialize (IHn (shift >> Γ) f).
         specialize (in_map (ren_tm shift)
                       (HOL_ctx_stand n (shift >> Γ))
                       (𝕊 ((shift >> Γ) f) ⟦ f ⟧ₛ) IHn) as H.
         asimpl in H. apply H.
      ++ left. reflexivity.
  Qed.

  Theorem pr_stand_tm :
    forall {n : nat} {Γ : HOL_ctx n} (t : tm n) (s : st),
      stand_tm n t -> Γ ⊢⟨ n ⟩ t ~: s ->
      Γ ∣ HOL_ctx_stand n Γ ⊢| n | 𝕊 s t.
  Proof.
    intros n Γ t s stand H. induction H;
      try rename IHHOL_typing into IH;
      try rename IHHOL_typing1 into IH1;
      try rename IHHOL_typing2 into IH2;
      try rename IHHOL_typing3 into IH3.
    - apply pr_ax. apply typ_stand. apply stand_in_stand_ctx.
    - dependent destruction stand. specialize (IH stand).
      apply pr_sort_lam. simpl in IH. assumption.
    - dependent destruction stand.
      specialize (IH1 stand1); specialize (IH2 stand2).
      apply (pr_sort_app s); assumption.
    - apply pr_sort_Z. apply typ_stand.
    - dependent destruction stand. specialize (IH stand).
      apply pr_sort_S; assumption.
    - dependent destruction stand.
      specialize (IH1 stand1); specialize (IH2 stand2);
        specialize (IH3 stand3).
      apply pr_sort_recN; assumption.
    - apply pr_sort_T. apply typ_stand.
    - apply pr_sort_F. apply typ_stand.
    - dependent destruction stand.
      specialize (IH1 stand1); specialize (IH2 stand2);
        specialize (IH3 stand3).
      apply pr_sort_recB; assumption.
    - apply pr_sort_nil. apply typ_stand.
    - dependent destruction stand.
      specialize (IH1 stand1); specialize (IH2 stand2).
      apply (pr_sort_cons); assumption.
    - dependent destruction stand.
      specialize (IH1 stand1); specialize (IH2 stand2);
        specialize (IH3 stand3).
      apply (pr_sort_recL s'); assumption.
    - dependent destruction stand.
      specialize (IH1 stand1); specialize (IH2 stand2).
      apply (pr_sort_pair); assumption.
    - dependent destruction stand. specialize (IH stand).
      apply (pr_sort_proj1 s'); assumption.
    - dependent destruction stand. specialize (IH stand).
      apply (pr_sort_proj2 s); assumption.
    - inversion stand.
    - inversion stand.
    - inversion stand.
  Qed.

  Corollary pr_stand_cl :
    forall (t : tm 0) (s : st),
      stand_tm 0 t ->
      False_rect st ⊢⟨ 0 ⟩ t ~: s ->
      False_rect st ∣ nil ⊢| 0 | 𝕊 s t.
  Proof.
    intros. apply (@pr_stand_tm 0 _ t s).
    apply H. apply H0.
  Qed.

End Standardization.

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
