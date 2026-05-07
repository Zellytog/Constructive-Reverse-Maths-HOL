From CRM Require Import Base Typing Reduction Theorie fintype.
Import CombineNotations SubstNotations.
From CRM Require Import Prelude.ListCRM.

Require Import PeanoNat List.

Definition shift11 {n : nat} (g : fin (S n)) : fin (S (S n)).
Proof.
  destruct g.
  - apply Some. apply Some. apply f.
  - apply None.
Defined.

Lemma typ_shift : forall (n : nat) (Γ : HOL_ctx n)
                         (s s' s0: st) (t : tm (S n)),
    s .: Γ ⊢⟨ S n ⟩ t ~: s0 ->
    s .: (s' .: Γ) ⊢⟨ S (S n) ⟩ ren_tm shift11 t ~: s0.
Proof.
  intros. apply (typ_ren (S (S n)) (S n) shift11 (s .: (s' .: Γ)) (s .: Γ)).
  intro. unfold ">>"; simpl. case f; reflexivity.
  apply H.
Qed.

Definition ex_tm {n : nat} (s : st) (φ : tm (S n)) : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply imp_tm.
  apply forall_tm. apply s. apply imp_tm.
  exact (ren_tm shift11 φ). apply var_tm. apply Some. apply None.
  apply var_tm. apply None.
Defined.

Notation "∃ₛ" := (ex_tm) (at level 80).

Lemma typ_ex : forall {n : nat} {Γ : HOL_ctx n} {φ : tm (S n)} (s : st),
    s .: Γ ⊢⟨ S n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ∃ₛ s φ ~: ℙₛ.
Proof.
  intros. apply typ_forall.
  constructor. apply typ_forall. constructor.
  apply typ_shift. apply H.
  constructor. constructor.
Qed.

Definition eq_tm {n : nat} (s : st) (t : tm n) (u : tm n) : tm n.
Proof.
  apply forall_tm. apply (s →ₛ ℙₛ). apply imp_tm.
  apply app_tm. apply var_tm; apply None.
  exact (ren_tm shift t).
  apply app_tm. apply var_tm; apply None.
  exact (ren_tm shift u).
Defined.

Notation "t =⟨ s ⟩ u" := (eq_tm s t u) (at level 77).

Lemma typ_eq : forall {n : nat} {Γ : HOL_ctx n} (s : st)
                         {t u : tm n},
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s -> Γ ⊢⟨ n ⟩ t =⟨ s ⟩ u ~: ℙₛ.
Proof.
  intros. apply typ_forall.
  constructor. apply (typ_app s).
  constructor. apply typ_weaken. apply H.
  apply (typ_app s). constructor. apply typ_weaken. apply H0.
Qed.

Definition or_tm {n : nat} (φ ψ : tm n) : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply imp_tm.
  apply imp_tm.
  exact (ren_tm shift φ). apply var_tm. apply None.
  apply imp_tm. apply imp_tm.
  exact (ren_tm shift ψ). apply var_tm. apply None.
  apply var_tm. apply None.
Defined.

Notation "φ ∨ₛ ψ" := (or_tm φ ψ) (at level 80).

Lemma typ_or : forall {n : nat} {Γ : HOL_ctx n} {φ ψ : tm n},
    Γ ⊢⟨ n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ -> Γ ⊢⟨ n ⟩ φ ∨ₛ ψ ~: ℙₛ.
Proof.
  intros. apply typ_forall. constructor.
  constructor. apply typ_weaken. apply H.
  constructor. constructor. constructor. apply typ_weaken.
  apply H0. constructor. constructor.
Qed.

Definition and_tm {n : nat} (φ ψ : tm n) : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply imp_tm. apply imp_tm.
  apply (ren_tm shift φ).
  apply imp_tm. apply (ren_tm shift ψ). apply var_tm. apply None.
  apply var_tm. apply None.
Defined.

Notation "φ ∧ₛ ψ" := (and_tm φ ψ) (at level 79).

Lemma typ_and : forall {n : nat} {Γ : HOL_ctx n} {φ ψ : tm n},
    Γ ⊢⟨ n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ -> Γ ⊢⟨ n ⟩ φ ∧ₛ ψ ~: ℙₛ.
Proof.
  intros. constructor.
  constructor. constructor. apply typ_weaken. apply H.
  constructor. apply typ_weaken. apply H0.
  constructor. constructor.
Qed.

Definition true_tm {n : nat} : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply imp_tm. apply var_tm. apply None.
  apply var_tm. apply None.
Defined.

Notation "⊤ₛ" := (true_tm).

Lemma typ_true : forall {n : nat} (Γ : HOL_ctx n),
    Γ ⊢⟨ n ⟩ ⊤ₛ ~: ℙₛ.
Proof.
  intros. apply (typ_forall ℙₛ). repeat constructor.
Qed.

Definition false_tm {n : nat} : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply var_tm. apply None.
Defined.

Notation "⊥ₛ" := (false_tm).

Lemma typ_false : forall {n : nat} (Γ : HOL_ctx n),
    Γ ⊢⟨ n ⟩ ⊥ₛ ~: ℙₛ.
Proof.
  intros. apply (typ_forall ℙₛ). constructor.
Qed.

Definition not_tm {n : nat} (φ : tm n) : tm n.
Proof.
  apply imp_tm. apply φ. apply ⊥ₛ.
Defined.

Notation "¬ₛ φ" := (not_tm φ) (at level 79).

Lemma typ_not : forall {n : nat} {Γ : HOL_ctx n} {φ : tm n},
    Γ ⊢⟨ n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ¬ₛ φ ~: ℙₛ.
Proof.
  intros. constructor. apply H. apply typ_false.
Qed.

Definition relat_forall_tm {n : nat} (s : st) (φ : tm (S n))
  : tm n.
Proof.
  apply forall_tm. apply s. apply imp_tm.
  apply sort_tm. apply s. apply var_tm. apply var_zero.
  apply φ.
Defined.

Notation "∀{ s } φ" := (relat_forall_tm s φ) (at level 80).

Lemma typ_relat_forall :
  forall {n : nat} {Γ : HOL_ctx n} (s : st) {φ : tm (S n)},
    s .: Γ ⊢⟨ S n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ∀{ s } φ ~: ℙₛ.
Proof.
  intros. apply typ_forall. constructor.
  constructor. constructor. apply H.
Qed.

Definition relat_ex_tm {n : nat} (s : st) (φ : tm (S n)) : tm n.
Proof.
  apply ex_tm. apply s. apply and_tm.
  apply sort_tm. apply s. apply var_tm. apply var_zero.
  apply φ.
Defined.

Notation "∃{ s } φ" := (relat_ex_tm s φ) (at level 80).

Lemma typ_relat_ex :
  forall {n : nat} {Γ : HOL_ctx n} (s : st) {φ : tm (S n)},
    s .: Γ ⊢⟨ S n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ∃{ s } φ ~: ℙₛ.
Proof.
  intros. apply typ_ex. apply typ_and.
  constructor. constructor. apply H.
Qed.

Lemma proving_refl :
  forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
         {t : tm n} {s : st},
    wt_ctx Ξ -> Γ ⊢⟨ n ⟩ t ~: s -> proving n Γ Ξ (t =⟨ s ⟩ t).
Proof.
  intros. unfold eq_tm. apply pr_abs_f.
  apply pr_abs. apply pr_ax. constructor.
  apply (typ_app s). constructor. apply typ_weaken; apply H0.
  apply (map_forall _ _ (ren_tm shift) (fun x => typ_weaken n Γ x ℙₛ (s →ₛ ℙₛ))).
  apply H. simpl. left; reflexivity.
Qed.

Lemma eq_elim :
  forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
         {t : tm n} {u φ : tm n} {s : st},
    proving n Γ Ξ (t =⟨ s ⟩ u) ->
    Γ ⊢⟨ n ⟩ φ ~: s →ₛ ℙₛ ->
    proving n Γ Ξ (φ @ₛ t) ->
    proving n Γ Ξ (φ @ₛ u).
Proof.
  intros.
  apply (pr_app_f φ (s →ₛ ℙₛ)) in H.
  asimpl in H.
  apply (pr_app (φ @ₛ t) H H1).
  apply H0.
Qed.

Lemma def_eq_to_eq :
  forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
         {t u : tm n} {s : st},
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s ->
    t =ₛ u -> wt_ctx Ξ ->
    proving n Γ Ξ (t =⟨ s ⟩ u).
Proof.
  intros. apply (pr_transp (t =⟨ s ⟩ t)).
  apply proving_refl. apply H2.
  apply H. apply typ_eq.
  apply H. apply H0.
  repeat apply βeq_compat.
  apply ren_βeq.
  apply H1.
Qed.
