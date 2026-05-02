From CRM Require Import Base Typing fintype.
Import CombineNotations SubstNotations.

From Stdlib Require Import PeanoNat List Datatypes.
Import ListNotations.

Reserved Notation "Γ | Ξ ⊢ φ" (at level 85).

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

Definition ex_tm {n : nat} (φ : tm (S n)) : tm n.
Proof.
  apply forall_tm. apply imp_tm.
  apply forall_tm. apply imp_tm.
  exact (ren_tm shift11 φ). apply var_tm. apply Some. apply None.
  apply var_tm. apply None.
Defined.

Notation "∃ₛ" := (ex_tm).

Lemma typ_ex_tm : forall (n : nat) (Γ : HOL_ctx n) (s : st) (φ : tm (S n)),
    s .: Γ ⊢⟨ S n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ex_tm φ ~: ℙₛ.
Proof.
  intros. apply (typ_forall ℙₛ).
  constructor. apply (typ_forall s). constructor.
  apply typ_shift. apply H.
  constructor. constructor.
Qed.

Definition eq_tm {n : nat} (t : tm n) (u : tm n) : tm n.
Proof.
  apply forall_tm. apply imp_tm.
  apply app_tm. apply var_tm; apply None.
  exact (ren_tm shift t).
  apply app_tm. apply var_tm; apply None.
  exact (ren_tm shift u).
Defined.

Notation "t =ₛ u" := (eq_tm t u) (at level 86).

Lemma typ_eq_tm : forall (n : nat) (Γ : HOL_ctx n) (s : st)
                         (t : tm n) (u : tm n),
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s -> Γ ⊢⟨ n ⟩ t =ₛ u ~: ℙₛ.
Proof.
  intros. apply (typ_forall (s →ₛ ℙₛ)).
  constructor. apply (typ_app s).
  constructor. apply typ_weaken. apply H.
  apply (typ_app s). constructor. apply typ_weaken. apply H0.
Qed.

Definition proof_ctx (n : nat) (Γ : fin n -> st) := list (tm n).

Inductive wt_ctx {n : nat} {Γ : fin n -> st} : proof_ctx n -> Prop :=
| wt_nil : wt_ctx nil
| wt_cons : forall {Ξ : proof_ctx n} {φ : tm n},
    wt_ctx Ξ -> (Γ ⊢⟨ n ⟩ φ ~: ℙₛ) -> wt_ctx (φ :: Ξ).
