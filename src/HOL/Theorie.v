From CRM Require Import Base Typing fintype.
Import CombineNotations SubstNotations.

Require Import PeanoNat List Datatypes Program.Equality.
Import ListNotations.

(*Reserved Notation "Γ | Ξ ⊢⟨ n ⟩ φ" (at level 88).*)

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

Lemma typ_ex_tm : forall (n : nat) (Γ : HOL_ctx n) (s : st) (φ : tm (S n)),
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

Lemma typ_eq_tm : forall (n : nat) (Γ : HOL_ctx n) (s : st)
                         (t : tm n) (u : tm n),
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s -> Γ ⊢⟨ n ⟩ t =⟨ s ⟩ u ~: ℙₛ.
Proof.
  intros. apply typ_forall.
  constructor. apply (typ_app s).
  constructor. apply typ_weaken. apply H.
  apply (typ_app s). constructor. apply typ_weaken. apply H0.
Qed.

Definition or_tm {n : nat} (t u : tm n) : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply imp_tm.
  apply imp_tm.
  exact (ren_tm shift t). apply var_tm. apply None.
  apply imp_tm. apply imp_tm.
  exact (ren_tm shift u). apply var_tm. apply None.
  apply var_tm. apply None.
Defined.

Notation "φ ∨ₛ ψ" := (or_tm φ ψ) (at level 80).

Lemma typ_eq_or : forall (n : nat) (Γ : HOL_ctx n) (t u : tm n),
    Γ ⊢⟨ n ⟩ t ~: ℙₛ -> Γ ⊢⟨ n ⟩ u ~: ℙₛ -> Γ ⊢⟨ n ⟩ t ∨ₛ u ~: ℙₛ.
Proof.
  intros. apply typ_forall. constructor.
  constructor. apply typ_weaken. apply H.
  constructor. constructor. constructor. apply typ_weaken.
  apply H0. constructor. constructor.
Qed.

Definition and_tm {n : nat} (t u : tm n) : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply imp_tm. apply imp_tm.
  apply (ren_tm shift t).
  apply imp_tm. apply (ren_tm shift u). apply var_tm. apply None.
  apply var_tm. apply None.
Defined.

Notation "φ ∧ₛ ψ" := (and_tm φ ψ) (at level 79).

Lemma typ_and : forall (n : nat) (Γ : HOL_ctx n) (φ ψ : tm n),
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

Lemma typ_true : forall (n : nat) (Γ : HOL_ctx n),
    Γ ⊢⟨ n ⟩ ⊤ₛ ~: ℙₛ.
Proof.
  intros. apply (typ_forall ℙₛ). repeat constructor.
Qed.

Definition false_tm {n : nat} : tm n.
Proof.
  apply forall_tm. apply ℙₛ. apply var_tm. apply None.
Defined.

Notation "⊥ₛ" := (false_tm).

Lemma typ_false : forall (n : nat) (Γ : HOL_ctx n),
    Γ ⊢⟨ n ⟩ ⊥ₛ ~: ℙₛ.
Proof.
  intros. apply (typ_forall ℙₛ). constructor.
Qed.

Definition not_tm {n : nat} (t : tm n) : tm n.
Proof.
  apply imp_tm. apply t. apply ⊥ₛ.
Defined.

Notation "¬ₛ φ" := (not_tm φ) (at level 79).

Lemma typ_not : forall (n : nat) (Γ : HOL_ctx n) (φ : tm n),
    Γ ⊢⟨ n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ¬ₛ φ ~: ℙₛ.
Proof.
  intros. constructor. apply H. apply typ_false.
Qed.

Definition proof_ctx (n : nat) (Γ : HOL_ctx n) := list (tm n).

Inductive wt_ctx {n : nat} {Γ : HOL_ctx n} : proof_ctx n Γ -> Prop :=
| wt_nil : wt_ctx nil
| wt_cons : forall {Ξ : proof_ctx n Γ} {φ : tm n},
    wt_ctx Ξ -> (Γ ⊢⟨ n ⟩ φ ~: ℙₛ) -> wt_ctx (φ :: Ξ).

Inductive proving : forall (n : nat) (Γ : HOL_ctx n)
                           (Ξ : proof_ctx n Γ) (φ : tm n), Prop :=
| ax : forall {n : nat} {Γ : HOL_ctx n}
              {Ξ : proof_ctx n Γ} {φ : tm n},
    wt_ctx Ξ -> In φ Ξ -> proving n Γ Ξ φ
| abs : forall {n : nat} {Γ : HOL_ctx n}
               {Ξ : proof_ctx n Γ} {φ ψ : tm n},
    proving n Γ (φ :: Ξ) ψ -> proving n Γ Ξ (φ ⇒ₛ ψ)
| app : forall {n : nat} {Γ : HOL_ctx n}
               {Ξ : proof_ctx n Γ} {φ ψ : tm n},
    proving n Γ Ξ (φ ⇒ₛ ψ) -> proving n Γ Ξ φ ->
    proving n Γ Ξ ψ
| abs_f : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
                 {φ : tm (S n)} {s : st},
    proving (S n) (s .: Γ) (List.map (ren_tm shift) Ξ) φ ->
    proving n Γ Ξ (∀ₛ s φ)
| app_f : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
                 {φ : tm (S n)} {t : tm n} {s : st},
    proving n Γ Ξ (∀ₛ s φ) -> Γ ⊢⟨ n ⟩ t ~: s ->
    proving n Γ Ξ (φ [t .: (fun v => ⟦ v ⟧ₛ)]).

Lemma wt_proving :
  forall (n : nat) (Γ : HOL_ctx n) (Ξ : proof_ctx n Γ) (φ : tm n),
    proving n Γ Ξ φ -> wt_ctx Ξ /\ (Γ ⊢⟨ n ⟩ φ ~: ℙₛ).
Proof.
  intros. induction H.
  - split. apply H. induction Ξ. inversion H0.
    simpl in H0. destruct H0. subst. inversion H. apply H3.
    inversion H. apply IHΞ. apply H3. apply H0.
  - destruct IHproving as [wtφΞ wtψ].
    inversion wtφΞ. subst.
    split; [exact H2 | constructor ; [apply H3 | apply wtψ]].
  - destruct IHproving1 as [wtΞ wtψ].
    dependent destruction wtψ. split. apply wtΞ.
    apply wtψ2.
  - destruct IHproving. split.
    + clear φ H H1. induction Ξ. constructor.
      inversion H0. constructor. apply (IHΞ H2).
      admit.
    + apply (typ_forall s). apply H1.
  - destruct IHproving. split. apply H1.
    apply (comp_typ_vec _ _ _ _ (s .: Γ)).
    asimpl. intro f; case f eqn:e.
    asimpl. apply typ_var. asimpl. apply H0.
    dependent destruction H2. apply H2.
Admitted.

Lemma ren_proof :
  forall (n m : nat) (Γ : HOL_ctx n) (Δ : HOL_ctx m)
         (Ξ : proof_ctx n Γ) (φ : tm n) (ξ : fin n -> fin m),
    (forall f, (ξ >> Δ) f = Γ f) ->
    proving n Γ Ξ φ -> proving m Δ (map (ren_tm ξ) Ξ) (ren_tm ξ φ).
Proof.
  intros. induction H0.
  - induction Ξ.
    + inversion H1.
    + inversion H0; subst. specialize (IHΞ H4).
      destruct H1.
      ++ subst. simpl. constructor.
         constructor. admit.
         apply (typ_ren m n ξ Δ Γ φ ℙₛ H H5). constructor.
         reflexivity.
      ++ specialize (IHΞ H1). simpl. constructor.
         admit. admit.

Theorem typ_ren :
  forall (n m : nat) (ξ : fin m -> fin n) (Γ : HOL_ctx n) (Δ : HOL_ctx m)
         (t : tm m) (s : st),
    (forall f, (ξ >> Γ) f = Δ f) ->
    Δ ⊢⟨ m ⟩ t ~: s -> Γ ⊢⟨ n ⟩ ren_tm ξ t ~: s.
    proving n Γ Ξ φ ->
