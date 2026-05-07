Require Import CRM.HOL.Base.
Require Import CRM.HOL.fintype.
Import CombineNotations SubstNotations.

Require Import PeanoNat.
Require Import List.
Require Import Program.Equality.
Import ListNotations.

Reserved Notation "Γ ⊢⟨ n ⟩ t ~: s" (at level 87).

Inductive HOL_typing : forall n : nat, (fin n -> st) -> tm n -> st -> Prop :=
| typ_var : forall {n : nat} {Γ : fin n -> st} {v : fin n},
    Γ ⊢⟨ n ⟩ ⟦ v ⟧ₛ ~: Γ v
| typ_lam : forall {n : nat} {Γ : fin n -> st} {t : tm (S n)} {s s' : st},
    s .: Γ ⊢⟨ S n ⟩ t ~: s' -> Γ ⊢⟨ n ⟩ ƛ t ~: s →ₛ s'
| typ_app : forall {n : nat} {Γ : fin n -> st} {t u : tm n} (s : st) {s' : st},
    Γ ⊢⟨ n ⟩ t ~: s →ₛ s' -> Γ ⊢⟨ n ⟩ u ~: s -> Γ ⊢⟨ n ⟩ t @ₛ u ~: s'
| typ_z : forall {n : nat} {Γ : fin n -> st}, Γ ⊢⟨ n ⟩ Zₛ ~: ℕₛ
| typ_s : forall {n : nat} {Γ : fin n -> st} {t : tm n},
    Γ ⊢⟨ n ⟩ t ~: ℕₛ -> Γ ⊢⟨ n ⟩ Sₛ t ~: ℕₛ
| typ_recN : forall {n : nat} {Γ : fin n -> st} {t u v : tm n} {s : st},
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: ℕₛ →ₛ s →ₛ s -> Γ ⊢⟨ n ⟩ v ~: ℕₛ ->
    Γ ⊢⟨ n ⟩ recℕₛ t u v ~: s
| typ_tt : forall {n : nat} {Γ : fin n -> st}, Γ ⊢⟨ n ⟩ ttₛ ~: 𝔹ₛ
| typ_ff : forall {n : nat} {Γ : fin n -> st}, Γ ⊢⟨ n ⟩ ffₛ ~: 𝔹ₛ
| typ_recB : forall {n : nat} {Γ : fin n -> st} {t u v : tm n} {s : st},
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s -> Γ ⊢⟨ n ⟩ v ~: 𝔹ₛ ->
    Γ ⊢⟨ n ⟩ rec𝔹ₛ t u v ~: s
| typ_nil : forall {n : nat} {Γ : fin n -> st} {s : st}, Γ ⊢⟨ n ⟩ []ₛ ~: 𝕃ₛ s
| typ_cons : forall {n : nat} {Γ : fin n -> st} {t u : tm n} {s : st},
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: 𝕃ₛ s -> Γ ⊢⟨ n ⟩ t ::ₛ u ~: 𝕃ₛ s
| typ_recL : forall {n : nat} {Γ : fin n -> st} {t u v : tm n} {s : st}
                    (s' : st),
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s ->
    Γ ⊢⟨ n ⟩ v ~: 𝕃ₛ s' -> Γ ⊢⟨ n ⟩ rec𝕃ₛ t u v ~: s
| typ_pair : forall {n : nat} {Γ : fin n -> st} {t u : tm n} {s s' : st},
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s' -> Γ ⊢⟨ n ⟩ ⟨ t, u ⟩ₛ ~: s ×ₛ s'
| typ_proj1 : forall {n : nat} {Γ : fin n -> st} {t : tm n} {s : st} (s' : st),
    Γ ⊢⟨ n ⟩ t ~: s ×ₛ s' -> Γ ⊢⟨ n ⟩ π¹ₛ t ~: s
| typ_proj2 : forall {n : nat} {Γ : fin n -> st} {t : tm n} (s : st) {s' : st},
    Γ ⊢⟨ n ⟩ t ~: s ×ₛ s' -> Γ ⊢⟨ n ⟩ π²ₛ t ~: s'
| typ_imp : forall {n : nat} {Γ : fin n -> st} {φ ψ : tm n},
    Γ ⊢⟨ n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ -> Γ ⊢⟨ n ⟩ φ ⇒ₛ ψ ~: ℙₛ
| typ_forall : forall {n : nat} {Γ : fin n -> st} {φ : tm (S n)} (s : st),
    s .: Γ ⊢⟨ S n ⟩ φ ~: ℙₛ -> Γ ⊢⟨ n ⟩ ∀ₛ s φ ~: ℙₛ
| typ_sort : forall {n : nat} {Γ : fin n -> st} {t : tm n} {s : st},
    Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ 𝕊 s t ~: ℙₛ
where "Γ ⊢⟨ n ⟩ t ~: s" := (HOL_typing n Γ t s).

Proposition id_typ : forall (n : nat) (Γ : fin n -> st) (s : st),
    Γ ⊢⟨ n ⟩ ƛ ⟦ (None : fin (S n)) ⟧ₛ ~: s →ₛ s.
Proof.
  intros. constructor. constructor.
Qed.

Definition HOL_ctx (n : nat) := fin n -> st.

Definition HOL_vec (n m : nat) := fin n -> tm m.

Definition wt_vec (n m : nat) (Γ : HOL_ctx m) (Δ : HOL_ctx n) (v : HOL_vec n m)
  : Prop := forall f : fin n, Γ ⊢⟨ m ⟩ v f ~: Δ f.

Notation "Γ ⊢⟨ m ⟩ v ~:⟨ n , Δ ⟩" := (wt_vec n m Γ Δ v) (at level 87).  

Theorem typ_ren :
  forall (n m : nat) (ξ : fin m -> fin n) (Γ : HOL_ctx n) (Δ : HOL_ctx m)
         (t : tm m) (s : st),
    (forall f, (ξ >> Γ) f = Δ f) ->
    Δ ⊢⟨ m ⟩ t ~: s -> Γ ⊢⟨ n ⟩ ren_tm ξ t ~: s.
Proof.
  intros; revert n Γ ξ H. induction H0; intros; asimpl;
    try (specialize (IHHOL_typing1 _ _ _ H); specialize (IHHOL_typing2 _ _ _ H));
    try (specialize (IHHOL_typing3 _ _ _ H));
    try (specialize (IHHOL_typing _ _ _ H)); try constructor;
    try (apply IHHOL_typing1); try (apply IHHOL_typing2);
    try (apply IHHOL_typing3); try (apply IHHOL_typing).
  - unfold ">>" in H. specialize (H v). rewrite <- H. constructor.
  - intro f. case f. simpl. apply H. reflexivity.
  - exact (typ_app s IHHOL_typing1 IHHOL_typing2).
  - apply (typ_recL s'). apply IHHOL_typing1. apply IHHOL_typing2.
    apply IHHOL_typing3.
  - apply (typ_proj1 s'). apply IHHOL_typing.
  - apply (typ_proj2 s). apply IHHOL_typing.
  - intro f. case f. simpl. apply H. reflexivity.
Qed.

Theorem typ_ren_rev :
  forall (n m : nat) (ξ : fin m -> fin n) (Γ : HOL_ctx n) (Δ : HOL_ctx m)
         (t : tm m) (s : st),
    (forall f, (ξ >> Γ) f = Δ f) ->
    Γ ⊢⟨ n ⟩ ren_tm ξ t ~: s -> Δ ⊢⟨ m ⟩ t ~: s.
Proof.
  intros n m ξ Γ Δ t s H H0; revert n ξ Γ Δ s H H0; induction t;
    intros; asimpl;
    try (asimpl in H0; dependent destruction H0; try constructor);
    try (apply (IHt _ _ _ _ _ H H0));
    try (apply (IHt1 _ _ _ _ _ H H0_));
    try (apply (IHt2 _ _ _ _ _ H H0_0));
    try (apply (IHt3 _ _ _ _ _ H H0_1)).
  - unfold ">>" in H. rewrite H. constructor.
  - apply (IHt (S n) (var_zero .: ξ >> shift) (s .: Γ)).
    intro f; case f eqn : e. unfold ">>"; simpl.
    apply H. reflexivity. apply H0.
  - apply (typ_app s). apply (IHt1 _ _ _ _ _ H H0_).
    apply (IHt2 _ _ _ _ _ H H0_0).
  - apply (typ_recL s'). apply (IHt1 _ _ _ _ _ H H0_).
    apply (IHt2 _ _ _ _ _ H H0_0). apply (IHt3 _ _ _ _ _ H H0_1).
  - apply (typ_proj1 s'). apply (IHt _ _ _ _ _ H H0).
  - apply (typ_proj2 s). apply (IHt _ _ _ _ _ H H0).
  - apply (IHt (S n) (var_zero .: ξ >> shift) (s .: Γ)).
    intro f; case f eqn : e. unfold ">>"; simpl.
    apply H. reflexivity. apply H0.
Qed.

Theorem typ_weaken :
  forall (n : nat) (Γ : HOL_ctx n) (t : tm n) (s s' : st),
    Γ ⊢⟨ n ⟩ t ~: s -> s' .: Γ ⊢⟨ S n ⟩ ren_tm shift t ~: s.
Proof.
  intros. apply (typ_ren (S n) n shift (s' .: Γ) Γ t s).
  intro; unfold ">>"; reflexivity.
  apply H.
Qed.

Lemma typ_weaken_rev :
  forall (n : nat) (Γ : HOL_ctx n) (t : tm n) (s s' : st),
    s' .: Γ ⊢⟨ S n ⟩ ren_tm shift t ~: s -> Γ ⊢⟨ n ⟩ t ~: s.
Proof.
  intros. apply (typ_ren_rev (S n) n shift (s' .: Γ) Γ t s).
  intro; unfold ">>"; reflexivity.
  apply H.
Qed.

Theorem typ_weaken_vec :
  forall (n m :nat) (Γ : HOL_ctx m) (Δ : HOL_ctx n) (v : HOL_vec n m) (s : st),
    Γ ⊢⟨ m ⟩ v ~:⟨ n, Δ ⟩ -> s .: Γ ⊢⟨ S m ⟩ (v >> ren_tm shift) ~:⟨ n, Δ ⟩.
Proof.
  intros. induction n.
  intro f. inversion f.
  intro f. unfold ">>"; simpl. apply typ_weaken. apply (H f).
Qed.

Theorem comp_typ_vec :
  forall (n m : nat) (v : HOL_vec n m) (Γ : HOL_ctx m) (Δ : HOL_ctx n)
         (t : tm n) (s : st),
    Γ ⊢⟨ m ⟩ v ~:⟨ n , Δ ⟩ -> Δ ⊢⟨ n ⟩ t ~: s ->
    Γ ⊢⟨ m ⟩ t [ v ] ~: s.
Proof.
  intros; revert m v Γ H; induction H0; intros.
  - asimpl. apply H.
  - asimpl. constructor.
    apply IHHOL_typing.
    intro. case f eqn : e.
    asimpl. apply typ_weaken_vec. apply H.
    asimpl.
    assert (s .: Γ0 ⊢⟨ S m ⟩ (S m)__tm var_zero ~: (s .: Γ0) var_zero) as H1.
    apply typ_var. apply H1.
  - asimpl. apply (typ_app s). apply IHHOL_typing1. apply H.
    apply IHHOL_typing2. apply H.
  - constructor.
  - asimpl; apply typ_s. apply IHHOL_typing. apply H.
  - asimpl; constructor;
      [apply IHHOL_typing1 | apply IHHOL_typing2 | apply IHHOL_typing3]; apply H.
  - constructor.
  - constructor.
  - asimpl; constructor;
      [apply IHHOL_typing1 | apply IHHOL_typing2 | apply IHHOL_typing3]; apply H.
  - constructor.
  - asimpl; constructor;
      [apply IHHOL_typing1 | apply IHHOL_typing2]; apply H.
  - asimpl; apply (typ_recL s');
      [apply IHHOL_typing1 | apply IHHOL_typing2 | apply IHHOL_typing3]; apply H.
  - asimpl; constructor;
      [apply IHHOL_typing1 | apply IHHOL_typing2]; apply H.
  - asimpl; apply (typ_proj1 s'). apply IHHOL_typing. apply H.
  - asimpl; apply (typ_proj2 s). apply IHHOL_typing. apply H.
  - asimpl; constructor;
      [apply IHHOL_typing1 | apply IHHOL_typing2]; apply H.
  - asimpl. apply (typ_forall s).
    apply IHHOL_typing.
    intro. case f eqn : e.
    asimpl. apply typ_weaken_vec. apply H.
    asimpl.
    assert (s .: Γ0 ⊢⟨ S m ⟩ (S m)__tm var_zero ~: (s .: Γ0) var_zero) as H1.
    apply typ_var. apply H1.
  - asimpl. constructor. apply IHHOL_typing. apply H.
Qed.
