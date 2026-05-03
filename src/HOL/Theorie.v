From CRM Require Import Base Typing Reduction fintype.
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

Require Import CRM.Prelude.ListCRM.

Definition proof_ctx (n : nat) (Γ : HOL_ctx n) := list (tm n).

Definition wt_ctx {n : nat} {Γ : HOL_ctx n} (Ξ : proof_ctx n Γ) : Prop :=
  forall_l (fun Θ => Γ ⊢⟨ n ⟩ Θ ~: ℙₛ) Ξ.

Inductive proving : forall (n : nat) (Γ : HOL_ctx n)
                           (Ξ : proof_ctx n Γ) (φ : tm n), Prop :=
| ax : forall {n : nat} {Γ : HOL_ctx n}
              {Ξ : proof_ctx n Γ} {φ : tm n},
    wt_ctx Ξ -> In φ Ξ -> proving n Γ Ξ φ
| transp : forall {n : nat} {Γ : HOL_ctx n}
                  {Ξ : proof_ctx n Γ} {φ ψ : tm n},
    proving n Γ Ξ φ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ ->
    φ =ₛ ψ -> proving n Γ Ξ ψ
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

Lemma proving_refl :
  forall (n : nat) (Γ : HOL_ctx n) (Ξ : proof_ctx n Γ)
         (t : tm n) (s : st),
    wt_ctx Ξ -> Γ ⊢⟨ n ⟩ t ~: s -> proving n Γ Ξ (t =⟨ s ⟩ t).
Proof.
  intros. unfold eq_tm. apply abs_f.
  apply abs. apply ax. constructor.
  apply (typ_app s). constructor. apply typ_weaken; apply H0.
  apply (map_forall _ _ (ren_tm shift) (fun x => typ_weaken n Γ x ℙₛ (s →ₛ ℙₛ))).
  apply H. simpl. left; reflexivity.
Qed.

Lemma wt_proving :
  forall (n : nat) (Γ : HOL_ctx n) (Ξ : proof_ctx n Γ) (φ : tm n),
    proving n Γ Ξ φ -> wt_ctx Ξ /\ (Γ ⊢⟨ n ⟩ φ ~: ℙₛ).
Proof.
  intros. induction H.
  - split. apply H.
    apply (In_forall _ Ξ φ H H0).
  - destruct IHproving as [wtΞ wtφ].
    split ; [exact wtΞ | exact H0 ].
  - destruct IHproving as [wtφΞ wtψ].
    split; [exact (forall_tail _ _ _ wtφΞ) |].
    constructor. apply (forall_head _ _ _ wtφΞ).
    apply wtψ.
  - destruct IHproving1 as [wtΞ wtψ].
    dependent destruction wtψ. split. apply wtΞ.
    apply wtψ2.
  - destruct IHproving. split.
    + clear φ H H1.
      apply (map_forall_rev _ _ (ren_tm shift)
               (fun x => typ_weaken_rev n Γ x ℙₛ _)) in H0.
      apply H0.
    + apply (typ_forall s). apply H1.
  - destruct IHproving. split. apply H1.
    apply (comp_typ_vec _ _ _ _ (s .: Γ)).
    asimpl. intro f; case f eqn:e.
    asimpl. apply typ_var. asimpl. apply H0.
    dependent destruction H2. apply H2.
Qed.

Lemma ren_proof :
  forall (n m : nat) (Γ : HOL_ctx n) (Δ : HOL_ctx m)
         (Ξ : proof_ctx n Γ) (φ : tm n) (ξ : fin n -> fin m),
    (forall f, (ξ >> Δ) f = Γ f) ->
    proving n Γ Ξ φ -> proving m Δ (map (ren_tm ξ) Ξ) (ren_tm ξ φ).
Proof.
  intros; revert m Δ ξ H; induction H0; intros; simpl.
  - apply ax.
    apply (map_forall _ _ (ren_tm ξ)
             (fun x => typ_ren m n ξ Δ Γ x _ H1)).
    apply H. apply (in_map (ren_tm ξ) Ξ φ H0).
  -
  - simpl; apply abs. apply IHproving. apply H.
  - simpl. specialize (IHproving1 _ _ _ H).
    specialize (IHproving2 _ _ _ H).
    apply (app IHproving1 IHproving2).
  - asimpl. apply abs_f.
    specialize (IHproving _ (s .: Δ) (var_zero .: ξ >> shift)).
    asimpl in IHproving.
    rewrite map_map in IHproving. asimpl in IHproving.
    rewrite map_map. asimpl.
    rewrite (map_ext
               (ren_tm shift >> ren_tm (var_zero .: ξ >> shift))
               (ren_tm ξ >> ren_tm shift)) in IHproving.
    apply IHproving.
    intro f. unfold ">>". asimpl.
    case f eqn : e. simpl. asimpl. unfold ">>"; simpl.
    apply H. unfold ">>"; simpl. reflexivity.
    asimpl. reflexivity.
  - simpl. asimpl.
    specialize (IHproving m Δ ξ H1).
    asimpl in IHproving.
    assert (Δ ⊢⟨ m ⟩ ren_tm ξ t ~: s).
    apply (typ_ren _ _ _ _ _ _ _ H1 H).
    specialize (app_f IHproving H2); intro.
    asimpl in H3. apply H3.
Qed.

Lemma subst_proof :
  forall (n m : nat) (v : HOL_vec n m) (Γ : HOL_ctx m) (Δ : HOL_ctx n)
         (Ξ : proof_ctx n Δ) (φ : tm n),
    Γ ⊢⟨ m ⟩ v ~:⟨ n , Δ ⟩ -> proving n Δ Ξ φ ->
    proving m Γ (map (subst_tm v) Ξ) (φ [ v ]).
Proof.
  intros n m v Γ Δ Ξ φ Hv Hφ; revert m v Γ Hv; induction Hφ; intros; simpl.
  - apply ax.
    apply (map_forall (fun x => Γ  ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Γ0 ⊢⟨ m ⟩ x ~: ℙₛ)).
    intro a. apply comp_typ_vec.
    apply Hv. apply H.
    apply (in_map (subst_tm v) Ξ φ H0).
  - asimpl. apply abs. apply IHHφ.
    apply Hv.
  - specialize (IHHφ1 _ _ _ Hv).
    specialize (IHHφ2 _ _ _ Hv).
    apply (app IHHφ1 IHHφ2).
  - asimpl. apply abs_f.
    specialize (IHHφ (S m) ((S m)__tm var_zero .: v >> ren_tm shift)
                  (s .: Γ0)).
    asimpl in IHHφ.
    assert (s .: Γ0 ⊢⟨ S m ⟩ (S m)__tm var_zero .: v >> ren_tm shift ~:⟨ S n, s .: Γ ⟩).
    intro f. case f eqn : e.
    asimpl. unfold ">>". apply typ_weaken. apply Hv.
    constructor.
    specialize (IHHφ H).
    assert (map (subst_tm ((S m)__tm var_zero .: v >> ren_tm shift)) (map (ren_tm shift) Ξ) =
              (map (ren_tm shift) (map (subst_tm v) Ξ))).
    rewrite map_map. asimpl. unfold ">>". rewrite map_map. apply map_ext.
    intro f. asimpl. reflexivity.
    rewrite <- H0. apply IHHφ.
  - asimpl. specialize (IHHφ m v Γ0 Hv).
    asimpl in IHHφ.
    apply (@app_f _ _ _ _ (t [v])) in IHHφ.
    asimpl in IHHφ.
    assert (φ [t[v] .: v >> (ren_tm shift >> subst_tm (t[v] .: m __tm))] = φ[t[v] .: v]).
    apply ext_tm.
    intro f; case f eqn : e.
    asimpl. reflexivity. reflexivity.
    apply (eq_rec _ (proving m Γ0 (map (subst_tm v) Ξ)) IHHφ _ H0).
    apply (comp_typ_vec _ _ _ _ _ _ _ Hv H).
Qed.
