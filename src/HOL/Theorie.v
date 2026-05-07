From CRM Require Import Base Typing Reduction fintype.
Import CombineNotations SubstNotations.

Require Import PeanoNat List Datatypes Program.Equality.
Import ListNotations.

(*Reserved Notation "Γ | Ξ ⊢⟨ n ⟩ φ" (at level 88).*)


Require Import CRM.Prelude.ListCRM.

Definition proof_ctx (n : nat) (Γ : HOL_ctx n) := list (tm n).

Definition wt_ctx {n : nat} {Γ : HOL_ctx n} (Ξ : proof_ctx n Γ) : Prop :=
  forall_l (fun Θ => Γ ⊢⟨ n ⟩ Θ ~: ℙₛ) Ξ.

Inductive proving : forall (n : nat) (Γ : HOL_ctx n)
                           (Ξ : proof_ctx n Γ) (φ : tm n), Prop :=
| pr_ax : forall {n : nat} {Γ : HOL_ctx n}
                 {Ξ : proof_ctx n Γ} {φ : tm n},
    wt_ctx Ξ -> In φ Ξ -> proving n Γ Ξ φ
| pr_transp : forall {n : nat} {Γ : HOL_ctx n}
                     {Ξ : proof_ctx n Γ} (φ : tm n)
                     {ψ : tm n},
    proving n Γ Ξ φ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ ->
    φ =ₛ ψ -> proving n Γ Ξ ψ
| pr_abs : forall {n : nat} {Γ : HOL_ctx n}
                  {Ξ : proof_ctx n Γ} {φ ψ : tm n},
    proving n Γ (φ :: Ξ) ψ -> proving n Γ Ξ (φ ⇒ₛ ψ)
| pr_app : forall {n : nat} {Γ : HOL_ctx n}
                  {Ξ : proof_ctx n Γ} (φ : tm n)
                  {ψ : tm n},
    proving n Γ Ξ (φ ⇒ₛ ψ) -> proving n Γ Ξ φ ->
    proving n Γ Ξ ψ
| pr_abs_f : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
                    {φ : tm (S n)} {s : st},
    proving (S n) (s .: Γ) (List.map (ren_tm shift) Ξ) φ ->
    proving n Γ Ξ (∀ₛ s φ)
| pr_app_f : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
                    {φ : tm (S n)} (t : tm n) (s : st),
    proving n Γ Ξ (∀ₛ s φ) -> Γ ⊢⟨ n ⟩ t ~: s ->
    proving n Γ Ξ (φ [t .: (fun v => ⟦ v ⟧ₛ)])
| pr_recN : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
                   {φ : tm n},
    proving n Γ Ξ (φ @ₛ Zₛ) ->
    proving n Γ Ξ
      (∀ₛ ℕₛ ((ren_tm shift φ @ₛ ((S n) __tm var_zero)) ⇒ₛ
                (ren_tm shift φ @ₛ (Sₛ ((S n) __tm var_zero))))) ->
    proving n Γ Ξ (∀ₛ ℕₛ (ren_tm shift φ @ₛ ((S n) __tm var_zero)))
| pr_recB : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
                   {φ : tm n},
    proving n Γ Ξ (φ @ₛ ttₛ) ->
    proving n Γ Ξ (φ @ₛ ffₛ) ->
    proving n Γ Ξ (∀ₛ 𝔹ₛ (ren_tm shift φ @ₛ ((S n) __tm var_zero)))
| pr_recL : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n Γ}
                   {s : st} {φ : tm n},
    proving n Γ Ξ (φ @ₛ []ₛ) ->
    proving n Γ Ξ
      (∀ₛ s
        (∀ₛ (𝕃ₛ s)
          (ren_tm (shift >> shift) φ @ₛ
             (((S (S n)) __tm (shift var_zero)) ::ₛ
             ((S (S n)) __tm var_zero))))) ->
    proving n Γ Ξ (∀ₛ (𝕃ₛ s) (ren_tm shift φ @ₛ ((S n) __tm var_zero))).

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
  - destruct IHproving1 as [H1 H2]. split; [apply H1|].
    constructor. apply (typ_app ℕₛ).
    apply typ_weaken. dependent destruction H2.
    dependent destruction H2_0. apply H2_.
    constructor.
  - destruct IHproving1 as [H1 H2]. split; [apply H1|].
    constructor. apply (typ_app 𝔹ₛ).
    apply typ_weaken. dependent destruction H2.
    dependent destruction H2_0. apply H2_.
    constructor.
  - destruct IHproving1 as [H1 H2]. split; [apply H1|].
    constructor. apply (typ_app (𝕃ₛ s)).
    apply typ_weaken. dependent destruction H2.
    dependent destruction H2_0.
    destruct IHproving2 as [_ H3].
    dependent destruction H3. dependent destruction H3.
    dependent destruction H3.
    dependent destruction H3_0.
    dependent destruction H3_0_1.
    simpl in H3_.
    assert (ren_tm (shift >> shift) φ =
              ren_tm shift (ren_tm shift φ)).
    asimpl; reflexivity.
    apply (typ_weaken_rev _ _ _ _ s).
    apply (typ_weaken_rev _ _ _ _ (𝕃ₛ s)).
    asimpl. apply H3_.
    constructor.
Qed.

Lemma ren_proof :
  forall (n m : nat) (Γ : HOL_ctx n) (Δ : HOL_ctx m)
         (Ξ : proof_ctx n Γ) (φ : tm n) (ξ : fin n -> fin m),
    (forall f, (ξ >> Δ) f = Γ f) ->
    proving n Γ Ξ φ -> proving m Δ (map (ren_tm ξ) Ξ) (ren_tm ξ φ).
Proof.
  intros; revert m Δ ξ H; induction H0; intros; simpl.
  - apply pr_ax.
    apply (map_forall _ _ (ren_tm ξ)
             (fun x => typ_ren m n ξ Δ Γ x _ H1)).
    apply H. apply (in_map (ren_tm ξ) Ξ φ H0).
  - apply (ren_βeq n m φ ψ ξ) in H1.
    apply (pr_transp (ren_tm ξ φ)).
    apply IHproving. apply H2. apply (typ_ren _ _ ξ Δ Γ).
    apply H2. apply H. apply H1.
  - simpl; apply pr_abs. apply IHproving. apply H.
  - simpl. specialize (IHproving1 _ _ _ H).
    specialize (IHproving2 _ _ _ H).
    apply (pr_app _ IHproving1 IHproving2).
  - asimpl. apply pr_abs_f.
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
    specialize (pr_app_f _ _ IHproving H2); intro.
    asimpl in H3. apply H3.
  - asimpl.
    specialize (IHproving1 m Δ ξ H); specialize (IHproving2 m Δ ξ H).
    asimpl in IHproving2.
    specialize (@pr_recN m Δ (map (ren_tm ξ) Ξ) (ren_tm ξ φ) IHproving1).
    intro H0. asimpl in H0. apply H0.
    apply IHproving2.
  - asimpl.
    specialize (IHproving1 m Δ ξ H).
    specialize (IHproving2 m Δ ξ H).
    asimpl in IHproving1; asimpl in IHproving2.
    specialize (pr_recB IHproving1 IHproving2).
    asimpl. trivial.
  - asimpl.
    specialize (IHproving1 m Δ ξ H).
    specialize (IHproving2 m Δ ξ H).
    asimpl in IHproving1; simpl in IHproving2.
    specialize (@pr_recL m Δ (map (ren_tm ξ) Ξ) s (ren_tm ξ φ)).
    asimpl. intro H0; specialize (H0 IHproving1).
    apply H0.
    unfold ">>" in IHproving2.
    asimpl in IHproving2.
    apply IHproving2.
Qed.

Lemma subst_proof :
  forall (n m : nat) (v : HOL_vec n m) (Γ : HOL_ctx m) (Δ : HOL_ctx n)
         (Ξ : proof_ctx n Δ) (φ : tm n),
    Γ ⊢⟨ m ⟩ v ~:⟨ n , Δ ⟩ -> proving n Δ Ξ φ ->
    proving m Γ (map (subst_tm v) Ξ) (φ [ v ]).
Proof.
  intros n m v Γ Δ Ξ φ Hv Hφ; revert m v Γ Hv; induction Hφ; intros; simpl.
  - apply pr_ax.
    apply (map_forall (fun x => Γ  ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Γ0 ⊢⟨ m ⟩ x ~: ℙₛ)).
    intro a. apply comp_typ_vec.
    apply Hv. apply H.
    apply (in_map (subst_tm v) Ξ φ H0).
  - apply (subst_βeq n m φ ψ v) in H0.
    apply (pr_transp (subst_tm v φ)).
    apply IHHφ. apply Hv.
    apply (comp_typ_vec _ _ v Γ0 Γ).
    apply Hv. apply H. apply H0.
  - asimpl. apply pr_abs. apply IHHφ.
    apply Hv.
  - specialize (IHHφ1 _ _ _ Hv).
    specialize (IHHφ2 _ _ _ Hv).
    apply (pr_app _ IHHφ1 IHHφ2).
  - asimpl. apply pr_abs_f.
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
    apply (@pr_app_f _ _ _ _ (t [v])) in IHHφ.
    asimpl in IHHφ.
    assert (φ [t[v] .: v >> (ren_tm shift >> subst_tm (t[v] .: m __tm))] = φ[t[v] .: v]).
    apply ext_tm.
    intro f; case f eqn : e.
    asimpl. reflexivity. reflexivity.
    apply (eq_rec _ (proving m Γ0 (map (subst_tm v) Ξ)) IHHφ _ H0).
    apply (comp_typ_vec _ _ _ _ _ _ _ Hv H).
  - specialize (IHHφ1 m v Γ0 Hv). specialize (IHHφ2 m v Γ0 Hv).
    asimpl. asimpl in IHHφ1. asimpl in IHHφ2.
    assert (subst_tm (v >> ren_tm shift) φ = ren_tm shift (subst_tm v φ)).
    asimpl. reflexivity.
    rewrite H in IHHφ2.
    specialize (pr_recN IHHφ1 IHHφ2).
    asimpl. trivial.
  - asimpl; asimpl in IHHφ1; asimpl in IHHφ2.
    specialize (pr_recB (IHHφ1 _ _ _ Hv) (IHHφ2 _ _ _ Hv)).
    asimpl. trivial.
  - specialize (IHHφ1 m v Γ0 Hv); specialize (IHHφ2 m v Γ0 Hv).
    asimpl; asimpl in IHHφ1; asimpl in IHHφ2.
    assert
      (subst_tm
         (shift >>
            (((S m)__tm var_zero .: v >> ren_tm shift) >>
               ren_tm shift)) φ =
         ren_tm (shift >> shift) (subst_tm v φ)).
    asimpl. apply ext_tm.
    intro; unfold ">>"; asimpl.
    reflexivity.
    rewrite H in IHHφ2; clear H.
    specialize (pr_recL IHHφ1 IHHφ2).
    asimpl. trivial.
Qed.

Lemma weaken_proof :
  forall (n : nat) (Γ : HOL_ctx n)
         (Ξ Θ : proof_ctx n Γ) (φ : tm n),
    proving n Γ Ξ φ -> incl Ξ Θ ->
    wt_ctx Θ -> proving n Γ Θ φ.
Proof.
  intros; revert Θ H0 H1; induction H; intros.
  - apply pr_ax. apply H2. apply H1.
    apply H0.
  - apply (pr_transp φ). apply IHproving.
    apply H2. apply H3. apply H0. apply H1.
  - apply pr_abs. apply IHproving.
    intro χ. intro χφΞ.
    simpl; simpl in χφΞ.
    destruct χφΞ as [ φχ | χΞ ].
    left; apply φχ.
    right; apply (H0 _ χΞ).
    constructor.
    destruct (wt_proving n Γ (φ :: Ξ) ψ H) as [H2 _].
    inversion H2. apply H5.
    apply H1.
  - apply (pr_app φ). apply IHproving1.
    apply H1. apply H2. apply IHproving2.
    apply H1. apply H2.
  - apply pr_abs_f. apply IHproving.
    intro x.
    intro xΞ. rewrite in_map_iff. rewrite in_map_iff in xΞ.
    destruct xΞ. exists x0. destruct H2.
    split; [apply H2|].
    apply H0. apply H3.
    apply (map_forall _ _ (ren_tm shift)
             (fun x => typ_weaken n Γ x _ _) Θ H1).
  - apply (pr_app_f t s).
    apply IHproving. apply H1. apply H2.
    apply H0.
  - apply pr_recN. apply IHproving1. apply H1. apply H2.
    apply IHproving2. apply H1. apply H2.
  - apply pr_recB. apply IHproving1. apply H1. apply H2.
    apply IHproving2. apply H1. apply H2.
  - apply pr_recL. apply IHproving1. apply H1. apply H2.
    apply IHproving2. apply H1. apply H2.
Qed.

Lemma weaken_proof_1 :
  forall (n : nat) (Γ : HOL_ctx n)
         (Ξ : proof_ctx n Γ) (φ ψ : tm n),
    proving n Γ Ξ φ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ ->
    proving n Γ (ψ :: Ξ) φ.
Proof.
  intros.
  apply (weaken_proof n Γ Ξ (ψ :: Ξ)).
  apply H. intros x xΞ; simpl; right; apply xΞ.
  constructor. apply H0.
  apply (wt_proving n Γ Ξ φ H).
Qed.
