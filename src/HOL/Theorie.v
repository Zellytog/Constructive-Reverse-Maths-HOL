From CRM Require Import Base Typing Reduction fintype.
Import CombineNotations SubstNotations.

Require Import PeanoNat List Datatypes Program.Equality.
Import ListNotations.

(*Reserved Notation "Γ | Ξ ⊢⟨ n ⟩ φ" (at level 88).*)


Require Import CRM.Prelude.ListCRM.

Definition proof_ctx (n : nat) := list (tm n).

Definition wt_ctx {n : nat} (Γ : HOL_ctx n) (Ξ : proof_ctx n) : Prop :=
  forall_l (fun Θ => Γ ⊢⟨ n ⟩ Θ ~: ℙₛ) Ξ.

Inductive proving : forall (n : nat) (Γ : HOL_ctx n)
                           (Ξ : proof_ctx n) (φ : tm n), Prop :=
| pr_ax : forall {n : nat} {Γ : HOL_ctx n}
                 {Ξ : proof_ctx n} {φ : tm n},
    wt_ctx Γ Ξ -> In φ Ξ -> proving n Γ Ξ φ
| pr_transp : forall {n : nat} {Γ : HOL_ctx n}
                     {Ξ : proof_ctx n} (φ : tm n)
                     {ψ : tm n},
    proving n Γ Ξ φ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ ->
    φ =ₛ ψ -> proving n Γ Ξ ψ
| pr_abs : forall {n : nat} {Γ : HOL_ctx n}
                  {Ξ : proof_ctx n} {φ ψ : tm n},
    proving n Γ (φ :: Ξ) ψ -> proving n Γ Ξ (φ ⇒ₛ ψ)
| pr_app : forall {n : nat} {Γ : HOL_ctx n}
                  {Ξ : proof_ctx n} (φ : tm n)
                  {ψ : tm n},
    proving n Γ Ξ (φ ⇒ₛ ψ) -> proving n Γ Ξ φ ->
    proving n Γ Ξ ψ
| pr_abs_f : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                    {φ : tm (S n)} {s : st},
    proving (S n) (s .: Γ) (List.map (ren_tm shift) Ξ) φ ->
    proving n Γ Ξ (∀ₛ s φ)
| pr_app_f : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                    {φ : tm (S n)} (t : tm n) (s : st),
    proving n Γ Ξ (∀ₛ s φ) -> Γ ⊢⟨ n ⟩ t ~: s ->
    proving n Γ Ξ (φ [t .: (fun v => ⟦ v ⟧ₛ)])
| pr_recN : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                   {φ : tm n},
    proving n Γ Ξ (φ @ₛ Zₛ) ->
    proving n Γ Ξ
      (∀ₛ ℕₛ ((ren_tm shift φ @ₛ ((S n) __tm var_zero)) ⇒ₛ
                (ren_tm shift φ @ₛ (Sₛ ((S n) __tm var_zero))))) ->
    proving n Γ Ξ (∀ₛ ℕₛ (ren_tm shift φ @ₛ ((S n) __tm var_zero)))
| pr_recB : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                   {φ : tm n},
    proving n Γ Ξ (φ @ₛ ttₛ) ->
    proving n Γ Ξ (φ @ₛ ffₛ) ->
    proving n Γ Ξ (∀ₛ 𝔹ₛ (ren_tm shift φ @ₛ ((S n) __tm var_zero)))
| pr_recL : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                   {s : st} {φ : tm n},
    proving n Γ Ξ (φ @ₛ []ₛ) ->
    proving n Γ Ξ
      (∀ₛ s
        (∀ₛ (𝕃ₛ s)
          (ren_tm (shift >> shift) φ @ₛ
             (((S (S n)) __tm (shift var_zero)) ::ₛ
             ((S (S n)) __tm var_zero))))) ->
    proving n Γ Ξ (∀ₛ (𝕃ₛ s) (ren_tm shift φ @ₛ ((S n) __tm var_zero)))
| pr_sort_Z : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n},
    wt_ctx Γ Ξ -> proving n Γ Ξ (𝕊 ℕₛ Zₛ)
| pr_sort_S : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                     {t : tm n},
    proving n Γ Ξ (𝕊 ℕₛ t) -> proving n Γ Ξ (𝕊 ℕₛ (Sₛ t))
| pr_sort_recN : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                        {t u v : tm n} {s : st},
    proving n Γ Ξ (𝕊 s t) -> proving n Γ Ξ (𝕊 (ℕₛ →ₛ s →ₛ s) u) ->
    proving n Γ Ξ (𝕊 ℕₛ v) -> proving n Γ Ξ (𝕊 s (recℕₛ t u v))
| pr_sort_T : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n},
    wt_ctx Γ Ξ -> proving n Γ Ξ (𝕊 𝔹ₛ ttₛ)
| pr_sort_F : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n},
    wt_ctx Γ Ξ -> proving n Γ Ξ (𝕊 𝔹ₛ ffₛ)
| pr_sort_recB : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                        {t u v : tm n} {s : st},
    proving n Γ Ξ (𝕊 s t) -> proving n Γ Ξ (𝕊 s u) ->
    proving n Γ Ξ (𝕊 𝔹ₛ v) -> proving n Γ Ξ (𝕊 s (rec𝔹ₛ t u v))
| pr_sort_nil : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                       {s : st},
    wt_ctx Γ Ξ -> proving n Γ Ξ (𝕊 (𝕃ₛ s) []ₛ)
| pr_sort_cons : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                        {t u : tm n} {s : st},
    proving n Γ Ξ (𝕊 s t) -> proving n Γ Ξ (𝕊 (𝕃ₛ s) u) ->
    proving n Γ Ξ (𝕊 (𝕃ₛ s) (t ::ₛ u))
| pr_sort_recL : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                        {t u v : tm n} {s : st} (s' : st),
    proving n Γ Ξ (𝕊 s t) -> proving n Γ Ξ (𝕊 (s' →ₛ 𝕃ₛ s' →ₛ s →ₛ s) u) ->
    proving n Γ Ξ (𝕊 (𝕃ₛ s') v) -> proving n Γ Ξ (𝕊 s (rec𝕃ₛ t u v))
| pr_sort_lam : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                       {t : tm (S n)} {s s' : st},
    proving (S n) (s .: Γ) ((𝕊 s ⟦ var_zero ⟧ₛ) :: map (ren_tm shift) Ξ) (𝕊 s' t) ->
    proving n Γ Ξ (𝕊 (s →ₛ s') (ƛ t))
| pr_sort_app : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                       {t u : tm n} (s : st) {s' : st},
    proving n Γ Ξ (𝕊 (s →ₛ s') t) -> proving n Γ Ξ (𝕊 s u) ->
    proving n Γ Ξ (𝕊 s' (t @ₛ u))
| pr_sort_pair : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                        {t u : tm n} {s s' : st},
    proving n Γ Ξ (𝕊 s t) -> proving n Γ Ξ (𝕊 s' u) ->
    proving n Γ Ξ (𝕊 (s ×ₛ s') ⟨ t , u ⟩ₛ)
| pr_sort_proj1 : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                         {t : tm n} {s : st} (s' : st),
    proving n Γ Ξ (𝕊 (s ×ₛ s') t) -> proving n Γ Ξ (𝕊 s (π¹ₛ t))
| pr_sort_proj2 : forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
                         {t : tm n} (s : st) {s' : st},
    proving n Γ Ξ (𝕊 (s ×ₛ s') t) -> proving n Γ Ξ (𝕊 s' (π²ₛ t)).

Notation "Γ ∣ Ξ ⊢| n | φ" := (proving n Γ Ξ φ) (at level 87).

Lemma wt_proving :
  forall (n : nat) (Γ : HOL_ctx n) (Ξ : proof_ctx n) (φ : tm n),
    Γ ∣ Ξ ⊢| n | φ -> wt_ctx Γ Ξ /\ (Γ ⊢⟨ n ⟩ φ ~: ℙₛ).
Proof.
  intros. induction H; try (split; [assumption | ]);
    try (destruct IHproving as [HΞ IH]; split; [try assumption | try assumption]);
    try (destruct IHproving1 as [HΞ IH1]; destruct IHproving2 as [_ IH2];
         try destruct IHproving3 as [_ IH3];
         split; [try assumption| try assumption]);
    try (constructor; constructor; fail).
  - apply (In_forall _ Ξ φ H H0).
  - dependent destruction HΞ. apply HΞ.
  - constructor; [| assumption]. inversion HΞ.
    apply H2.
  - dependent destruction IH1. apply IH1_2.
  - eapply (map_forall_rev _
              (fun x => s .: Γ ⊢⟨ S n ⟩ x ~: ℙₛ)
              (ren_tm shift)).
    intros a Ha.
    eapply typ_weaken_rev.
    apply Ha. apply HΞ.
  - apply typ_forall. apply IH.
  - apply (comp_typ_vec _ _ _ _ (s .: Γ)).
    asimpl. intro f; case f eqn:e.
    asimpl. apply typ_var. asimpl. apply H0.
    dependent destruction IH. apply IH.
  - constructor. apply (typ_app ℕₛ).
    apply typ_weaken. dependent destruction IH1.
    dependent destruction IH1_2. apply IH1_1.
    constructor.
  - constructor. apply (typ_app 𝔹ₛ).
    apply typ_weaken. dependent destruction IH2.
    dependent destruction IH2_2. apply IH2_1.
    constructor.
  - constructor. apply (typ_app (𝕃ₛ s)).
    apply typ_weaken. dependent destruction IH2.
    dependent destruction IH2.
    dependent destruction IH2.
    dependent destruction IH2_2.
    dependent destruction IH2_2_2.
    apply (typ_weaken_rev _ _ _ _ s0).
    apply (typ_weaken_rev _ _ _ _ (𝕃ₛ s0)).
    asimpl. apply IH2_1. constructor.
  - constructor. dependent destruction IH.
    constructor. apply IH.
  - constructor. dependent destruction IH1.
    dependent destruction IH2.
    dependent destruction IH3.
    constructor; assumption.
  - dependent destruction IH1.
    dependent destruction IH2.
    dependent destruction IH3.
    constructor. constructor; assumption.
  - dependent destruction IH1.
    dependent destruction IH2.
    constructor. constructor; assumption.
  - dependent destruction IH1.
    dependent destruction IH2.
    dependent destruction IH3.
    constructor. apply (typ_recL s'); assumption.
  - dependent destruction HΞ.
    eapply (map_forall_rev _
              (fun x => s .: Γ ⊢⟨ S n ⟩ x ~: ℙₛ)
              (ren_tm shift)).
    intros a Ha.
    eapply typ_weaken_rev.
    apply Ha.
    apply HΞ.
  - constructor. constructor.
    dependent destruction IH.
    apply IH.
  - constructor.
    dependent destruction IH1.
    dependent destruction IH2.
    apply (typ_app s); assumption.
  - constructor.
    dependent destruction IH1.
    dependent destruction IH2.
    constructor; assumption.
  - constructor. dependent destruction IH.
    apply (typ_proj1 s'). assumption.
  - constructor. dependent destruction IH.
    apply (typ_proj2 s). assumption.
Qed.

Lemma ren_proof :
  forall (n m : nat) (Γ : HOL_ctx n) (Δ : HOL_ctx m)
         (Ξ : proof_ctx n) (φ : tm n) (ξ : fin n -> fin m),
    (forall f, (ξ >> Δ) f = Γ f) ->
    Γ ∣ Ξ ⊢| n | φ -> Δ ∣ map (ren_tm ξ) Ξ ⊢| m | ren_tm ξ φ.
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
  - apply pr_sort_Z.
    apply (map_forall (fun x => Γ ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Δ ⊢⟨ m ⟩ x ~: ℙₛ)
             (ren_tm ξ)).
    intros a Ha.
    eapply typ_ren.
    apply H0. apply Ha.
    apply H.
  - apply pr_sort_S.
    apply IHproving. apply H.
  - apply pr_sort_recN.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
    apply IHproving3; assumption.
  - apply pr_sort_T.
    apply (map_forall (fun x => Γ ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Δ ⊢⟨ m ⟩ x ~: ℙₛ)
             (ren_tm ξ)).
    intros a Ha.
    eapply typ_ren.
    apply H0. apply Ha.
    apply H.
  - apply pr_sort_F.
    apply (map_forall (fun x => Γ ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Δ ⊢⟨ m ⟩ x ~: ℙₛ)
             (ren_tm ξ)).
    intros a Ha.
    eapply typ_ren.
    apply H0. apply Ha.
    apply H.
  - apply pr_sort_recB.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
    apply IHproving3; assumption.
  - apply pr_sort_nil.
    apply (map_forall (fun x => Γ ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Δ ⊢⟨ m ⟩ x ~: ℙₛ)
             (ren_tm ξ)).
    intros a Ha.
    eapply typ_ren.
    apply H0. apply Ha.
    apply H.
  - apply pr_sort_cons.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
  - apply (pr_sort_recL s').
    apply IHproving1; assumption.
    apply IHproving2; assumption.
    apply IHproving3; assumption.
  - apply pr_sort_lam.
    specialize (IHproving (S m) (s .: Δ) (upRen_tm_tm ξ)).
    asimpl in IHproving.
    assert
      (forall f, ((var_zero .: ξ >> shift) >> (s .: Δ)) f = (s .: Γ) f).
    intro f; case f eqn : e. asimpl.
    unfold ">>"; simpl. apply H. reflexivity.
    specialize (IHproving H1); clear H1.
    asimpl in IHproving. simpl in IHproving.
    rewrite map_map in IHproving.
    asimpl in IHproving.
    rewrite map_map. asimpl.
    assert (forall f,
               (ren_tm shift >> ren_tm (var_zero .: ξ >> shift)) f =
                 (ren_tm ξ >> ren_tm shift) f).
    intro f; asimpl. reflexivity.
    rewrite (map_ext _ _ H1) in IHproving.
    apply IHproving.
  - apply (pr_sort_app s).
    apply IHproving1; assumption.
    apply IHproving2; assumption.
  - apply pr_sort_pair.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
  - apply (pr_sort_proj1 s').
    apply IHproving; assumption.
  - apply (pr_sort_proj2 s).
    apply IHproving; assumption.
Qed.

Lemma subst_proof :
  forall (n m : nat) (v : HOL_vec n m) (Γ : HOL_ctx m) (Δ : HOL_ctx n)
         (Ξ : proof_ctx n) (φ : tm n),
    Γ ⊢⟨ m ⟩ v ~:⟨ n , Δ ⟩ -> Δ ∣ Ξ ⊢| n | φ ->
    Γ ∣ map (subst_tm v) Ξ ⊢| m | φ [ v ].
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
  - apply pr_sort_Z.
    apply (map_forall
             (fun x => Γ  ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Γ0 ⊢⟨ m ⟩ x ~: ℙₛ)
             (subst_tm v)).
    intros a Ha.
    apply (comp_typ_vec _ _ _ _ _ _ _ Hv Ha).
    apply H.
  - asimpl. apply pr_sort_S.
    apply IHHφ.
    apply Hv.
  - asimpl. apply pr_sort_recN.
    apply IHHφ1; assumption.
    apply IHHφ2; assumption.
    apply IHHφ3; assumption.
  - apply pr_sort_T.
    apply (map_forall
             (fun x => Γ  ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Γ0 ⊢⟨ m ⟩ x ~: ℙₛ)
             (subst_tm v)).
    intros a Ha.
    apply (comp_typ_vec _ _ _ _ _ _ _ Hv Ha).
    apply H.
  - apply pr_sort_F.
    apply (map_forall
             (fun x => Γ  ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Γ0 ⊢⟨ m ⟩ x ~: ℙₛ)
             (subst_tm v)).
    intros a Ha.
    apply (comp_typ_vec _ _ _ _ _ _ _ Hv Ha).
    apply H.
  - asimpl. apply pr_sort_recB.
    apply IHHφ1; assumption.
    apply IHHφ2; assumption.
    apply IHHφ3; assumption.
  - apply pr_sort_nil.
    apply (map_forall
             (fun x => Γ  ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => Γ0 ⊢⟨ m ⟩ x ~: ℙₛ)
             (subst_tm v)).
    intros a Ha.
    apply (comp_typ_vec _ _ _ _ _ _ _ Hv Ha).
    apply H.
  - asimpl. apply pr_sort_cons.
    apply IHHφ1; assumption.
    apply IHHφ2; assumption.
  - asimpl. apply (pr_sort_recL s').
    apply IHHφ1; assumption.
    apply IHHφ2; assumption.
    apply IHHφ3; assumption.
  - asimpl. apply pr_sort_lam.
    specialize (IHHφ (S m) ((S m)__tm var_zero .: v >> ren_tm shift)
                  (s .: Γ0)).
    assert (s .: Γ0 ⊢⟨ S m ⟩ (S m) __tm var_zero .: v >> ren_tm shift ~:⟨ S n, s .: Γ ⟩).
    intro f. case f eqn : e.
    asimpl. unfold ">>". apply typ_weaken. apply Hv.
    asimpl. constructor.
    specialize (IHHφ H); clear H.
    asimpl in IHHφ.
    rewrite map_map. asimpl.
    simpl in IHHφ. rewrite map_map in IHHφ.
    asimpl in IHHφ.
    assert
      (forall f,
          (ren_tm shift >> subst_tm
             ((S m)__tm var_zero .: v >> ren_tm shift)) f =
            (subst_tm v >> ren_tm shift) f).
    intro f; asimpl. reflexivity.
    rewrite (map_ext _ _ H) in IHHφ.
    apply IHHφ.
  - asimpl. apply (pr_sort_app s).
    apply IHHφ1; assumption.
    apply IHHφ2; assumption.
  - asimpl. apply pr_sort_pair.
    apply IHHφ1; assumption.
    apply IHHφ2; assumption.
  - asimpl. apply (pr_sort_proj1 s').
    apply IHHφ; assumption.
  - asimpl. apply (pr_sort_proj2 s).
    apply IHHφ; assumption.
Qed.

Lemma weaken_proof :
  forall (n : nat) (Γ : HOL_ctx n)
         (Ξ Θ : proof_ctx n) (φ : tm n),
    Γ ∣ Ξ ⊢| n | φ -> incl Ξ Θ ->
    wt_ctx Γ Θ -> Γ ∣ Θ ⊢| n | φ.
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
  - apply pr_sort_Z; assumption.
  - apply pr_sort_S. apply IHproving; assumption.
  - apply pr_sort_recN.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
    apply IHproving3; assumption.
  - apply pr_sort_T; assumption.
  - apply pr_sort_F; assumption.
  - apply pr_sort_recB.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
    apply IHproving3; assumption.
  - apply pr_sort_nil; assumption.
  - apply pr_sort_cons.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
  - apply (pr_sort_recL s').
    apply IHproving1; assumption.
    apply IHproving2; assumption.
    apply IHproving3; assumption.
  - apply pr_sort_lam. apply IHproving.
    apply incl_cons.
    left; reflexivity.
    apply incl_tl.
    apply incl_map. apply H0.
    constructor.
    constructor. constructor.
    apply (map_forall
             (fun x => Γ  ⊢⟨ n ⟩ x ~: ℙₛ)
             (fun x => s .: Γ ⊢⟨ S n ⟩ x ~: ℙₛ)
             (ren_tm shift)).
    intros a Ha. apply typ_weaken.
    apply Ha.
    apply H1.
  - apply (pr_sort_app s).
    apply IHproving1; assumption.
    apply IHproving2; assumption.
  - apply pr_sort_pair.
    apply IHproving1; assumption.
    apply IHproving2; assumption.
  - apply (pr_sort_proj1 s').
    apply IHproving; assumption.
  - apply (pr_sort_proj2 s).
    apply IHproving; assumption.
Qed.

Lemma weaken_proof_1 :
  forall (n : nat) (Γ : HOL_ctx n)
         (Ξ : proof_ctx n) (φ ψ : tm n),
    Γ ∣ Ξ ⊢| n | φ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ ->
    Γ ∣ ψ :: Ξ ⊢| n | φ.
Proof.
  intros.
  apply (weaken_proof n Γ Ξ (ψ :: Ξ)).
  apply H. intros x xΞ; simpl; right; apply xΞ.
  constructor. apply H0.
  apply (wt_proving n Γ Ξ φ H).
Qed.
