Require Import CRM.HOL.Base.
Require Import CRM.HOL.unscoped.
Import CombineNotations SubstNotations.

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Import ListNotations.

(** Infinitary typing :
The relation ∞⊢ uses an infinitary context, because it works better with
regard to the autosubst functions. *)

Definition typ_env : Type := nat -> st.

Reserved Notation "ρ ∞⊢ t ~: s" (at level 87).

Inductive inf_typing : typ_env -> tm -> st -> Prop :=
| typ_var : forall {n : nat} {ρ : typ_env}, ρ ∞⊢ ⟦ n ⟧ₛ ~: ρ n
| typ_lam : forall {t : tm} {s s' : st} {ρ : typ_env},
    s .: ρ ∞⊢ t ~: s' -> ρ ∞⊢ ƛ t ~: s →ₛ s'
| typ_app : forall {t u : tm} {s s' : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s →ₛ s' -> ρ ∞⊢ u ~: s -> ρ ∞⊢ t @ₛ u ~: s'
| typ_z : forall {ρ : typ_env}, ρ ∞⊢ Zₛ ~: ℕₛ
| typ_s : forall {t : tm} {ρ : typ_env},
    ρ ∞⊢ t ~: ℕₛ -> ρ ∞⊢ Sₛ t ~: ℕₛ
| typ_recN : forall {t u v : tm} {s : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s -> ρ ∞⊢ u ~: s →ₛ ℕₛ →ₛ s -> ρ ∞⊢ v ~: ℕₛ ->
    ρ ∞⊢ recℕₛ t u v ~: s
| typ_tt : forall {ρ : typ_env}, ρ ∞⊢ ttₛ ~: 𝔹ₛ
| typ_ff : forall {ρ : typ_env}, ρ ∞⊢ ffₛ ~: 𝔹ₛ
| typ_recB : forall {t u v : tm} {s : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s -> ρ ∞⊢ u ~: s -> ρ ∞⊢ v ~: 𝔹ₛ ->
    ρ ∞⊢ rec𝔹ₛ t u v ~: s
| typ_nil : forall {s : st} {ρ : typ_env}, ρ ∞⊢ []ₛ ~: 𝕃ₛ s
| typ_cons : forall {t u : tm} {s : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s -> ρ ∞⊢ u ~: 𝕃ₛ s -> ρ ∞⊢ t ::ₛ u ~: 𝕃ₛ s
| typ_recL : forall {t u v : tm} {s s' : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s -> ρ ∞⊢ u ~: s →ₛ s' →ₛ 𝕃ₛ s' →ₛ s -> ρ ∞⊢ v ~: 𝕃ₛ s' ->
    ρ ∞⊢ rec𝕃ₛ t u v ~: s
| typ_pair : forall {t u : tm} {s s' : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s -> ρ ∞⊢ u ~: s' -> ρ ∞⊢ ⟨ t , u ⟩ₛ ~: s ×ₛ s'
| typ_proj1 : forall {t : tm} {s s' : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s ×ₛ s' -> ρ ∞⊢ π¹ₛ t ~: s
| typ_proj2 : forall {t : tm} {s s' : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s ×ₛ s' -> ρ ∞⊢ π²ₛ t ~: s'
| typ_imp : forall {φ ψ : tm} {ρ : typ_env},
    ρ ∞⊢ φ ~: ℙₛ -> ρ ∞⊢ ψ ~: ℙₛ -> ρ ∞⊢ φ ⇒ₛ ψ ~: ℙₛ
| typ_forall : forall {φ : tm} {s : st} {ρ : typ_env},
    s .: ρ ∞⊢ φ ~: ℙₛ -> ρ ∞⊢ ∀ₛ φ ~: ℙₛ
| typ_sort : forall {t : tm} {s : st} {ρ : typ_env},
    ρ ∞⊢ t ~: s -> ρ ∞⊢ 𝕊 t ~: ℙₛ
where "ρ ∞⊢ t ~: s" := (inf_typing ρ t s).

Notation "0⊢ t ~: s" := (inf_typing (fun _ => ℕₛ) t s) (at level 87).

Proposition id_typed : forall (s : st), 0⊢ ƛ ⟦ 0 ⟧ₛ ~: s →ₛ s.
Proof.
  intro. repeat constructor.
Qed.

Fixpoint vl (t : tm) : nat :=
  match t with
  | n __tm => S n
  | ƛ t => pred (vl t)
  | t @ₛ u => max (vl t) (vl u)
  | Zₛ => 0
  | Sₛ t => vl t
  | recℕₛ t u v => max (vl t) (max (vl u) (vl v))
  | ttₛ => 0
  | ffₛ => 0
  | rec𝔹ₛ t u v => max (vl t) (max (vl u) (vl v))
  | []ₛ => 0
  | t ::ₛ u => max (vl t) (vl u)
  | rec𝕃ₛ t u v => max (vl t) (max (vl u) (vl v))
  | ⟨ t , u ⟩ₛ => max (vl t) (vl u)
  | π¹ₛ t => vl t
  | π²ₛ t => vl t
  | φ ⇒ₛ ψ => max (vl φ) (vl ψ)
  | ∀ₛ φ => pred (vl φ)
  | 𝕊 t => vl t
     end.

Lemma inf_typ_ext_vl : forall (ρ ρ' : typ_env) (m : nat),
    (forall n, n < m -> ρ n = ρ' n) -> forall (t : tm) (s : st),
      vl t <= m -> ρ ∞⊢ t ~: s -> ρ' ∞⊢ t ~: s.
Proof.
  intros ρ ρ' m H t; revert ρ ρ' m H; induction t;
    intros ρ ρ' m H s tm H0; inversion H0; subst;
    try (specialize (IHt1 _ _ _ H _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _) tm) H4);
         specialize (IHt2 _ _ _ H _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _) tm) H6));
    try (specialize (IHt1 _ _ _ H _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _) tm) H5);
         specialize (IHt2 _ _ _ H _
                       (Nat.le_trans _ _ _ (Nat.le_trans _ _ _
                                              (Nat.le_max_l _ _)
                                              (Nat.le_max_r _ _))
                          tm) H7);
         specialize (IHt3 _ _ _ H _
                       (Nat.le_trans _ _ _ (Nat.le_trans _ _ _
                                              (Nat.le_max_r _ _)
                                              (Nat.le_max_r _ _))
                          tm) H8)).
  - rewrite H. constructor. apply tm.
  - constructor.
    assert (forall n, n < S m -> (s0 .: ρ) n = (s0 .: ρ') n).
    intro n; case n. reflexivity. simpl.
    intro p. intro SpSm. apply H. rewrite Nat.succ_lt_mono. apply SpSm.
    apply (IHt (s0 .: ρ) _ (S m)).
    apply H1. simpl in tm. apply Nat.le_pred_le_succ. apply tm.
    apply H3.
  - exact (typ_app IHt1 IHt2).
  - exact typ_z.
  - exact (typ_s (IHt _ _ _ H _ tm H3)).
  - exact (typ_recN IHt1 IHt2 IHt3).
  - exact typ_tt.
  - exact typ_ff.
  - exact (typ_recB IHt1 IHt2 IHt3).
  - exact typ_nil.
  - exact (typ_cons IHt1 IHt2).
  - exact (typ_recL IHt1 IHt2 IHt3).
  - exact (typ_pair IHt1 IHt2).
  - exact (typ_proj1 (IHt _ _ _ H _ tm H3)).
  - exact (typ_proj2 (IHt _ _ _ H _ tm H3)).
  - exact (typ_imp IHt1 IHt2).
  - apply (@typ_forall _ s0).
    assert (forall n, n < S m -> (s0 .: ρ) n = (s0 .: ρ') n).
    intro n; case n. reflexivity. simpl.
    intro p. intro SpSm. apply H. rewrite Nat.succ_lt_mono. apply SpSm.
    apply (IHt (s0 .: ρ) _ (S m)).
    apply H1. simpl in tm. apply Nat.le_pred_le_succ. apply tm.
    apply H3.
  - apply (@typ_sort _ s0). apply (IHt _ _ _ H _ tm H3).
Qed.

Lemma inf_typ_ext : forall (ρ ρ' : typ_env),
    (forall n, ρ n = ρ' n) -> forall (t : tm) (s : st),
      ρ ∞⊢ t ~: s -> ρ' ∞⊢ t ~: s.
Proof.
  intros. apply (inf_typ_ext_vl ρ _ (vl t)). intros n H'; apply H.
  apply Nat.le_refl. apply H0.
Qed.

Definition well_typed_env (sigma_tm : nat -> tm) (ρ ρ' : typ_env) : Prop :=
  forall n : nat, ρ ∞⊢ sigma_tm n ~: ρ' n.

Lemma ren_typ_env :
  forall (t : tm) (ρ ρ' : typ_env) (xi_tm : nat -> nat) (s : st),
    (forall n, (xi_tm >> ρ) n = ρ' n) ->
    ρ' ∞⊢ t ~: s -> ρ ∞⊢ ren_tm xi_tm t ~: s.
Proof.
  intro t; induction t; intros; inversion H0; subst; asimpl.
  - assert ((xi_tm >> ρ) n = ρ (xi_tm n)).
    asimpl. reflexivity.
    rewrite <- H. rewrite H1. apply typ_var.
  - apply typ_lam.
    specialize (IHt (s0 .: ρ) (s0 .: ρ') (0 .: xi_tm >> S) s').
    asimpl in IHt. apply IHt.
    intro n. case n eqn : e. simpl. reflexivity.
    simpl. asimpl. rewrite <- H. reflexivity.
    apply H3.
  - specialize (IHt1 _ _ _ _ H H4); specialize (IHt2 _ _ _ _ H H6).
    apply (typ_app IHt1 IHt2).
  - apply typ_z.
  - constructor. apply (IHt _ _ _ _ H H3).
  - specialize (IHt1 _ _ _ _ H H5); specialize (IHt2 _ _ _ _ H H7);
      specialize (IHt3 _ _ _ _ H H8).
    apply (typ_recN IHt1 IHt2 IHt3).
  - constructor.
  - constructor.
  - specialize (IHt1 _ _ _ _ H H5); specialize (IHt2 _ _ _ _ H H7);
      specialize (IHt3 _ _ _ _ H H8).
    apply (typ_recB IHt1 IHt2 IHt3).
  - constructor.
  - specialize (IHt1 _ _ _ _ H H4); specialize (IHt2 _ _ _ _ H H6).
    apply (typ_cons IHt1 IHt2).
  - specialize (IHt1 _ _ _ _ H H5); specialize (IHt2 _ _ _ _ H H7);
      specialize (IHt3 _ _ _ _ H H8).
    apply (typ_recL IHt1 IHt2 IHt3).
  - constructor. apply (IHt1 _ _ _ _ H H4).
    apply (IHt2 _ _ _ _ H H6).
  - apply (typ_proj1 (IHt _ _ _ _ H H3)).
  - apply (typ_proj2 (IHt _ _ _ _ H H3)).
  - specialize (IHt1 _ _ _ _ H H4); specialize (IHt2 _ _ _ _ H H6).
    apply (typ_imp IHt1 IHt2).
  - apply (@typ_forall _ s0 _).
    specialize (IHt (s0 .: ρ) (s0 .: ρ') (0 .: xi_tm >> S) ℙₛ).
    asimpl in IHt. apply IHt.
    intro n. case n eqn : e. simpl. reflexivity.
    simpl. asimpl. rewrite <- H. reflexivity.
    apply H3.
  - specialize (IHt _ _ _ _ H H3). apply (typ_sort IHt).
Qed.

Lemma comp_typ_env :
  forall (sigma_tm : nat -> tm) (ρ ρ' : typ_env) (t : tm) (s : st),
    well_typed_env sigma_tm ρ ρ' -> ρ' ∞⊢ t ~: s ->
    ρ ∞⊢ t [ sigma_tm ] ~: s.
Proof.
  intros sigma_tm ρ ρ' t; revert sigma_tm ρ ρ'; induction t; intros;
    asimpl; try (inversion H0; subst); try constructor;
    try apply (IHt1 _ _ _ _ H H5); try apply (IHt2 _ _ _ _ H H7);
    try apply (IHt3 _ _ _ _ H H8).
  - apply H.
  - specialize (IHt (0 __tm .: sigma_tm >> ren_tm shift) (s0 .: ρ) (s0 .: ρ')).
    apply IHt.
    -- clear IHt H0 H3. intro n; case n eqn : e; subst.
       ++ simpl. constructor.
       ++ simpl. specialize (H n0).
          unfold ">>". apply (ren_typ_env (sigma_tm n0) (s0 .: ρ) ρ shift (ρ' n0)).
          asimpl. reflexivity. apply H.
    -- apply H3.
  - specialize (IHt1 _ _ _ _ H H4).
    specialize (IHt2 _ _ _ _ H H6). apply (typ_app IHt1 IHt2).
  - specialize (IHt _ _ _ _ H H3). apply IHt.
  - specialize (IHt1 _ _ _ _ H H4). apply IHt1.
  - specialize (IHt2 _ _ _ _ H H6). apply IHt2.
  - specialize (IHt1 _ _ _ _ H H5) ; specialize (IHt2 _ _ _ _ H H7);
      specialize (IHt3 _ _ _ _ H H8). apply (typ_recL IHt1 IHt2 IHt3).
  - specialize (IHt1 _ _ _ _ H H4). apply IHt1.
  - specialize (IHt2 _ _ _ _ H H6). apply IHt2.
  - specialize (IHt _ _ _ _ H H3). apply (typ_proj1 IHt).
  - specialize (IHt _ _ _ _ H H3). apply (typ_proj2 IHt).
  - apply (IHt1 _ _ _ _ H H4).
  - apply (IHt2 _ _ _ _ H H6).
  - apply (@typ_forall _ s0).
    specialize (IHt (0 __tm .: sigma_tm >> ren_tm shift) (s0 .: ρ) (s0 .: ρ')).
    apply IHt.
    -- clear IHt H0 H3. intro n; case n eqn : e; subst.
       ++ simpl. constructor.
       ++ simpl. specialize (H n0).
          unfold ">>". apply (ren_typ_env (sigma_tm n0) (s0 .: ρ) ρ shift (ρ' n0)).
          asimpl. reflexivity. apply H.
    -- apply H3.
  - specialize (IHt _ _ _ _ H H3). apply (typ_sort IHt).
Qed.

(** Typing relation
The typing relation uses a finitary context. It is the usual typing system one
expects. *)

Definition HOL_ctx : Type := list st.

Inductive bind : nat -> st -> HOL_ctx -> Prop :=
| bind_z : forall {s : st} {Γ : HOL_ctx}, bind 0 s (s :: Γ)
| bind_s : forall {n : nat} {s s' : st} {Γ : HOL_ctx},
    bind n s Γ -> bind (S n) s (s' :: Γ).

Notation "⟪ n → s ⟫ ∈ˢ Γ" := (bind n s Γ) (at level 85).

Reserved Notation "Γ ⊢ t ~: s" (at level 87).

Inductive HOL_typing : HOL_ctx -> tm -> st -> Prop :=
| HOL_typ_var : forall {n : nat} {s : st} {Γ : HOL_ctx},
    ⟪ n → s ⟫ ∈ˢ Γ -> Γ ⊢ ⟦ n ⟧ₛ ~: s
| HOL_typ_lam : forall {t : tm} {s s' : st} {Γ : HOL_ctx},
    s :: Γ ⊢ t ~: s' -> Γ ⊢ ƛ t ~: s →ₛ s'
| HOL_typ_app : forall {t u : tm} {s s' : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s →ₛ s' -> Γ ⊢ u ~: s -> Γ ⊢ (app_tm t u) ~: s'
| HOL_typ_z : forall {Γ : HOL_ctx}, Γ ⊢ Zₛ ~: ℕₛ
| HOL_typ_s : forall {t : tm} {Γ : HOL_ctx},
    Γ ⊢ t ~: ℕₛ -> Γ ⊢ Sₛ t ~: ℕₛ
| HOL_typ_recN : forall {t u v : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s →ₛ ℕₛ →ₛ s -> Γ ⊢ v ~: ℕₛ ->
    Γ ⊢ recℕₛ t u v ~: s
| HOL_typ_tt : forall {Γ : HOL_ctx}, Γ ⊢ ttₛ ~: 𝔹ₛ
| HOL_typ_ff : forall {Γ : HOL_ctx}, Γ ⊢ ffₛ ~: 𝔹ₛ
| HOL_typ_recB : forall {t u v : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s -> Γ ⊢ v ~: 𝔹ₛ ->
    Γ ⊢ rec𝔹ₛ t u v ~: s
| HOL_typ_nil : forall {s : st} {Γ : HOL_ctx}, Γ ⊢ []ₛ ~: 𝕃ₛ s
| HOL_typ_cons : forall {t u : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: 𝕃ₛ s -> Γ ⊢ t ::ₛ u ~: 𝕃ₛ s
| HOL_typ_recL : forall {t u v : tm} {s s' : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s →ₛ s' →ₛ 𝕃ₛ s' →ₛ s -> Γ ⊢ v ~: 𝕃ₛ s' ->
    Γ ⊢ rec𝕃ₛ t u v ~: s
| HOL_typ_pair : forall {t u : tm} {s s' : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ u ~: s' -> Γ ⊢ ⟨ t , u ⟩ₛ ~: s ×ₛ s'
| HOL_typ_proj1 : forall {t : tm} {s s' : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s ×ₛ s' -> Γ ⊢ π¹ₛ t ~: s
| HOL_typ_proj2 : forall {t : tm} {s s' : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s ×ₛ s' -> Γ ⊢ π²ₛ t ~: s'
| HOL_typ_imp : forall {φ ψ : tm} {Γ : HOL_ctx},
    Γ ⊢ φ ~: ℙₛ -> Γ ⊢ ψ ~: ℙₛ -> Γ ⊢ φ ⇒ₛ ψ ~: ℙₛ
| HOL_typ_forall : forall {φ : tm} {s : st} {Γ : HOL_ctx},
    s :: Γ ⊢ φ ~: ℙₛ -> Γ ⊢ ∀ₛ φ ~: ℙₛ
| HOL_typ_sort : forall {t : tm} {s : st} {Γ : HOL_ctx},
    Γ ⊢ t ~: s -> Γ ⊢ 𝕊 t ~: ℙₛ
where "Γ ⊢ t ~: s" := (HOL_typing Γ t s).

Fixpoint env_app_ctx (ρ : typ_env) (Γ : HOL_ctx) : typ_env :=
  match Γ with
  | [] => ρ
  | s :: Δ => s .: env_app_ctx ρ Δ
  end.

Definition ctx_to_env (Γ : HOL_ctx) : typ_env := env_app_ctx (fun _ => ℕₛ) Γ.

Lemma ctx_bind_env : forall (ρ : typ_env) (Γ : HOL_ctx) (n : nat) (s : st),
    ⟪ n → s ⟫ ∈ˢ Γ -> env_app_ctx ρ Γ n = s.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. apply IHbind.
Qed.

Lemma ctx_to_env_scons : forall (ρ : typ_env) (Γ : HOL_ctx) (s : st),
  forall n, (s .: env_app_ctx ρ Γ) n = (env_app_ctx ρ (s :: Γ)) n.
Proof.
  intros. case n eqn : e; subst; reflexivity.
Qed.

Lemma finite_to_infinite : forall (Γ : HOL_ctx) (s : st) (t : tm),
    Γ ⊢ t ~: s -> ctx_to_env Γ ∞⊢ t ~: s.
Proof.
  intros Γ s t; revert Γ s; induction t; intros; inversion H; subst;
    try (specialize (IHt1 _ _ H3); specialize (IHt2 _ _ H5));
    try (specialize (IHt1 _ _ H4); specialize (IHt2 _ _ H6);
         specialize (IHt3 _ _ H7)).
  - apply (ctx_bind_env (fun _ => ℕₛ)) in H2. rewrite <- H2. apply typ_var.
  - constructor.
    specialize (IHt (s0 :: Γ) s' H2).
    apply (inf_typ_ext (ctx_to_env (s0 :: Γ)) (s0 .: ctx_to_env Γ)) in IHt.
    apply IHt. apply ctx_to_env_scons.
  - apply (typ_app IHt1 IHt2).
  - constructor.
  - constructor. apply IHt. apply H2.
  - apply (typ_recN IHt1 IHt2 IHt3).
  - constructor.
  - constructor.
  - apply (typ_recB IHt1 IHt2 IHt3).
  - constructor.
  - apply (typ_cons IHt1 IHt2).
  - apply (typ_recL IHt1 IHt2 IHt3).
  - apply (typ_pair IHt1 IHt2).
  - apply (typ_proj1 (IHt _ _ H2)).
  - apply (typ_proj2 (IHt _ _ H2)).
  - apply (typ_imp IHt1 IHt2).
  - apply (@typ_forall _ s0).
    specialize (IHt (s0 :: Γ) ℙₛ H2).
    apply (inf_typ_ext (ctx_to_env (s0 :: Γ)) (s0 .: ctx_to_env Γ)) in IHt.
    apply IHt. apply ctx_to_env_scons.
  - apply (@typ_sort _ s0). apply IHt. apply H2.
Qed.

Lemma bind_vl : forall (Γ : HOL_ctx) (s : st) (n : nat),
    ⟪ n → s ⟫ ∈ˢ Γ -> n < length Γ.
Proof.
  intros; induction H.
  simpl. apply Nat.lt_0_succ.
  simpl. rewrite <- Nat.succ_lt_mono. apply IHbind.
Qed.
     
Lemma typ_vl : forall (Γ : HOL_ctx) (s : st) (t : tm),
    Γ ⊢ t ~: s -> vl t <= length Γ.
Proof.
  intros; induction H; try (apply Nat.le_0_l); try (apply IHHOL_typing);
    try (apply (Nat.max_lub _ _ _ IHHOL_typing1
                  (Nat.max_lub _ _ _ IHHOL_typing2 IHHOL_typing3)));
    try (apply (Nat.max_lub _ _ _ IHHOL_typing1 IHHOL_typing2)).
  - apply bind_vl in H. simpl. apply H.
  - simpl. simpl in IHHOL_typing.
    case (vl t) eqn : e.
    + simpl. apply Nat.le_0_l.
    + simpl. rewrite Nat.succ_le_mono. apply IHHOL_typing.
  - simpl. simpl in IHHOL_typing.
    case (vl φ) eqn : e.
    + simpl. apply Nat.le_0_l.
    + simpl. rewrite Nat.succ_le_mono. apply IHHOL_typing.
Qed.

Fixpoint restr_param (ρ : typ_env) (n k : nat) : HOL_ctx :=
  match k with
  | 0 => []
  | S m => ρ n :: restr_param ρ (S n) m
  end.

Definition restr (ρ : typ_env) (n : nat) : HOL_ctx := restr_param ρ 0 n.

Lemma restr_param_shift : forall (ρ : typ_env) (n k : nat),
    restr_param ρ (S n) k = restr_param (shift >> ρ) n k.
Proof.
  intros ρ n k; revert ρ n; induction k; intros.
  - simpl. reflexivity.
  - simpl. unfold ">>"; unfold shift. f_equal.
    apply IHk.
Qed.

Lemma restr_param_ext : forall (ρ ρ' : typ_env) (n k : nat),
    (forall n : nat, ρ n = ρ' n) -> restr_param ρ n k = restr_param ρ' n k.
Proof.
  intros ρ ρ' n k; revert ρ ρ' n; induction k; intros.
  reflexivity. simpl. f_equal. apply H. apply IHk. apply H.
Qed.

Fixpoint restr_rev (ρ : typ_env) (n : nat) : HOL_ctx :=
  match n with
  | 0 => []
  | S m => ρ m :: restr_rev ρ m
  end.

Lemma restr_cons_r : forall (ρ : typ_env) (n k : nat),
    restr_param ρ n (S k) = restr_param ρ n k ++ [ ρ (n + k) ].
Proof.
  intros ρ n k; revert n; induction k; intros. simpl.
  rewrite Nat.add_0_r; reflexivity.
  simpl. f_equal. specialize (IHk (S n)). simpl in IHk.
  rewrite IHk. f_equal. f_equal. f_equal.
  rewrite <- Nat.add_succ_comm. reflexivity.
Qed.
  
Lemma restr_concat : forall (ρ : typ_env) (n m k : nat),
    restr_param ρ n (m + k) = restr_param ρ n m ++ restr_param ρ (n + m) k.
Proof.
  intros; revert n m; induction k; intros.
  - simpl. rewrite app_nil_r. rewrite Nat.add_0_r. reflexivity.
  - simpl. specialize (IHk n (S m)). rewrite <- Nat.add_succ_comm.
    rewrite IHk. rewrite <- Nat.add_succ_comm. rewrite restr_cons_r.
    rewrite <- app_assoc. reflexivity.
Qed.

Theorem restr_rev_rev : forall (ρ : typ_env) (n : nat),
    restr_rev ρ n = List.rev (restr ρ n).
Proof.
  intros. induction n. reflexivity.
  unfold restr; rewrite restr_cons_r.
  unfold restr in IHn. Search (rev (_ ++ [_])).
  rewrite rev_unit. rewrite <- IHn. reflexivity.
Qed.

Theorem restr_rev_unrev : forall (ρ : typ_env) (n : nat),
    restr ρ n = List.rev (restr_rev ρ n).
Proof.
  intros. rewrite <- (rev_involutive (restr ρ n)).
  rewrite restr_rev_rev. reflexivity.
Qed.

Lemma restr_succ : forall (ρ : typ_env) (n : nat),
    restr ρ (S n) = restr ρ n ++ [ ρ n ].
Proof.
  intros. unfold restr. rewrite restr_cons_r. reflexivity.
Qed.
  
Lemma restr_scons : forall (ρ : typ_env) (s : st) (n : nat),
    restr (s .: ρ) (S n) = s :: restr ρ n.
Proof.
  intros ρ s n; revert ρ s; induction n; intros.
  - unfold restr. simpl. reflexivity.
  - unfold restr; simpl. rewrite restr_param_shift. f_equal.
Qed.

Lemma restr_append : forall (ρ : typ_env) (Γ : HOL_ctx) (n : nat),
    restr (env_app_ctx ρ Γ) (n + length Γ) = Γ ++ restr ρ n.
Proof.
  intros. induction Γ.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite <- Nat.add_succ_comm. simpl. rewrite restr_scons.
    rewrite IHΓ. reflexivity.
Qed.

Lemma bind_in_restr : forall (ρ : typ_env) (n m : nat),
    n < m -> ⟪ n → ρ n ⟫ ∈ˢ restr ρ m.
Proof.
  intros ρ n m; revert ρ n; induction m; intros.
  - inversion H.
  - case n eqn : e; unfold restr; simpl; constructor.
    rewrite restr_param_shift. unfold restr in IHm.
    assert (ρ (S n0) = (shift >> ρ) n0). reflexivity.
    rewrite H0. apply IHm. rewrite Nat.succ_lt_mono. apply H.
Qed.

Theorem infinite_to_finite : forall (ρ : typ_env) (t : tm) (s : st) (n : nat),
    vl t <= n -> ρ ∞⊢ t ~: s -> restr ρ n ⊢ t ~: s.
Proof.
  intros ρ t; revert ρ; induction t; intros; inversion H0; subst.
  - constructor. apply bind_in_restr. simpl in H. apply H.
  - constructor. simpl in H. rewrite Nat.le_pred_le_succ in H.
    specialize (IHt (s0 .: ρ) s' (S n) H H3).
    rewrite <- restr_scons. apply IHt.
  - apply (@HOL_typ_app _ _ s0).
    apply IHt1. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_l.
    apply H. apply H4.
    apply IHt2. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_r.
    apply H. apply H6.
  - apply HOL_typ_z.
  - constructor. apply IHt. apply H. apply H3.
  - constructor. apply IHt1. transitivity (vl (recℕₛ t1 t2 t3)).
    apply Nat.le_max_l. apply H. apply H5.
    apply IHt2. transitivity (vl (recℕₛ t1 t2 t3)).
    transitivity (max (vl t2) (vl t3)). apply Nat.le_max_l. apply Nat.le_max_r.
    apply H. apply H7.
    apply IHt3. transitivity (vl (recℕₛ t1 t2 t3)).
    transitivity (max (vl t2) (vl t3)). apply Nat.le_max_r. apply Nat.le_max_r.
    apply H. apply H8.
  - constructor.
  - constructor.
  - constructor. apply IHt1. transitivity (vl (recℕₛ t1 t2 t3)).
    apply Nat.le_max_l. apply H. apply H5.
    apply IHt2. transitivity (vl (recℕₛ t1 t2 t3)).
    transitivity (max (vl t2) (vl t3)). apply Nat.le_max_l. apply Nat.le_max_r.
    apply H. apply H7.
    apply IHt3. transitivity (vl (recℕₛ t1 t2 t3)).
    transitivity (max (vl t2) (vl t3)). apply Nat.le_max_r. apply Nat.le_max_r.
    apply H. apply H8.
  - constructor.
  - constructor.
    apply IHt1. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_l.
    apply H. apply H4.
    apply IHt2. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_r.
    apply H. apply H6.
  - apply (@HOL_typ_recL _ _ _ s s'). apply IHt1. transitivity (vl (recℕₛ t1 t2 t3)).
    apply Nat.le_max_l. apply H. apply H5.
    apply IHt2. transitivity (vl (recℕₛ t1 t2 t3)).
    transitivity (max (vl t2) (vl t3)). apply Nat.le_max_l. apply Nat.le_max_r.
    apply H. apply H7.
    apply IHt3. transitivity (vl (recℕₛ t1 t2 t3)).
    transitivity (max (vl t2) (vl t3)). apply Nat.le_max_r. apply Nat.le_max_r.
    apply H. apply H8.
  - constructor.
    apply IHt1. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_l.
    apply H. apply H4.
    apply IHt2. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_r.
    apply H. apply H6.
  - apply (@HOL_typ_proj1 _ s s'). apply IHt. apply H. apply H3.
  - apply (@HOL_typ_proj2 _ s0 s). apply IHt. apply H. apply H3.
  - constructor.
    apply IHt1. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_l.
    apply H. apply H4.
    apply IHt2. transitivity (max (vl t1) (vl t2)). apply Nat.le_max_r.
    apply H. apply H6.
  - apply (@HOL_typ_forall _ s0). simpl in H. rewrite Nat.le_pred_le_succ in H.
    specialize (IHt (s0 .: ρ) ℙₛ (S n) H H3).
    rewrite <- restr_scons. apply IHt.
  - apply (@HOL_typ_sort _ s0). apply IHt. apply H. apply H3.
Qed.

Theorem fin_inf_fin : forall (ρ : typ_env) (Γ : HOL_ctx),
    restr (env_app_ctx ρ Γ) (length Γ) = Γ.
Proof.
  intros; revert ρ; induction Γ; intros.
  - reflexivity.
  - unfold restr; simpl; f_equal. rewrite (restr_param_shift _ 0).
    assert (forall n, (shift >> (a .: env_app_ctx ρ Γ)) n = env_app_ctx ρ Γ n).
    intro n; case n eqn : e.
    unfold ">>"; unfold scons. simpl. reflexivity.
    unfold ">>"; unfold scons. simpl. reflexivity.
    rewrite (restr_param_ext
               (shift >> (a .: env_app_ctx ρ Γ))
               (env_app_ctx ρ Γ) 0 (length Γ) H).
    apply IHΓ.
Qed.

Theorem inf_fin_inf_param : forall (ρ ρ' : typ_env) (n k m : nat),
    m < k -> env_app_ctx ρ' (restr_param ρ n k) m = ρ (n + m).
Proof.
  intros ρ ρ' n k; revert ρ' ρ n; induction k; intros.
  - inversion H.
  - case m eqn : e; subst.
    + rewrite Nat.add_0_r. unfold ctx_to_env; simpl. reflexivity.
    + simpl.
      rewrite <- Nat.succ_lt_mono in H.
      specialize (IHk ρ' ρ (S n) n0 H).
      rewrite Nat.add_succ_comm in IHk. apply IHk.
Qed.

Theorem inf_fin_inf : forall (ρ : typ_env) (n m : nat),
    m < n -> ctx_to_env (restr ρ n) m = ρ m.
Proof.
  intros. unfold ctx_to_env ; unfold restr.
  apply inf_fin_inf_param. apply H.
Qed.
