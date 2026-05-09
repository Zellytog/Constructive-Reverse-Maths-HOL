From CRM Require Import Base Typing Reduction Theorie fintype.
Import CombineNotations SubstNotations.
From CRM Require Import Prelude.ListCRM.

Require Import PeanoNat List Program.Equality.

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

(*Section LogicLemma.*)

  Lemma proving_refl :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {t : tm n} {s : st},
      wt_ctx Γ Ξ -> Γ ⊢⟨ n ⟩ t ~: s -> Γ ∣ Ξ ⊢| n | t =⟨ s ⟩ t.
  Proof.
    intros. unfold eq_tm. apply pr_abs_f.
    apply pr_abs. apply pr_ax. constructor.
    apply (typ_app s). constructor. apply typ_weaken; apply H0.
    apply (map_forall _ _ (ren_tm shift) (fun x => typ_weaken n Γ x ℙₛ (s →ₛ ℙₛ))).
    apply H. simpl. left; reflexivity.
  Qed.

  Lemma eq_elim :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {t : tm n} {u φ : tm n} {s : st},
      Γ ∣ Ξ ⊢| n | t =⟨ s ⟩ u -> Γ ⊢⟨ n ⟩ φ ~: s →ₛ ℙₛ ->
      Γ ∣ Ξ ⊢| n | φ @ₛ t -> Γ ∣ Ξ ⊢| n | φ @ₛ u.
  Proof.
    intros.
    apply (pr_app_f φ (s →ₛ ℙₛ)) in H.
    asimpl in H.
    apply (pr_app (φ @ₛ t) H H1).
    apply H0.
  Qed.

  Lemma def_eq_to_eq :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {t u : tm n} {s : st},
      Γ ⊢⟨ n ⟩ t ~: s -> Γ ⊢⟨ n ⟩ u ~: s ->
      t =ₛ u -> wt_ctx Γ Ξ ->
      Γ ∣ Ξ ⊢| n | t =⟨ s ⟩ u.
  Proof.
    intros. apply (pr_transp (t =⟨ s ⟩ t)).
    apply proving_refl. apply H2.
    apply H. apply typ_eq.
    apply H. apply H0.
    repeat apply βeq_compat.
    apply ren_βeq.
    apply H1.
  Qed.

  Lemma pr_pair :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ ψ : tm n},
      Γ ∣ Ξ ⊢| n | φ -> Γ ∣ Ξ ⊢| n | ψ ->
      Γ ∣ Ξ ⊢| n | φ ∧ₛ ψ.
  Proof.
    intros. apply pr_abs_f.
    apply pr_abs.
    assert (ℙₛ .: Γ ⊢⟨ S n ⟩ ren_tm shift φ ~: ℙₛ) as Hφ.
    apply typ_weaken. apply (proj2 (wt_proving n Γ Ξ φ H)).
    assert (ℙₛ .: Γ ⊢⟨ S n ⟩ ren_tm shift ψ ~: ℙₛ) as Hψ.
    apply typ_weaken. apply (proj2 (wt_proving n Γ Ξ ψ H0)).
    assert (@wt_ctx (S n) (ℙₛ .: Γ) (map (ren_tm shift) Ξ)).
    eapply map_forall. intros a Ha.
    apply typ_weaken. apply Ha.
    apply (proj1 (wt_proving n Γ Ξ φ H)).
    apply (pr_app (ren_tm shift ψ)).
    apply (pr_app (ren_tm shift φ)).
    repeat constructor; try assumption.
    apply weaken_proof_1.
    eapply ren_proof. intro f; reflexivity.
    apply H.
    repeat constructor; try assumption.
    apply weaken_proof_1.
    eapply ren_proof. intro f; reflexivity.
    apply H0.
    repeat constructor; assumption.
  Qed.

  Lemma pr_proj1 :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ : tm n} (ψ : tm n),
      Γ ∣ Ξ ⊢| n | φ ∧ₛ ψ -> Γ ∣ Ξ ⊢| n | φ.
  Proof.
    intros.
    specialize (proj2 (wt_proving n Γ Ξ _ H)) as H0.
    dependent destruction H0.
    dependent destruction H0.
    dependent destruction H0_.
    rename H0_1 into Hφ.
    dependent destruction H0_2.
    rename H0_2_1 into Hψ.
    clear H0_2_2 H0_0.
    apply typ_weaken_rev in Hφ.
    apply typ_weaken_rev in Hψ.
    specialize (pr_app_f φ ℙₛ H Hφ) as H0.
    asimpl in H0.
    apply (pr_app (φ ⇒ₛ ψ ⇒ₛ φ)).
    apply H0.
    apply pr_abs. apply pr_abs. constructor.
    repeat constructor. apply Hψ.
    apply Hφ.
    apply (proj1(wt_proving n Γ Ξ _ H)).
    simpl. right; left; reflexivity.
  Qed.

  Lemma pr_proj2 :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           (φ : tm n) {ψ : tm n},
      Γ ∣ Ξ ⊢| n | φ ∧ₛ ψ -> Γ ∣ Ξ ⊢| n | ψ.
  Proof.
    intros.
    specialize (proj2 (wt_proving n Γ Ξ _ H)) as H0.
    dependent destruction H0.
    dependent destruction H0.
    dependent destruction H0_.
    rename H0_1 into Hφ.
    dependent destruction H0_2.
    rename H0_2_1 into Hψ.
    clear H0_2_2 H0_0.
    apply typ_weaken_rev in Hφ.
    apply typ_weaken_rev in Hψ.
    specialize (pr_app_f ψ ℙₛ H Hψ) as H0.
    asimpl in H0.
    apply (pr_app (φ ⇒ₛ ψ ⇒ₛ ψ)).
    apply H0.
    apply pr_abs. apply pr_abs. constructor.
    repeat constructor. apply Hψ.
    apply Hφ.
    apply (proj1(wt_proving n Γ Ξ _ H)).
    simpl. left; reflexivity.
  Qed.

  Lemma pr_coproj1 :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ : tm n} (ψ : tm n),
      Γ ∣ Ξ ⊢| n | φ -> Γ ⊢⟨ n ⟩ ψ ~: ℙₛ -> Γ ∣ Ξ ⊢| n | φ ∨ₛ ψ.
  Proof.
    intros.
    specialize (wt_proving _ _ _ _ H) as [HΞ Hφ].
    apply pr_abs_f. apply pr_abs. apply pr_abs.
    apply (pr_app (ren_tm shift φ)).
    constructor. repeat constructor.
    apply typ_weaken. apply H0.
    apply typ_weaken. apply Hφ.
    eapply map_forall.
    intros a Ha; apply typ_weaken; apply Ha.
    apply HΞ.
    right; left; reflexivity.
    apply weaken_proof_1. apply weaken_proof_1.
    eapply ren_proof.
    intro; reflexivity.
    apply H.
    repeat constructor. apply typ_weaken. apply Hφ.
    repeat constructor. apply typ_weaken. apply H0.
  Qed.

  Lemma pr_coproj2 :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           (φ : tm n) {ψ : tm n},
      Γ ⊢⟨ n ⟩ φ ~: ℙₛ -> Γ ∣ Ξ ⊢| n | ψ -> Γ ∣ Ξ ⊢| n | φ ∨ₛ ψ.
  Proof.
    intros.
    specialize (wt_proving _ _ _ _ H0) as [HΞ Hψ].
    apply pr_abs_f. apply pr_abs. apply pr_abs.
    apply (pr_app (ren_tm shift ψ)).
    constructor. repeat constructor.
    apply typ_weaken. apply Hψ.
    apply typ_weaken. apply H.
    eapply map_forall.
    intros a Ha; apply typ_weaken; apply Ha.
    apply HΞ.
    left; reflexivity.
    apply weaken_proof_1. apply weaken_proof_1.
    eapply ren_proof.
    intro; reflexivity.
    apply H0.
    repeat constructor. apply typ_weaken. apply H.
    repeat constructor. apply typ_weaken. apply Hψ.
  Qed.

  Lemma pr_cases :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ ψ χ: tm n},
      Γ ∣ Ξ ⊢| n | φ ∨ₛ ψ ->
      Γ ∣ φ :: Ξ ⊢| n | χ -> Γ ∣ ψ :: Ξ ⊢| n | χ ->
      Γ ∣ Ξ ⊢| n | χ.
  Proof.
    intros.
    apply (pr_app_f χ) in H. asimpl in H.
    apply (pr_app (ψ ⇒ₛ χ)). apply (pr_app (φ ⇒ₛ χ)).
    apply H.
    apply pr_abs. apply H0.
    apply pr_abs. apply H1.
    apply wt_proving in H0.
    exact (proj2 H0).
  Qed.

  Lemma pr_wit :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ : tm (S n)} (t : tm n) {s : st},
      s .: Γ ⊢⟨ S n ⟩ φ ~: ℙₛ ->
      Γ ⊢⟨ n ⟩ t ~: s -> Γ ∣ Ξ ⊢| n | subst_tm (t .: var_tm) φ ->
      Γ ∣ Ξ ⊢| n | ∃ₛ s φ.
  Proof.
    intros n Γ Ξ φ t s HI H H0.
    pose (φ₀ := (∀ₛ s (ren_tm shift11 φ ⇒ₛ
                         (S (S n))__tm (Some None)))).
    pose (Ξ₀ := φ₀ :: map (ren_tm shift) Ξ).
    apply pr_abs_f. apply pr_abs.
    assert (forall x, ((ren_tm shift t) .: (S n) __tm) (shift11 x) =
                        (ren_tm shift t .: shift >> var_tm) x).
    intro x; case x eqn : e; try reflexivity.
    apply (pr_app (subst_tm (shift11 >> (ren_tm shift t .: (S n)__tm)) φ)).
    rewrite (ext_tm _ _ H1).
    specialize (@pr_ax (S n) (ℙₛ .: Γ) Ξ₀ φ₀) as H2.
    assert (ℙₛ .: Γ ⊢⟨ S n ⟩ φ₀ ~: ℙₛ).
    constructor. constructor. apply typ_shift.
    apply HI. constructor.
    assert (@wt_ctx (S n) (ℙₛ .: Γ) Ξ₀).
    constructor. apply H3.
    eapply map_forall.
    intros a Ha; apply typ_weaken; apply Ha.
    apply (proj1 (wt_proving _ _ _ _ H0)).
    specialize (H2 H4).
    assert (In φ₀ Ξ₀). left; reflexivity.
    specialize (H2 H5); clear H5.
    apply (pr_app_f (ren_tm shift t)) in H2.
    asimpl in H2.
    assert (forall f,
               (shift11 >> (ren_tm shift t .: (S n) __tm)) f =
                 (ren_tm shift t .: shift >> (S n) __tm) f).
    intro f; case f eqn : e; try reflexivity.
    rewrite (ext_tm _ _ H5) in H2.
    apply H2. apply typ_weaken. apply H.
    rewrite (ext_tm _ _ H1).
    apply (ren_proof n (S n) Γ (ℙₛ .: Γ) Ξ (subst_tm (t .: var_tm) φ) shift) in H0.
    asimpl in H0.
    apply (weaken_proof_1 _ _ _ _ (∀ₛ s (ren_tm shift11 φ ⇒ₛ (S (S n)) __tm (Some None)))) in H0.
    apply H0.
    constructor. constructor.
    apply typ_shift. apply HI.
    constructor. intro; reflexivity.
  Qed.

  Lemma pr_ex_e :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ : tm (S n)} {ψ : tm n} (t : tm n) {s : st},
      Γ ∣ Ξ ⊢| n | ∃ₛ s φ ->
      s .: Γ ∣ φ :: map (ren_tm shift) Ξ ⊢| S n | ren_tm shift ψ ->
      Γ ∣ Ξ ⊢| n | ψ.
  Proof.
    intros. apply (pr_app_f ψ) in H.
    asimpl in H. unfold ">>" in H. asimpl in H.
    eapply (pr_app _ H).
    apply pr_abs_f.
    apply pr_abs.
    assert
      (subst_tm (
           shift11 >> ((S n)__tm var_zero .:
                         (ψ .: var_tm) >> ren_tm shift)) φ
       = φ).
    apply idSubst_tm.
    intros x; case x eqn : e; try reflexivity.
    rewrite H1. apply H0.
    apply (typ_weaken_rev _ _ _ _ s).
    apply (proj2 (wt_proving _ _ _ _ H0)).
  Qed.

  Lemma pr_true :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n},
      wt_ctx Γ Ξ -> Γ ∣ Ξ ⊢| n | ⊤ₛ.
  Proof.
    intros. apply pr_abs_f. apply pr_abs.
    repeat constructor.
    eapply map_forall.
    intros a Ha. apply typ_weaken. apply Ha.
    apply H.
  Qed.

  Lemma pr_false_e :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ : tm n},
      Γ ⊢⟨ n ⟩ φ ~: ℙₛ -> Γ ∣ Ξ ⊢| n | ⊥ₛ -> Γ ∣ Ξ ⊢| n | φ.
  Proof.
    intros. apply (pr_app_f φ) in H0.
    asimpl in H0. apply H0. apply H.
  Qed.

  Lemma pr_not_i :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ : tm n},
      Γ ∣ φ :: Ξ ⊢| n | ⊥ₛ -> Γ ∣ Ξ ⊢| n | ¬ₛ φ.
  Proof.
    intros. apply pr_abs. apply H.
  Qed.

  Lemma pr_not_e :
    forall {n : nat} {Γ : HOL_ctx n} {Ξ : proof_ctx n}
           {φ : tm n},
      Γ ∣ Ξ ⊢| n | φ -> Γ ∣ Ξ ⊢| n | ¬ₛ φ ->
      Γ ∣ Ξ ⊢| n | ⊥ₛ.
  Proof.
    intros. apply (pr_app φ). apply H0. apply H.
  Qed.

  
