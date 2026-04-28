Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive st : Type :=
| nat_st : st
| bool_st : st
| list_st : st -> st
| prop_st : st
| to_st : st -> st -> st
| prod_st : st -> st -> st.

Notation ℕₛ := nat_st.
Notation 𝔹ₛ := bool_st.
Notation 𝕃ₛ := list_st.
Notation ℙₛ := prop_st.
Notation "s →ₛ s'" := (to_st s s') (at level 86, right associativity).
Notation "s ×ₛ s'" := (prod_st s s') (at level 87, right associativity).

Lemma congr_nat_st : nat_st = nat_st.
Proof.
exact (eq_refl).
Qed.

Lemma congr_bool_st : bool_st = bool_st.
Proof.
exact (eq_refl).
Qed.

Lemma congr_list_st {s0 : st} {t0 : st} (H0 : s0 = t0) :
  list_st s0 = list_st t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => list_st x) H0)).
Qed.

Lemma congr_prop_st : prop_st = prop_st.
Proof.
exact (eq_refl).
Qed.

Lemma congr_to_st {s0 : st} {s1 : st} {t0 : st} {t1 : st} (H0 : s0 = t0)
  (H1 : s1 = t1) : to_st s0 s1 = to_st t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => to_st x s1) H0))
         (ap (fun x => to_st t0 x) H1)).
Qed.

Lemma congr_prod_st {s0 : st} {s1 : st} {t0 : st} {t1 : st} (H0 : s0 = t0)
  (H1 : s1 = t1) : prod_st s0 s1 = prod_st t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => prod_st x s1) H0))
         (ap (fun x => prod_st t0 x) H1)).
Qed.

Inductive tm : Type :=
| var_tm : nat -> tm
| lam_tm : tm -> tm
| app_tm : tm -> tm -> tm
| z_tm : tm
| s_tm : tm -> tm
| recN_tm : tm -> tm -> tm -> tm
| tt_tm : tm
| ff_tm : tm
| recB_tm : tm -> tm -> tm -> tm
| nil_tm : tm
| cons_tm : tm -> tm -> tm
| recL_tm : tm -> tm -> tm -> tm
| pair_tm : tm -> tm -> tm
| pi1_tm : tm -> tm
| pi2_tm : tm -> tm
| imp_tm : tm -> tm -> tm
| forall_tm : tm -> tm
| sort_tm : tm -> tm.

Notation "⟦ n ⟧ₛ" := (var_tm n).
Notation ƛ := lam_tm.
Notation "t @ₛ u" := (app_tm t u) (at level 88, left associativity).
Notation Zₛ := z_tm.
Notation Sₛ := s_tm.
Notation recℕₛ := recN_tm.
Notation ttₛ := tt_tm.
Notation ffₛ := ff_tm.
Notation rec𝔹ₛ := recB_tm.
Notation "[]ₛ" := nil_tm.
Notation "t ::ₛ u" := (cons_tm t u) (at level 86, right associativity).
Notation rec𝕃ₛ := recL_tm.
Notation "⟨ t , u ⟩ₛ" := (pair_tm t u).
Notation "π¹ₛ" := pi1_tm.
Notation "π²ₛ" := pi2_tm.
Notation "φ ⇒ₛ ψ" := (imp_tm φ ψ) (at level 89, right associativity).
Notation "∀ₛ" := forall_tm.
Notation 𝕊 := sort_tm.

Lemma congr_lam_tm {s0 : tm} {t0 : tm} (H0 : s0 = t0) : lam_tm s0 = lam_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam_tm x) H0)).
Qed.

Lemma congr_app_tm {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : app_tm s0 s1 = app_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app_tm x s1) H0))
         (ap (fun x => app_tm t0 x) H1)).
Qed.

Lemma congr_z_tm : z_tm = z_tm.
Proof.
exact (eq_refl).
Qed.

Lemma congr_s_tm {s0 : tm} {t0 : tm} (H0 : s0 = t0) : s_tm s0 = s_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => s_tm x) H0)).
Qed.

Lemma congr_recN_tm {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm}
  {t2 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  recN_tm s0 s1 s2 = recN_tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => recN_tm x s1 s2) H0))
            (ap (fun x => recN_tm t0 x s2) H1))
         (ap (fun x => recN_tm t0 t1 x) H2)).
Qed.

Lemma congr_tt_tm : tt_tm = tt_tm.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ff_tm : ff_tm = ff_tm.
Proof.
exact (eq_refl).
Qed.

Lemma congr_recB_tm {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm}
  {t2 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  recB_tm s0 s1 s2 = recB_tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => recB_tm x s1 s2) H0))
            (ap (fun x => recB_tm t0 x s2) H1))
         (ap (fun x => recB_tm t0 t1 x) H2)).
Qed.

Lemma congr_nil_tm : nil_tm = nil_tm.
Proof.
exact (eq_refl).
Qed.

Lemma congr_cons_tm {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : cons_tm s0 s1 = cons_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => cons_tm x s1) H0))
         (ap (fun x => cons_tm t0 x) H1)).
Qed.

Lemma congr_recL_tm {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm}
  {t2 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  recL_tm s0 s1 s2 = recL_tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => recL_tm x s1 s2) H0))
            (ap (fun x => recL_tm t0 x s2) H1))
         (ap (fun x => recL_tm t0 t1 x) H2)).
Qed.

Lemma congr_pair_tm {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : pair_tm s0 s1 = pair_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pair_tm x s1) H0))
         (ap (fun x => pair_tm t0 x) H1)).
Qed.

Lemma congr_pi1_tm {s0 : tm} {t0 : tm} (H0 : s0 = t0) : pi1_tm s0 = pi1_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => pi1_tm x) H0)).
Qed.

Lemma congr_pi2_tm {s0 : tm} {t0 : tm} (H0 : s0 = t0) : pi2_tm s0 = pi2_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => pi2_tm x) H0)).
Qed.

Lemma congr_imp_tm {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : imp_tm s0 s1 = imp_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => imp_tm x s1) H0))
         (ap (fun x => imp_tm t0 x) H1)).
Qed.

Lemma congr_forall_tm {s0 : tm} {t0 : tm} (H0 : s0 = t0) :
  forall_tm s0 = forall_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => forall_tm x) H0)).
Qed.

Lemma congr_sort_tm {s0 : tm} {t0 : tm} (H0 : s0 = t0) :
  sort_tm s0 = sort_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => sort_tm x) H0)).
Qed.

Lemma upRen_tm_tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_tm (xi_tm : nat -> nat) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => var_tm (xi_tm s0)
  | lam_tm s0 => lam_tm (ren_tm (upRen_tm_tm xi_tm) s0)
  | app_tm s0 s1 => app_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | z_tm => z_tm
  | s_tm s0 => s_tm (ren_tm xi_tm s0)
  | recN_tm s0 s1 s2 =>
      recN_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | tt_tm => tt_tm
  | ff_tm => ff_tm
  | recB_tm s0 s1 s2 =>
      recB_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | nil_tm => nil_tm
  | cons_tm s0 s1 => cons_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | recL_tm s0 s1 s2 =>
      recL_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | pair_tm s0 s1 => pair_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | pi1_tm s0 => pi1_tm (ren_tm xi_tm s0)
  | pi2_tm s0 => pi2_tm (ren_tm xi_tm s0)
  | imp_tm s0 s1 => imp_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | forall_tm s0 => forall_tm (ren_tm (upRen_tm_tm xi_tm) s0)
  | sort_tm s0 => sort_tm (ren_tm xi_tm s0)
  end.

Lemma up_tm_tm (sigma : nat -> tm) : nat -> tm.
Proof.
exact (scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm (sigma_tm : nat -> tm) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => sigma_tm s0
  | lam_tm s0 => lam_tm (subst_tm (up_tm_tm sigma_tm) s0)
  | app_tm s0 s1 => app_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | z_tm => z_tm
  | s_tm s0 => s_tm (subst_tm sigma_tm s0)
  | recN_tm s0 s1 s2 =>
      recN_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
        (subst_tm sigma_tm s2)
  | tt_tm => tt_tm
  | ff_tm => ff_tm
  | recB_tm s0 s1 s2 =>
      recB_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
        (subst_tm sigma_tm s2)
  | nil_tm => nil_tm
  | cons_tm s0 s1 => cons_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | recL_tm s0 s1 s2 =>
      recL_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
        (subst_tm sigma_tm s2)
  | pair_tm s0 s1 => pair_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | pi1_tm s0 => pi1_tm (subst_tm sigma_tm s0)
  | pi2_tm s0 => pi2_tm (subst_tm sigma_tm s0)
  | imp_tm s0 s1 => imp_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | forall_tm s0 => forall_tm (subst_tm (up_tm_tm sigma_tm) s0)
  | sort_tm s0 => sort_tm (subst_tm sigma_tm s0)
  end.

Lemma upId_tm_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = var_tm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_tm (sigma_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam_tm s0 =>
      congr_lam_tm (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  | app_tm s0 s1 =>
      congr_app_tm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 => congr_s_tm (idSubst_tm sigma_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1) (idSubst_tm sigma_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1) (idSubst_tm sigma_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1) (idSubst_tm sigma_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | pi1_tm s0 => congr_pi1_tm (idSubst_tm sigma_tm Eq_tm s0)
  | pi2_tm s0 => congr_pi2_tm (idSubst_tm sigma_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  | sort_tm s0 => congr_sort_tm (idSubst_tm sigma_tm Eq_tm s0)
  end.

Lemma upExtRen_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm) {struct s} :
ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | lam_tm s0 =>
      congr_lam_tm
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  | app_tm s0 s1 =>
      congr_app_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 => congr_s_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | pi1_tm s0 => congr_pi1_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | pi2_tm s0 => congr_pi2_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  | sort_tm s0 => congr_sort_tm (extRen_tm xi_tm zeta_tm Eq_tm s0)
  end.

Lemma upExt_tm_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam_tm s0 =>
      congr_lam_tm
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  | app_tm s0 s1 =>
      congr_app_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 => congr_s_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | pi1_tm s0 => congr_pi1_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
  | pi2_tm s0 => congr_pi2_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  | sort_tm s0 => congr_sort_tm (ext_tm sigma_tm tau_tm Eq_tm s0)
  end.

Lemma up_ren_ren_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(rho_tm : nat -> nat) (Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x)
(s : tm) {struct s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | lam_tm s0 =>
      congr_lam_tm
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  | app_tm s0 s1 =>
      congr_app_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 => congr_s_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | pi1_tm s0 => congr_pi1_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | pi2_tm s0 => congr_pi2_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  | sort_tm s0 => congr_sort_tm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  end.

Lemma up_ren_subst_tm_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm) {struct s} :
subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam_tm s0 =>
      congr_lam_tm
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  | app_tm s0 s1 =>
      congr_app_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 => congr_s_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | pi1_tm s0 =>
      congr_pi1_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | pi2_tm s0 =>
      congr_pi2_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  | sort_tm s0 =>
      congr_sort_tm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  end.

Lemma up_subst_ren_tm_tm (sigma : nat -> tm) (zeta_tm : nat -> nat)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x) 
(s : tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam_tm s0 =>
      congr_lam_tm
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  | app_tm s0 s1 =>
      congr_app_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 =>
      congr_s_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | pi1_tm s0 =>
      congr_pi1_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | pi2_tm s0 =>
      congr_pi2_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  | sort_tm s0 =>
      congr_sort_tm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  end.

Lemma up_subst_subst_tm_tm (sigma : nat -> tm) (tau_tm : nat -> tm)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam_tm s0 =>
      congr_lam_tm
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  | app_tm s0 s1 =>
      congr_app_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 =>
      congr_s_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | pi1_tm s0 =>
      congr_pi1_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | pi2_tm s0 =>
      congr_pi2_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  | sort_tm s0 =>
      congr_sort_tm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  end.

Lemma renRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise (xi_tm : nat -> nat) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise (xi_tm : nat -> nat) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise (sigma_tm : nat -> tm) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_tm : nat -> nat) (sigma_tm : nat -> tm)
(Eq_tm : forall x, funcomp (var_tm) xi_tm x = sigma_tm x) (s : tm) {struct s}
   : ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam_tm s0 =>
      congr_lam_tm
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  | app_tm s0 s1 =>
      congr_app_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | z_tm => congr_z_tm
  | s_tm s0 => congr_s_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | recN_tm s0 s1 s2 =>
      congr_recN_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tt_tm => congr_tt_tm
  | ff_tm => congr_ff_tm
  | recB_tm s0 s1 s2 =>
      congr_recB_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | nil_tm => congr_nil_tm
  | cons_tm s0 s1 =>
      congr_cons_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | recL_tm s0 s1 s2 =>
      congr_recL_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | pair_tm s0 s1 =>
      congr_pair_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | pi1_tm s0 => congr_pi1_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | pi2_tm s0 => congr_pi2_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | imp_tm s0 s1 =>
      congr_imp_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | forall_tm s0 =>
      congr_forall_tm
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  | sort_tm s0 => congr_sort_tm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  end.

Lemma rinstInst'_tm (xi_tm : nat -> nat) (s : tm) :
  ren_tm xi_tm s = subst_tm (funcomp (var_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (ren_tm xi_tm) (subst_tm (funcomp (var_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_tm) s = s.
Proof.
exact (idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise : pointwise_relation _ eq (subst_tm (var_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise : pointwise_relation _ eq (@ren_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm (sigma_tm : nat -> tm) (x : nat) :
  subst_tm sigma_tm (var_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise (sigma_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm)) sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm (xi_tm : nat -> nat) (x : nat) :
  ren_tm xi_tm (var_tm x) = var_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm))
    (funcomp (var_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

#[global] Instance Subst_tm : (Subst1 _ _ _) := @subst_tm.

#[global] Instance Up_tm_tm : (Up_tm _ _) := @up_tm_tm.

#[global] Instance Ren_tm : (Ren1 _ _ _) := @ren_tm.

#[global]
Instance VarInstance_tm : (Var _ _) := @var_tm.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing)  : subst_scope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing)  : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
( at level 5, format "x __tm", only printing)  : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm")  :
subst_scope.

#[global]
Instance subst_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => ext_tm f_tm g_tm Eq_tm s).
Qed.

#[global]
Instance ren_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance ren_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => extRen_tm f_tm g_tm Eq_tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress unfold up_tm_tm, upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_tm: rewrite.

#[global] Hint Opaque ren_tm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

