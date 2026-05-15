From CRM Require Import Base.
From Stdlib Require Import List Program.Equality.
Import ListNotations.

(* We call a relation on terms a relation
   (R ⊂ Σ[ Γ, s ∈ HOL_ctx × st] Γ ⊢ₛ s)² *)

Definition Rel_tm : Type :=
  forall (Γ : HOL_ctx) (s : st), Γ ⊢ₛ s -> Γ ⊢ₛ s -> Prop.

(* We define the inclusion relation and equivalence relation, on relations,
 along with their basic properties. *)

Definition incl_Rel (R R' : Rel_tm) : Prop :=
  forall (Γ : HOL_ctx) (s : st) (t u : Γ ⊢ₛ s), R Γ s t u -> R' Γ s t u.

Notation "R ⊂ R'" := (incl_Rel R R') (at level 60).

Lemma trans_incl : forall (R R' R'' : Rel_tm),
    R ⊂ R' -> R' ⊂ R'' -> R ⊂ R''.
Proof.
  intros R R' R'' RR' R'R'' Γ s t u Rtu; apply R'R''; apply RR'; apply Rtu.
Qed.

Definition equiv_Rel (R R' : Rel_tm) : Prop := R ⊂ R' /\ R' ⊂ R.

Notation "R ≡ R'" := (equiv_Rel R R') (at level 60).

Lemma trans_equiv : forall (R R' R'' : Rel_tm),
    R ≡ R' -> R' ≡ R'' -> R ≡ R''.
Proof.
  intros R R' R'' [RR' R'R] [R'R'' R''R'].
  exact (conj (trans_incl _ _ _ RR' R'R'') (trans_incl _ _ _ R''R' R'R)).
Qed.

Lemma sym_equiv : forall (R R' : Rel_tm), R ≡ R' -> R' ≡ R.
Proof. intros R R' [RR' R'R]. exact (conj R'R RR'). Qed.

(* We state the usual properties on relations: symmetry, reflexivity and
 transitivity. *)

Definition is_sym_rel (R : Rel_tm) : Prop :=
  forall (Γ : HOL_ctx) (s : st) (t u : Γ ⊢ₛ s), R Γ s t u -> R Γ s u t.

Definition is_trans_rel (R : Rel_tm) : Prop :=
  forall (Γ : HOL_ctx) (s : st) (t u v : Γ ⊢ₛ s),
    R Γ s t u -> R Γ s u v -> R Γ s t v.

Definition is_refl_rel (R : Rel_tm) : Prop :=
  forall (Γ : HOL_ctx) (s : st) (t : Γ ⊢ₛ s), R Γ s t t.

(* We also define the symmetric closure, the reflexivity and transitive closure,
 and the equivalence relation closure. *)

Inductive s_clot (R : Rel_tm) : Rel_tm :=
| s_step : forall {Γ : HOL_ctx} {s : st} {t u : Γ ⊢ₛ s},
    R Γ s t u -> s_clot R Γ s t u
| s_unstep : forall {Γ : HOL_ctx} {s : st} {t u : Γ ⊢ₛ s},
    R Γ s u t -> s_clot R Γ s t u.

Inductive rt_clot (R : Rel_tm) : Rel_tm :=
| rt_refl : forall {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s), rt_clot R _ _ t t
| rt_step : forall {Γ : HOL_ctx} {s : st} {t v : Γ ⊢ₛ s} (u : Γ ⊢ₛ s),
    rt_clot R _ _ t u -> R _ _ u v -> rt_clot R _ _ t v.

Inductive rst_clot (R : Rel_tm) : Rel_tm :=
| rst_refl : forall {Γ : HOL_ctx} {s : st} (t : Γ ⊢ₛ s), rst_clot R _ _ t t
| rst_step : forall {Γ : HOL_ctx} {s : st} {t v : Γ ⊢ₛ s} (u : Γ ⊢ₛ s),
    rst_clot R _ _ t u -> R _ _ u v -> rst_clot R _ _ t v
| rst_unstep : forall {Γ : HOL_ctx} {s : st} {t v : Γ ⊢ₛ s} (u : Γ ⊢ₛ s),
    rst_clot R _ _ t u -> R _ _ v u -> rst_clot R _ _ t v.

(* We state that they are indeed closures: they have the expected properties,
 and contain the relation they are built on. *)

Proposition s_r : forall (R : Rel_tm), R ⊂ (s_clot R).
Proof. intros R Γ s t u Rtu; apply s_step; apply Rtu. Qed.

Proposition rt_r : forall (R : Rel_tm), R ⊂ rt_clot R.
Proof. intros R Γ s t u. apply (rt_step R t). constructor. Qed.

Proposition rst_r : forall (R : Rel_tm), R ⊂ rst_clot R.
Proof. intros R Γ s t u. apply (rst_step R t). constructor. Qed.

Proposition rt_trans : forall (R : Rel_tm), is_trans_rel (rt_clot R).
Proof.
  intros R Γ s t u v H H0. induction H0. apply H. apply (rt_step _ u).
  apply IHrt_clot. apply H. apply H1.
Qed.

Proposition rst_trans : forall (R : Rel_tm), is_trans_rel (rst_clot R).
Proof.
  intros R Γ s t u v H H0. induction H0. apply H. apply (rst_step _ u).
  apply IHrst_clot. apply H. apply H1.
  apply (rst_unstep _ u). apply IHrst_clot. apply H. apply H1.
Qed.

Proposition s_sym : forall (R : Rel_tm), is_sym_rel (s_clot R).
Proof.
  intros R Γ s t u tu.
  induction tu; [apply s_unstep | apply s_step]; assumption.
Qed.

Proposition rst_sym : forall (R : Rel_tm), is_sym_rel (rst_clot R).
Proof.
  intros R Γ s t u H. induction H. constructor.
  apply (rst_trans R Γ s v u t). apply (rst_unstep R v). constructor.
  assumption. apply IHrst_clot.
  apply (rst_trans R _ _ _ u). apply rst_r. apply H0. apply IHrst_clot.
Qed.

(* In fact, symmetry behaves well w.r.t reflexive and transitive closure. *)

Proposition rt_comp_sym : forall (R : Rel_tm),
    is_sym_rel R -> is_sym_rel (rt_clot R).
Proof.
  intros R sR Γ s t u Rtu. induction Rtu.
  apply rt_refl. apply (rt_trans _ _ _ _ u).
  apply rt_r. apply sR. apply H.
  apply IHRtu.
Qed.

(* The closures satisfy a universal property among the relations. *)

Lemma PU_s_clot : forall (R R' : Rel_tm),
    R ⊂ R' -> is_sym_rel R' -> s_clot R ⊂ R'.
Proof.
  intros R R' RR' sR' Γ s t u Rtu.
  induction Rtu. apply RR'. apply H.
  apply sR'. apply RR'. apply H.
Qed.

Lemma PU_rt_clot : forall (R R' : Rel_tm),
    R ⊂ R' -> is_refl_rel R' -> is_trans_rel R' -> rt_clot R ⊂ R'.
Proof.
  intros R R' RR' rR' tR' Γ s t u Rtu.
  induction Rtu. apply rR'. apply (tR' Γ s t u v).
  apply IHRtu. apply RR'. apply H.
Qed.

Lemma PU_rst_clot : forall (R R' : Rel_tm),
    R ⊂ R' -> is_refl_rel R' -> is_sym_rel R' -> is_trans_rel R' ->
    rst_clot R ⊂ R'.
Proof.
  intros R R' RR' rR' sR' tR' Γ s t u Rtu.
  induction Rtu. apply rR'.
  apply (tR' Γ s t u v). apply IHRtu. apply RR'. apply H.
  apply (tR' Γ s t u v). apply IHRtu. apply sR'. apply RR'. apply H.
Qed.

(* This allows to show that ∼ᴿ = (↔ᴿ)*. *)

Lemma rst_is_rt_of_s :
  forall (R : Rel_tm), rst_clot R ≡ rt_clot (s_clot R).
Proof.
  intro. split.
  apply PU_rst_clot. apply (trans_incl _ (s_clot R)).
  apply s_r. apply rt_r.
  intros Γ s t. apply rt_refl.
  apply rt_comp_sym. apply s_sym. apply rt_trans.
  apply PU_rt_clot. apply PU_s_clot. apply rst_r.
  apply rst_sym. intros Γ s st; apply rst_refl. apply rst_trans.
Qed.

(* An extensional predicate on relation is one that is compatible with ≡. *)

Definition ext_prop_rel (P : Rel_tm -> Prop) : Prop :=
  forall R R' : Rel_tm, R ≡ R' -> P R -> P R'.

(* To show that an extensional predicate holds on the equivalence relation
 closure of a relation, it suffices to show that it holds for the rt and the s
 closure. *)

Lemma prop_to_rst :
  forall (P : Rel_tm -> Prop),
    ext_prop_rel P ->
    (forall R : Rel_tm, P R -> P (s_clot R)) ->
    (forall R : Rel_tm, P R -> P (rt_clot R)) ->
    forall R : Rel_tm, P R -> P (rst_clot R).
Proof.
  intros. apply (H (rt_clot (s_clot R))).
  apply sym_equiv. apply rst_is_rt_of_s.
  apply H1. apply H0. apply H2.
Qed.
