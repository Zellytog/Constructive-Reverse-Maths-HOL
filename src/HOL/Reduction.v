From CRM Require Import Base Typing fintype.
Import CombineNotations SubstNotations.

Definition rewriting :=
  forall (n : nat), tm n -> tm n -> Prop.

Inductive reduc : rewriting :=
| beta_lam : forall {n : nat} (t : tm (S n)) (u : tm n),
    reduc n ((ƛ t) @ₛ u) (t [u .: var_tm])
| beta_pair1 : forall {n : nat} (t u : tm n),
    reduc n (π¹ₛ ⟨ t , u ⟩ₛ) t
| beta_pair2 : forall {n : nat} (t u : tm n),
    reduc n (π²ₛ ⟨ t , u ⟩ₛ) u
| beta_Nz : forall {n : nat} (t u : tm n),
    reduc n (recℕₛ t u Zₛ) t
| beta_Ns : forall {n : nat} (t u v : tm n),
    reduc n (recℕₛ t u (Sₛ v)) (u @ₛ v @ₛ (recℕₛ t u v))
| beta_Bt : forall {n : nat} (t u : tm n),
    reduc n (rec𝔹ₛ t u ttₛ) t
| beta_Bf : forall {n : nat} (t u : tm n),
    reduc n (rec𝔹ₛ t u ffₛ) u
| beta_Ln : forall {n : nat} (t u : tm n),
    reduc n (rec𝕃ₛ t u []ₛ) t
| beta_Lc : forall {n : nat} (t u v w : tm n),
    reduc n (rec𝕃ₛ t u (v ::ₛ w)) (u @ₛ v @ₛ w @ₛ (rec𝕃ₛ t u w)).

Inductive to_compat (R : rewriting) : rewriting :=
| incl_R : forall {n : nat} {t u : tm n},
    R n t u ->
    to_compat R n t u
| sub_lam : forall {n : nat} {t u : tm (S n)},
    to_compat R (S n) t u ->
    to_compat R n (ƛ t) (ƛ u)
| sub_app_1 : forall {n : nat} {t u v : tm n},
    to_compat R n t u ->
    to_compat R n (t @ₛ v) (u @ₛ v)
| sub_app_2 : forall {n : nat} {t u v : tm n},
    to_compat R n u v ->
    to_compat R n (t @ₛ u) (t @ₛ v)
| sub_S : forall {n : nat} {t u : tm n},
    to_compat R n t u ->
    to_compat R n (Sₛ t) (Sₛ u)
| sub_recN_1 : forall {n : nat} {t u v w : tm n},
    to_compat R n t u ->
    to_compat R n (recℕₛ t v w) (recℕₛ u v w)
| sub_recN_2 : forall {n : nat} {t u v w : tm n},
    to_compat R n u v ->
    to_compat R n (recℕₛ t u w) (recℕₛ t v w)
| sub_recN_3 : forall {n : nat} {t u v w : tm n},
    to_compat R n v w ->
    to_compat R n (recℕₛ t u v) (recℕₛ t u w)
| sub_recB_1 : forall {n : nat} {t u v w : tm n},
    to_compat R n t u ->
    to_compat R n (rec𝔹ₛ t v w) (rec𝔹ₛ u v w)
| sub_recB_2 : forall {n : nat} {t u v w : tm n},
    to_compat R n u v ->
    to_compat R n (rec𝔹ₛ t u w) (rec𝔹ₛ t v w)
| sub_recB_3 : forall {n : nat} {t u v w : tm n},
    to_compat R n v w ->
    to_compat R n (rec𝔹ₛ t u v) (rec𝔹ₛ t u w)
| sub_cons_1 : forall {n : nat} {t u v : tm n},
    to_compat R n t u ->
    to_compat R n (t ::ₛ v) (u ::ₛ v)
| sub_cons_2 : forall {n : nat} {t u v : tm n},
    to_compat R n u v ->
    to_compat R n (t ::ₛ u) (t ::ₛ v)
| sub_recL_1 : forall {n : nat} {t u v w : tm n},
    to_compat R n t u ->
    to_compat R n (rec𝕃ₛ t v w) (rec𝕃ₛ u v w)
| sub_recL_2 : forall {n : nat} {t u v w : tm n},
    to_compat R n u v ->
    to_compat R n (rec𝕃ₛ t u w) (rec𝕃ₛ t v w)
| sub_recL_3 : forall {n : nat} {t u v w : tm n},
    to_compat R n v w ->
    to_compat R n (rec𝕃ₛ t u v) (rec𝕃ₛ t u w)
| sub_pair_1 : forall {n : nat} {t u v : tm n},
    to_compat R n t u ->
    to_compat R n ⟨ t, v ⟩ₛ ⟨ u, v ⟩ₛ
| sub_pair_2 : forall {n : nat} {t u v : tm n},
    to_compat R n u v ->
    to_compat R n ⟨ t, u ⟩ₛ ⟨ t, v ⟩ₛ
| sub_proj1 : forall {n : nat} {t u : tm n},
    to_compat R n t u ->
    to_compat R n (π¹ₛ t) (π¹ₛ u)
| sub_proj2 : forall {n : nat} {t u : tm n},
    to_compat R n t u ->
    to_compat R n (π²ₛ t) (π²ₛ u)
| sub_imp_1 : forall {n : nat} {t u v : tm n},
    to_compat R n t u ->
    to_compat R n (t ⇒ₛ v) (u ⇒ₛ v)
| sub_imp_2 : forall {n : nat} {t u v : tm n},
    to_compat R n u v ->
    to_compat R n (t ⇒ₛ u) (t ⇒ₛ v)
| sub_forall : forall {n : nat} {s : st} {t u : tm (S n)},
    to_compat R (S n) t u ->
    to_compat R n (∀ₛ s t) (∀ₛ s u)
| sub_sort : forall {n : nat} {t u : tm n} {s : st},
    to_compat R n t u ->
    to_compat R n (𝕊 s t) (𝕊 s u).

Definition βred : rewriting :=
  to_compat reduc.

Inductive t_closure (R : rewriting) : rewriting :=
| t_one : forall {n : nat} (t u : tm n),
    R n t u -> t_closure R n t u
| t_add : forall {n : nat} {t : tm n}
                 (u : tm n) {v : tm n},
    t_closure R n t u -> R n u v ->
    t_closure R n t v.

Inductive rt_closure (R : rewriting) : rewriting :=
| rt_refl : forall {n : nat} (t : tm n),
    rt_closure R n t t
| rt_add : forall {n : nat} {t : tm n}
                  (u : tm n) {v : tm n},
    rt_closure R n t u -> R n u v ->
    rt_closure R n t v.

Inductive rts_closure (R : rewriting) : rewriting :=
| rts_refl : forall {n : nat} (t : tm n),
    rts_closure R n t t
| rts_add : forall {n : nat} {t : tm n}
                   (u : tm n) {v : tm n},
    rts_closure R n t u -> R n u v ->
    rts_closure R n t v
| rts_sym : forall {n : nat} {t : tm n}
                   (u : tm n) {v : tm n},
    rts_closure R n t u -> R n v u ->
    rts_closure R n t v.

Notation "R >+" := (t_closure R) (at level 65).
Notation "R >*" := (rt_closure R) (at level 65).
Notation "R >~" := (rts_closure R) (at level 65).

Lemma closure_R_in_t :
 forall (R : rewriting) {n : nat}
        {t u : tm n}, R n t u -> R >+ n t u.
Proof.
  intros. apply t_one. apply H.
Qed.

Lemma closure_R_in_rt :
  forall (R : rewriting) {n : nat}
         {t u : tm n}, R n t u -> R >* n t u.
Proof.
  intros. apply (rt_add _ _ (rt_refl R t) H).
Qed.

Lemma closure_R_in_rts :
  forall (R : rewriting) {n : nat}
         {t u : tm n}, R n t u -> R >~ n t u.
Proof.
  intros. apply (rts_add _ _ (rts_refl R t) H).
Qed.

Lemma closure_t_trans :
  forall (R : rewriting) {n : nat}
         {t : tm n} (u : tm n) {v : tm n},
    R >+ n t u -> R >+ n u v -> R >+ n t v.
Proof.
  intros. induction H0. apply (t_add R _ H H0).
  apply (t_add R u). apply IHt_closure. apply H. apply H1.
Qed.

Lemma closure_rt_trans :
  forall (R : rewriting) {n : nat}
         {t : tm n} (u : tm n) {v : tm n},
    R >* n t u -> R >* n u v -> R >* n t v.
Proof.
  intros. induction H0. apply H. apply (rt_add R u).
  apply IHrt_closure. apply H. apply H1.
Qed.

Lemma closure_rts_trans :
  forall (R : rewriting) {n : nat}
         {t : tm n} (u : tm n) {v : tm n},
    R >~ n t u -> R >~ n u v -> R >~ n t v.
Proof.
  intros. induction H0. apply H. apply (rts_add R u).
  apply IHrts_closure. apply H. apply H1. apply (rts_sym R u).
  apply IHrts_closure. apply H. apply H1.
Qed.

Lemma closure_rts_sym :
  forall (R : rewriting) {n : nat}
         {t u : tm n}, R >~ n t u -> R >~ n u t.
Proof.
  intros. induction H. apply rts_refl.
  apply (closure_rts_trans R u).
  apply (rts_sym _ _ (rts_refl R v) H0). apply IHrts_closure.
  apply (closure_rts_trans R u).
  apply (rts_add _ _ (rts_refl R v) H0). apply IHrts_closure.
Qed.

Lemma closure_t_in_rt :
  forall (R : rewriting) {n : nat} {t u : tm n},
    R >+ n t u -> R >* n t u.
Proof.
  intros. induction H. apply (rt_add R _ (rt_refl R t) H).
  apply (rt_add R _ IHt_closure H0).
Qed.

Lemma closure_t_in_rts :
  forall (R : rewriting) {n : nat} {t u : tm n},
    R >+ n t u -> R >~ n t u.
Proof.
  intros. induction H. apply (rts_add R _ (rts_refl R t) H).
  apply (rts_add R _ IHt_closure H0).
Qed.

Lemma closure_rt_in_rts :
  forall (R : rewriting) {n : nat} {t u : tm n},
    R >* n t u -> R >~ n t u.
Proof.
  intros. induction H. apply rts_refl.
  apply (rts_add R _ IHrt_closure H0).
Qed.

(** We define the main properties of diamond, local confluence and
    confluence. *)

Definition Diamond_prop (R : rewriting) : Prop :=
  forall (n : nat) (t u v : tm n),
    R n t u /\ R n t v ->
    exists w : tm n, R n u w /\ R n v w.

Definition Local_confluence (R : rewriting) : Prop :=
  forall (n : nat) (t u v : tm n),
    R n t u /\ R n t v ->
    exists w : tm n, R >* n u w /\ R >* n v w.

Definition Confluence (R : rewriting) : Prop :=
  forall (n : nat) (t u v : tm n),
    R >* n t u /\ R >* n t v ->
    exists w : tm n, R >* n u w /\ R >* n v w.

Definition Church_Rosser_prop (R : rewriting) : Prop :=
  forall (n : nat) (t u : tm n),
    R >~ n t u ->
    exists v : tm n, R >* n t v /\ R >* n u v.

(** → is confluent iff →＊ has the diamond property. *)

Lemma confluence_is_rt_diamond :
  forall (R : rewriting), (Confluence R <-> Diamond_prop (R >* )).
Proof.
  intro; split; intro. unfold Diamond_prop; intros.
  specialize (H n t u v H0). destruct H. exists x. apply H.
  unfold Confluence; intros. specialize (H n t u v H0).
  destruct H. exists x. apply H.
Qed.

(** Diamond property implies confluence. *)

Lemma diamond_gives_confluence :
  forall (R : rewriting), Diamond_prop R -> Confluence R.
Proof.
  intros R HR n t. unfold Confluence; intros u v tuv.
  destruct tuv as [tu tv].
  revert v tv; induction tu as [ | n t u w ]; intros v tv.
  - exists v. split; [apply tv | apply rt_refl].
  - specialize (IHtu v tv); destruct IHtu as [y [uy vy]].
    assert (exists x : tm n, R n y x /\ R >* n w x).
    clear tv tu vy t v. induction uy.
    + exists w. split; [apply H | apply rt_refl].
    + specialize (IHuy w H); destruct IHuy as [z [uz wz]].
      specialize (HR _ _ _ _ (conj H0 uz)).
      destruct HR as [x [vx zx]].
      exists x. split.
      apply vx. apply (closure_rt_trans _ x).
      apply (rt_add R z). apply wz. apply zx.
      apply rt_refl.
    + destruct H0 as [x [yx wx]].
      exists x. split; [apply wx|].
      apply (rt_add _ y). apply vy. apply yx.
Qed.

(** Church-Rosser property is equivalent to confluence. *)

Lemma CR_equiv_confluence :
  forall (R : rewriting), Confluence R <-> Church_Rosser_prop R.
Proof.
  intro; split; intro. unfold Church_Rosser_prop. intros.
  induction H0. exists t. split; apply rt_refl.
  destruct IHrts_closure. destruct H2. unfold Confluence in H.
  specialize (H n u v x).
  assert (R >* n u v /\ R >* n u x). split. apply closure_R_in_rt.
  apply H1. apply H3.
  specialize (H H4). destruct H. destruct H. exists x0.
  split; try apply H.
  apply (closure_rt_trans _ _ H2 H5). destruct IHrts_closure.
  destruct H2. exists x.
  split; try apply H2.
  apply (closure_rt_trans R u); try apply H3.
  apply closure_R_in_rt. apply H1.
  unfold Confluence. intros. unfold Church_Rosser_prop in H.
  specialize (H n u v). apply H. apply (closure_rts_trans R t).
  apply closure_rts_sym.
  apply closure_rt_in_rts. apply H0. apply closure_rt_in_rts.
  apply H0.
Qed.

(** If two relations are equal, they have the same properties. *)

Lemma diamond_stable_equiv :
  forall (R T : rewriting),
    (forall (n : nat) (t u : tm n), R n t u <-> T n t u) ->
    Diamond_prop R -> Diamond_prop T.
Proof.
  intros. unfold Diamond_prop; intros. unfold Diamond_prop in H0.
  destruct H1.
  apply H in H1. apply H in H2. assert (R n t u /\ R n t v). split.
  apply H1. apply H2.
  specialize (H0 n t u v H3). destruct H0. destruct H0.
  apply H in H0. apply H in H4.
  exists x. split; try apply H0; apply H4.
Qed.

Definition βeq := (βred >~ ).

Notation "t =ₛ u" := (βeq t u) (at level 87).
