Section Relation.

  Variable A : Type.

  Definition rewrit : Type := A -> A -> Prop.

  Inductive t_closure (R : rewrit) : rewrit :=
  | t_one : forall a b : A, R a b -> t_closure R a b
  | t_add : forall a b c : A, t_closure R a b -> R b c ->
                                   t_closure R a c.
  
  Inductive rt_closure (R : rewrit) : rewrit :=
  | rt_refl : forall a : A, rt_closure R a a
  | rt_add : forall a b c : A, rt_closure R a b -> R b c ->
                                 rt_closure R a c.
  
  Inductive rts_closure (R : rewrit) : rewrit :=
  | rts_refl : forall a : A, rts_closure R a a
  | rts_add : forall a b c : A, rts_closure R a b -> R b c ->
                                  rts_closure R a c
  | rts_sym : forall a b c : A, rts_closure R a b -> R c b ->
                                  rts_closure R a c.
  
  Notation "R >+" := (t_closure R) (at level 65).
  Notation "R >*" := (rt_closure R) (at level 65).
  Notation "R >~" := (rts_closure R) (at level 65).
  
  Lemma closure_R_in_t : forall (R : rewrit) (t u : A),
      R t u -> R >+ t u.
  Proof.
    intros. apply t_one. apply H.
  Qed.
  
  Lemma closure_R_in_rt : forall (R : rewrit) (t u : A),
      R t u -> R >* t u.
  Proof.
    intros. apply (rt_add _ _ _ _ (rt_refl R t) H).
  Qed.

  Lemma closure_R_in_rts : forall (R : rewrit) (t u : A),
      R t u -> R >~ t u.
  Proof.
    intros. apply (rts_add _ _ _ _ (rts_refl R t) H).
  Qed.

  Lemma closure_t_trans : forall (R : rewrit) (t u v : A),
      R >+ t u -> R >+ u v -> R >+ t v.
  Proof.
    intros. induction H0. apply (t_add _ _ _ _ H H0).
    apply (t_add _ _ b). apply IHt_closure. apply H. apply H1.
  Qed.

  Lemma closure_rt_trans : forall (R : rewrit) (t u v : A),
      R >* t u -> R >* u v -> R >* t v.
  Proof.
    intros. induction H0. apply H. apply (rt_add _ _ b).
    apply IHrt_closure. apply H. apply H1.
  Qed.

  Lemma closure_rts_trans : forall (R : rewrit) (t u v : A),
      R >~ t u -> R >~ u v -> R >~ t v.
  Proof.
    intros. induction H0. apply H. apply (rts_add _ _ b).
    apply IHrts_closure. apply H. apply H1. apply (rts_sym _ _ b).
    apply IHrts_closure. apply H. apply H1.
  Qed.

  Lemma closure_rts_sym : forall (R : rewrit) (t u : A),
      R >~ t u -> R >~ u t.
  Proof.
    intros. induction H. apply rts_refl.
    apply (closure_rts_trans _ _ b).
    apply (rts_sym _ _ _ _ (rts_refl R c) H0). apply IHrts_closure.
    apply (closure_rts_trans _ _ b).
    apply (rts_add _ _ _ _ (rts_refl R c) H0). apply IHrts_closure.
  Qed.

  Lemma closure_t_in_rt : forall (R : rewrit) (t u : A),
      R >+ t u -> R >* t u.
  Proof.
    intros. induction H. apply (rt_add _ _ _ _ (rt_refl R a) H).
    apply (rt_add _ _ _ _ IHt_closure H0).
  Qed.

  Lemma closure_t_in_rts : forall (R : rewrit) (t u : A),
      R >+ t u -> R >~ t u.
  Proof.
    intros. induction H. apply (rts_add _ _ _ _ (rts_refl R a) H).
    apply (rts_add _ _ _ _ IHt_closure H0).
  Qed.

  Lemma closure_rt_in_rts : forall (R : rewrit) (t u : A),
      R >* t u -> R >~ t u.
  Proof.
    intros. induction H. apply rts_refl.
    apply (rts_add _ _ _ _ IHrt_closure H0).
  Qed.

  (**
     We define the main properties of diamond, local confluence and
     confluence. *)

  Definition Diamond_prop (R : rewrit) : Prop :=
    forall t u v : A,
      R t u /\ R t v -> exists w : A, R u w /\ R v w.
  
  Definition Local_confluence (R : rewrit) : Prop :=
    forall t u v : A,
      R t u /\ R t v -> exists w : A, R >* u w /\ R >* v w.

  Definition Confluence (R : rewrit) : Prop :=
    forall t u v : A,
      R >* t u /\ R >* t v -> exists w : A, R >* u w /\ R >* v w.

  Definition Church_Rosser_prop (R : rewrit) : Prop :=
    forall t u : A,
      R >~ t u -> exists v : A, R >* t v /\ R >* u v.
  
  (** → is confluent iff →＊ has the diamond property. *)
  
  Lemma confluence_is_rt_diamond : forall (R : rewrit),
      (Confluence R <-> Diamond_prop (R >*)).
       Proof.
         intro; split; intro. unfold Diamond_prop; intros.
         specialize (H t u v H0). destruct H. exists x. apply H.
         unfold Confluence; intros. specialize (H t u v H0).
         destruct H. exists x. apply H.
       Qed.

       (** Diamond property implies confluence. *)

       Lemma diamond_gives_confluence : forall (R : rewrit),
           Diamond_prop R -> Confluence R.
       Proof.
         intros R HR a. unfold Confluence; intros b c abc.
         destruct abc as [ab ac].
         revert c ac; induction ab as [ | a b d ]; intros c ac.
         - exists c. split; [apply ac | apply rt_refl].
         - specialize (IHab c ac); destruct IHab as [e [be ce]].
           assert (exists y : A, R e y /\ R >* d y).
           clear ac ab ce. induction be as [ f | f ].
           + exists d. split; [apply H | apply rt_refl].
           + specialize (IHbe H); destruct IHbe as [g [bg dg]].
             specialize (HR b c0 g (conj H0 bg)).
             destruct HR as [g' [c0g' gg']].
             exists g'. split.
             apply c0g'. apply (closure_rt_trans _ _ g).
             apply dg. apply closure_R_in_rt. apply gg'.
           + destruct H0 as [f [ef df]].
             exists f. split; [apply df|].
             apply (rt_add _ _ e). apply ce. apply ef.
       Qed.

       (** Church-Rosser property is equivalent to confluence. *)

       Lemma CR_equiv_confluence : forall (R : rewrit),
           Confluence R <-> Church_Rosser_prop R.
       Proof.
         intro; split; intro. unfold Church_Rosser_prop. intros.
         induction H0. exists a. split; apply rt_refl.
         destruct IHrts_closure. destruct H2. unfold Confluence in H.
         specialize (H b c x).
         assert (R >* b c /\ R >* b x). split. apply closure_R_in_rt.
         apply H1. apply H3.
         specialize (H H4). destruct H. destruct H. exists x0.
         split; try apply H.
         apply (closure_rt_trans _ _ _ _ H2 H5). destruct IHrts_closure.
         destruct H2. exists x.
         split; try apply H2.
         apply (closure_rt_trans R c b x); try apply H3.
         apply closure_R_in_rt. apply H1.
         unfold Confluence. intros. unfold Church_Rosser_prop in H.
         specialize (H u v). apply H. apply (closure_rts_trans _ _ t).
         apply closure_rts_sym.
         apply closure_rt_in_rts. apply H0. apply closure_rt_in_rts.
         apply H0.
       Qed.

       (** If two relations are equal, they have the same properties. *)

       Lemma diamond_stable_equiv : forall (R T : rewrit),
           (forall t u : A, R t u <-> T t u) ->
           Diamond_prop R -> Diamond_prop T.
       Proof.
         intros. unfold Diamond_prop; intros. unfold Diamond_prop in H0.
         destruct H1.
         apply H in H1. apply H in H2. assert (R t u /\ R t v). split.
         apply H1. apply H2.
         specialize (H0 t u v H3). destruct H0. destruct H0.
         apply H in H0. apply H in H4.
         exists x. split; try apply H0; apply H4.
       Qed.

       End Relation.
