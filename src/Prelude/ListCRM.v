Require Import List.
Import ListNotations.

Inductive forall_l {A : Type} (P : A -> Prop) : list A -> Prop :=
| forall_nil : forall_l P []
| forall_cons : forall {a : A} {l : list A},
    P a -> forall_l P l -> forall_l P (a :: l).

Lemma map_forall {A B : Type} :
  forall (P : A -> Prop) (Q : B -> Prop) (f : A -> B),
    (forall a : A, P a -> Q (f a)) ->
    forall l : list A, forall_l P l -> forall_l Q (map f l).
Proof.
  intros. induction l.
  - constructor.
  - simpl. inversion H0; subst. constructor.
    apply H. apply H3.
    apply IHl. apply H4.
Qed.

Lemma map_forall_rev {A B : Type} :
  forall (P : A -> Prop) (Q : B -> Prop) (f : A -> B),
    (forall a : A, Q (f a) -> P a) ->
    forall l : list A, forall_l Q (map f l) -> forall_l P l.
Proof.
  intros. induction l. constructor.
  inversion H0. subst. constructor.
  apply H. apply H3. apply IHl. apply H4.
Qed.

Lemma In_forall {A : Type} :
  forall (P : A -> Prop) (l : list A) (a : A),
    forall_l P l -> In a l -> P a.
Proof.
  intros. induction l. inversion H0.
  simpl in H0. destruct H0. subst.
  inversion H; subst. apply H2.
  apply IHl. inversion H; subst. apply H4.
  apply H0.
Qed.

Lemma forall_head {A : Type} :
  forall (P : A -> Prop) (l : list A) (a : A),
    forall_l P (a :: l) -> P a.
Proof.
  intros. inversion H. apply H2.
Qed.

Lemma forall_tail {A : Type} :
  forall (P : A -> Prop) (l : list A) (a : A),
    forall_l P (a :: l) -> forall_l P l.
Proof.
  intros. inversion H. apply H3.
Qed.
