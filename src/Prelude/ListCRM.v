Require Import List.
Import ListNotations.
From Stdlib Require Import Program.Equality.

Inductive forall_l {A : Type} (P : A -> Type) : list A -> Type :=
| forall_nil : forall_l P []
| forall_cons : forall {a : A} {l : list A},
    P a -> forall_l P l -> forall_l P (a :: l).

Inductive In_s {A : Type} : A -> list A -> Type :=
| In_hd : forall {a : A} {l : list A}, In_s a (a :: l)
| In_cs : forall {a b : A} {l : list A},
    In_s a l -> In_s a (b :: l).

Lemma map_forall {A B : Type} :
  forall (P : A -> Type) (Q : B -> Type) (f : A -> B),
    (forall a : A, P a -> Q (f a)) ->
    forall l : list A, forall_l P l -> forall_l Q (map f l).
Proof.
  intros. induction l.
  - constructor.
  - simpl. inversion X0; subst. constructor.
    apply X. apply X1.
    apply IHl. apply X2.
Defined.

Lemma map_forall_rev {A B : Type} :
  forall (P : A -> Type) (Q : B -> Type) (f : A -> B),
    (forall a : A, Q (f a) -> P a) ->
    forall l : list A, forall_l Q (map f l) -> forall_l P l.
Proof.
  intros. induction l. constructor.
  inversion X0. subst. constructor.
  apply X. apply X1. apply IHl. apply X2.
Defined.

Lemma In_forall {A : Type} :
  forall (P : A -> Type) (l : list A) (a : A),
    forall_l P l -> In_s a l -> P a.
Proof.
  intros. induction X0.
  inversion X. apply X0.
  apply IHX0. inversion X. apply X2.
Defined.

Lemma forall_head {A : Type} :
  forall (P : A -> Type) (l : list A) (a : A),
    forall_l P (a :: l) -> P a.
Proof.
  intros. inversion X. apply X0.
Defined.

Lemma forall_tail {A : Type} :
  forall (P : A -> Type) (l : list A) (a : A),
    forall_l P (a :: l) -> forall_l P l.
Proof.
  intros. inversion X. apply X1.
Defined.
