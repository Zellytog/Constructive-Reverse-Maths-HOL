From Stdlib Require Import PeanoNat List.

Record EFData : Type :=
  { E : Type
  ; Φ : Type
  ; rel : E -> Φ -> Φ -> Prop
  ; p_top : Φ
  ; e_top : E
  ; e_is_top :
    forall {φ : Φ}, rel e_top φ p_top
  ; e_id : E
  ; e_is_id :
    forall {φ : Φ}, rel e_id φ φ
  ; e_comp : E -> E -> E
  ; e_is_comp :
    forall {φ : Φ} (ψ : Φ) {χ : Φ} {e e' : E},
      rel e φ ψ -> rel e' ψ χ -> rel (e_comp e e') φ χ
  ; p_pair : Φ -> Φ -> Φ
  ; e_pair : E -> E -> E
  ; e_fst : E
  ; e_snd : E
  ; e_is_fst :
    forall {φ ψ : Φ}, rel e_fst (p_pair φ ψ) φ
  ; e_is_snd :
    forall {φ ψ : Φ}, rel e_snd (p_pair φ ψ) ψ
  ; e_is_pair :
    forall {φ ψ χ : Φ} {e e' : E},
      rel e φ ψ -> rel e' φ χ ->
      rel (e_pair e e') φ (p_pair ψ χ)
  ; p_forall : (Φ -> Prop) -> Φ
  ; e_incl : E
  ; e_is_forall :
    forall {φ : Φ} {Ψ : Φ -> Prop} {e : E},
      (forall ψ : Φ, Ψ ψ -> rel e φ ψ) ->
      rel e φ (p_forall Ψ)
  ; e_is_incl :
    forall {Ψ : Φ -> Prop} {ψ : Φ},
      Ψ ψ -> rel e_incl (p_forall Ψ) ψ
  ; p_imp : Φ -> Φ -> Φ
  ; e_abs : E -> E
  ; e_eval : E
  ; e_is_abs :
    forall {φ ψ χ : Φ} {e : E},
      rel e (p_pair φ ψ) χ -> rel (e_abs e) φ (p_imp ψ χ)
  ; e_is_eval :
    forall {φ ψ : Φ},
      rel e_eval (p_pair (p_imp φ ψ) φ) ψ
  ; code_nat : nat -> Φ
  ; e_Z : E
  ; e_is_Z : rel e_Z p_top (code_nat 0)
  ; e_S : E
  ; e_is_S :
    forall n : nat, rel e_S (code_nat n) (code_nat (S n))
  ; e_rec : E
  ; e_is_rec :
    forall X : nat -> Φ,
      rel e_rec p_top (p_imp (X 0)
        (p_imp
           (p_forall
              (fun z =>
                 exists n : nat,
                   p_imp (code_nat n) (p_imp (X n) (X (S n))) = z))
           (p_forall (fun z => exists n : nat,
                          p_imp (code_nat n) (X n) = z))))
  }.

Section Properties.

  Variable ℰ : EFData.

  Notation "e ⊩ φ ≤ ψ" := (rel ℰ e φ ψ) (at level 87).
  Notation "φ ∧ₑ ψ" := (p_pair ℰ φ ψ) (at level 85, right associativity).
  Notation "φ ⊃ ψ" := (p_imp ℰ φ ψ) (at level 86, right associativity).
  Notation "e ⊪ φ" := (rel ℰ e (p_top ℰ) φ) (at level 87).
  Notation "e @ₑ e'" := (e_comp ℰ (e_pair ℰ e e') (e_eval ℰ)) (at level 84, left associativity).
  Notation "e ;ₑ e'" := (e_comp ℰ e e') (at level 83).
  Notation "⌜ n ⌝" := (code_nat ℰ n).

  Definition e_weaken (e : E ℰ) : E ℰ :=
    e_abs ℰ (e_fst ℰ ;ₑ e).
  
  Lemma e_is_weaken :
    forall (φ ψ₀ ψ₁ : Φ ℰ) (e : E ℰ),
      e ⊩ φ ≤ ψ₁ -> 
      e_weaken e ⊩ φ ≤ ψ₀ ⊃ ψ₁.
  Proof.
    intros.
    apply e_is_abs.
    apply (e_is_comp ℰ φ).
    apply e_is_fst.
    apply H.
  Qed.

  Definition e_lam (e : E ℰ) : E ℰ :=
    e_pair ℰ (e_top ℰ ;ₑ e) (e_id ℰ) ;ₑ e_eval ℰ.

  Lemma e_is_lam :
    forall {φ ψ : Φ ℰ} {e : E ℰ},
      e ⊪ φ ⊃ ψ -> e_lam e ⊩ φ ≤ ψ.
  Proof.
    intros.
    apply (e_is_comp ℰ (p_pair ℰ (φ ⊃ ψ) φ)).
    apply e_is_pair.
    apply (e_is_comp ℰ (p_top ℰ)).
    apply e_is_top.
    apply H.
    apply e_is_id.
    apply e_is_eval.
  Qed.

  Notation ƛₑ := e_lam.

  Definition log_le (φ ψ : Φ ℰ) : Prop :=
    exists (e : E ℰ), e ⊩ φ ≤ ψ.

  Definition log_eq (φ ψ : Φ ℰ) : Prop :=
    log_le φ ψ /\ log_le ψ φ.

  Definition push_in_powerset {A : Type} (f : A -> Φ ℰ) : Φ ℰ :=
    p_forall ℰ (fun φ => exists a : A, f a = φ).

  Notation "⋂" := (push_in_powerset).
  
  Lemma e_is_for_pow :
    forall {A : Type} {φ : Φ ℰ} {Ψ : A -> Φ ℰ} {e : E ℰ},
      (forall a : A, rel ℰ e φ (Ψ a)) ->
      rel ℰ e φ (⋂ Ψ).
  Proof.
    intros. apply e_is_forall.
    intros ψ [a Ha].
    specialize (H a).
    rewrite <- Ha. apply H.
  Qed.

  Lemma e_is_incl_pow :
    forall {A : Type} {Ψ : A -> Φ ℰ} {a : A},
      rel ℰ (e_incl ℰ) (⋂ Ψ) (Ψ a).
  Proof.
    intros. apply e_is_incl. exists a.
    reflexivity.
  Qed.

  Definition p_bot : Φ ℰ := p_forall ℰ (fun _ => True).

  Definition p_or (φ ψ : Φ ℰ) : Φ ℰ :=
    ⋂ (fun χ => (φ ⊃ χ) ⊃ (ψ ⊃ χ) ⊃ χ).

  Lemma appli : forall {e e' : E ℰ} (φ : Φ ℰ)
                       {ψ : Φ ℰ},
      e ⊪ φ ⊃ ψ -> e' ⊪ φ -> e @ₑ e' ⊪ ψ.
  Proof.
    intros. unfold "@ₑ".
    apply (e_is_comp ℰ (p_pair ℰ (φ ⊃ ψ) φ)).
    apply e_is_pair. apply H. apply H0.
    apply e_is_eval.
  Qed.

  Definition e_abstract (e : E ℰ) : E ℰ :=
    e_abs ℰ (e_snd ℰ ;ₑ e).

  Lemma e_is_abstract : forall {e : E ℰ} (φ ψ: Φ ℰ),
      e ⊩ φ ≤ ψ -> e_abstract e ⊪ φ ⊃ ψ.
  Proof.
    intros.
    apply (e_is_abs ℰ).
    apply (e_is_comp ℰ φ).
    apply e_is_snd.
    apply H.
  Qed.

  Lemma advance : forall (e e' : E ℰ) (φ ψ : Φ ℰ),
      e ⊩ φ ≤ ψ -> e' ⊪ φ -> e' ;ₑ e ⊪ ψ.
  Proof. intros. apply (e_is_comp ℰ φ). apply H0. apply H. Qed.

  Lemma recur : forall (X : nat -> Φ ℰ) (e e' : E ℰ),
      e ⊪ X 0 -> e' ⊪ ⋂ (fun n => ⌜ n ⌝ ⊃ (X n) ⊃ (X (S n))) ->
      e_rec ℰ @ₑ e @ₑ e' ⊪ ⋂ (fun n => ⌜ n ⌝ ⊃ X n).
  Proof.
    intros. specialize (e_is_rec ℰ X) as H1.
    apply (appli (⋂ (fun n => ⌜ n ⌝ ⊃ (X n ⊃ X (S n))))).
    apply (appli (X 0)).
    apply H1.
    apply H. apply H0.
  Qed.

  Lemma bot_elim : forall {φ : Φ ℰ},
      e_incl ℰ ⊩ p_bot ≤ φ.
  Proof. intros. apply e_is_incl. trivial. Qed.

  Fixpoint p_meet_list (Γ : list (Φ ℰ)) : Φ ℰ :=
    match Γ with
    | nil => p_top ℰ
    | φ :: Δ => p_pair ℰ (p_meet_list Δ) φ
    end.

  Fixpoint e_proj (n : nat) : E ℰ :=
    match n with
    | 0 => e_snd ℰ
    | S m => e_comp ℰ (e_fst ℰ) (e_proj m)
    end.

  Inductive bind : list (Φ ℰ) -> Φ ℰ -> nat ->Prop :=
  | bind_hd : forall {φ : Φ ℰ} {Γ : list (Φ ℰ)}, bind (φ :: Γ) φ 0
  | bind_tl : forall {φ ψ : Φ ℰ} {Γ : list (Φ ℰ)} {n : nat},
      bind Γ φ n -> bind (ψ :: Γ) φ (S n).

  Lemma meet_is_lb :
    forall (Γ : list (Φ ℰ)) (φ : Φ ℰ) (n : nat),
      bind Γ φ n ->
      e_proj n ⊩ p_meet_list Γ ≤ φ.
  Proof.
    intros. induction H.
    simpl. apply e_is_snd.
    simpl. apply (e_is_comp ℰ (p_meet_list Γ)).
    apply e_is_fst. apply IHbind.
  Qed.

  Inductive is_bounding : (list (E ℰ)) -> (list (Φ ℰ)) -> Φ ℰ-> Prop :=
  | is_bounding_nil : forall {φ : Φ ℰ}, is_bounding nil nil φ
  | is_bounding_cons : forall {es : list (E ℰ)} {Γ : list (Φ ℰ)}
                              {φ : Φ ℰ} {e : E ℰ} {ψ : Φ ℰ},
      is_bounding es Γ φ -> e ⊩ φ ≤ ψ ->
      is_bounding (e :: es) (ψ :: Γ) φ.

  Fixpoint list_to_evid (es : list (E ℰ)) : E ℰ :=
    match es with
    | nil => e_top ℰ
    | e :: es' =>
        e_pair ℰ (list_to_evid es') e
    end.

  Lemma meet_is_inf :
    forall (Γ : list (Φ ℰ)) (ψ : Φ ℰ) (es : list (E ℰ)),
      is_bounding es Γ ψ ->
      list_to_evid es ⊩ ψ ≤ p_meet_list Γ.
  Proof.
    intros. induction H.
    simpl. apply e_is_top.
    simpl. apply e_is_pair.
    apply IHis_bounding. apply H0.
  Qed.

  Lemma adj_meet_impl_to_right :
    forall (Γ : list (Φ ℰ)) (φ ψ : Φ ℰ) (e : E ℰ),
      e ⊩ p_meet_list (φ :: Γ) ≤ ψ ->
      e_abs ℰ e ⊩ p_meet_list Γ ≤ φ ⊃ ψ.
  Proof.
    intros. simpl in H. apply e_is_abs.
    apply H.
  Qed.

  Lemma adj_meet_impl_to_left :
    forall (Γ : list (Φ ℰ)) (φ ψ : Φ ℰ) (e : E ℰ),
      e ⊩ p_meet_list Γ ≤ φ ⊃ ψ ->
      ((e_fst ℰ) ;ₑ e) @ₑ (e_snd ℰ) ⊩ p_meet_list (φ :: Γ) ≤ ψ.
  Proof.
    intros.
    apply (e_is_comp ℰ ((φ ⊃ ψ) ∧ₑ φ)).
    apply e_is_pair. apply (e_is_comp ℰ (p_meet_list Γ)).
    apply e_is_fst. apply H.
    apply e_is_snd.
    apply e_is_eval.
  Qed.

  Lemma p_f_intro :
    forall (φ : Φ ℰ) (e : E ℰ) {A : Type}
           (Ψ : A -> Φ ℰ),
      (forall a : A, e ⊩ φ ≤ Ψ a) ->
      e ⊩ φ ≤ ⋂ Ψ.
  Proof.
    intros. apply e_is_for_pow. apply H.
  Qed.

  Lemma p_f_elim :
    forall (φ : Φ ℰ) (e : E ℰ) {A : Type}
           (Ψ : A -> Φ ℰ) (a : A),
      e ⊩ φ ≤ ⋂ Ψ -> e ;ₑ e_incl ℰ ⊩ φ ≤ Ψ a.
  Proof.
    intros. apply (e_is_comp ℰ (⋂ Ψ)).
    apply H. apply e_is_incl.
    exists a. reflexivity.
  Qed.

  Definition code_bool (b : bool) : Φ ℰ :=
    match b with
    | true => code_nat ℰ 0
    | false => code_nat ℰ 1
    end.

  Notation "⌜ b ⌝ᵇ" := (code_bool b).

  Lemma e_is_cod_true : e_Z ℰ ;ₑ e_S ℰ ⊪ ⌜ false ⌝ᵇ.
  Proof.
    unfold code_bool; simpl. apply (advance _ _ ⌜ 0 ⌝).
    apply e_is_S. apply e_is_Z.
  Qed.

  Lemma e_is_cod_false : e_Z ℰ ⊪ ⌜ true ⌝ᵇ.
  Proof.
    intros. apply e_is_Z.
  Qed.

  Definition e_recB (e e' : E ℰ) : E ℰ :=
    (e_rec ℰ @ₑ e @ₑ e_weaken (e_weaken e')) ;ₑ (e_incl ℰ).
  
  Lemma e_is_recB :
      forall (Ψ : bool -> Φ ℰ) (e e' : E ℰ),
        e ⊪ Ψ true -> e' ⊪ Ψ false ->
        e_recB e e' ⊪ ⋂ (fun b => ⌜ b ⌝ᵇ ⊃ Ψ b).
  Proof.
    intros.
    pose (f := fun n => match n with
                          0 => Ψ true | S _ => Ψ false end).
    specialize (recur f e (e_weaken (e_weaken e'))) as Hf.
    assert (e ⊪ f 0). simpl. apply H.
    specialize (Hf H1); clear H1.
    assert (e_weaken (e_weaken e') ⊪
              ⋂ (fun n => ⌜ n ⌝ ⊃ f n ⊃ f (S n))).
    apply e_is_for_pow.
    intro n; simpl.
    apply e_is_weaken. apply e_is_weaken. apply H0.
    specialize (Hf H1); clear H1.
    unfold code_bool.
    unfold f in Hf.
    apply e_is_for_pow.
    intro b; case b.
    apply (e_is_comp ℰ
             (⋂ (fun n => ⌜ n ⌝ ⊃ f n))).
    apply Hf.
    apply e_is_incl.
    exists 0. reflexivity.
    apply (e_is_comp ℰ
             (⋂ (fun n => ⌜ n ⌝ ⊃ f n))).
    apply Hf.
    apply e_is_incl.
    exists 1. reflexivity.
  Qed.

  Definition code_fun {A B : Type}
    (codA : A -> Φ ℰ) (codB : B -> Φ ℰ) (f : A -> B) : Φ ℰ :=
    ⋂ (fun a => codA a ⊃ codB (f a)).

  Lemma e_is_fun_intro :
    forall {A B : Type} (codA : A -> Φ ℰ) (codB : B -> Φ ℰ)
           (f : A -> B) (e : E ℰ),
      (forall a : A, e ⊩ codA a ≤ codB (f a)) ->
      e_abstract e ⊪ code_fun codA codB f.
  Proof.
    intros. apply e_is_forall.
    intros ψ Ha.
    destruct Ha as [a Hψ]; subst.
    apply e_is_abstract. apply H.
  Qed.

  Lemma e_is_fun_elim :
    forall {A B : Type} (codA : A -> Φ ℰ) (codB : B -> Φ ℰ)
           (f : A -> B) (e e' : E ℰ) (a : A),
      e ⊪ code_fun codA codB f -> e' ⊪ codA a ->
      (e ;ₑ e_incl ℰ) @ₑ e' ⊪ codB (f a).
  Proof.
    intros.
    apply (appli (codA a)).
    apply (e_is_comp ℰ
             (⋂ (fun a => codA a ⊃ codB (f a)))).
    apply H. apply e_is_incl.
    exists a. reflexivity.
    apply H0.
  Qed.

  Definition code_prod {A B : Type}
    (codA : A -> Φ ℰ) (codB : B -> Φ ℰ) (α : A * B) : Φ ℰ :=
    match α with
    | pair a b => (codA a) ∧ₑ (codB b)
    end.

  Lemma e_is_pair_intro :
    forall {A B : Type} (codA : A -> Φ ℰ) (codB : B -> Φ ℰ)
           (e e' : E ℰ) (a : A) (b : B),
      e ⊪ codA a -> e' ⊪ codB b ->
      e_pair ℰ e e' ⊪ code_prod codA codB (a,b).
  Proof.
    intros. apply e_is_pair; assumption.
  Qed.

  Lemma e_is_fst_elim :
    forall {A B : Type} (codA : A -> Φ ℰ) (codB : B -> Φ ℰ)
           (e : E ℰ) (a : A) (b : B),
      e ⊪ code_prod codA codB (a, b) ->
      e ;ₑ e_fst ℰ ⊪ codA a.
  Proof.
    intros. apply (e_is_comp ℰ (code_prod codA codB (a , b))).
    apply H. apply e_is_fst.
  Qed.

  Lemma e_is_snd_elim :
    forall {A B : Type} (codA : A -> Φ ℰ) (codB : B -> Φ ℰ)
           (e : E ℰ) (a : A) (b : B),
      e ⊪ code_prod codA codB (a, b) ->
      e ;ₑ e_snd ℰ ⊪ codB b.
  Proof.
    intros. apply (e_is_comp ℰ (code_prod codA codB (a , b))).
    apply H. apply e_is_snd.
  Qed.
  
  Fixpoint code_list {A : Type} (code : A -> Φ ℰ)
    (l : list A) : Φ ℰ :=
    match l with
    | nil => p_pair ℰ (code_nat ℰ 0) (p_top ℰ)
    | cons a l' =>
        p_pair ℰ (code_nat ℰ (length l))
          (p_pair ℰ (code a) (code_list code l'))
    end.

  Lemma code_length :
    forall {A : Type} (codA : A -> Φ ℰ) (l : list A),
      e_fst ℰ ⊩ code_list codA l ≤ ⌜ length l ⌝.
  Proof.
    intros. case l eqn : e; apply e_is_fst.
  Qed.

  Definition e_nil : E ℰ := e_pair ℰ (e_Z ℰ) (e_id ℰ).

  Lemma e_is_nil :
    forall {A : Type} (codA : A -> Φ ℰ),
      e_nil ⊪ code_list codA nil.
  Proof.
    intros. apply e_is_pair. apply e_is_Z. apply e_is_id.
  Qed.

  Definition e_cons (e e' : E ℰ) : E ℰ :=
    e_pair ℰ (e' ;ₑ e_fst ℰ ;ₑ e_S ℰ)
      (e_pair ℰ e e').

  Lemma e_is_cons :
    forall {A : Type} (codA : A -> Φ ℰ) (a : A)
           (l : list A) (ea el : E ℰ),
      ea ⊪ codA a -> el ⊪ code_list codA l ->
      e_cons ea el ⊪ code_list codA (a ::l).
  Proof.
    intros.
    simpl.
    apply e_is_pair.
    apply (e_is_comp ℰ ⌜ length l ⌝).
    apply (e_is_comp ℰ (code_list codA l)).
    apply H0. apply code_length.
    apply e_is_S.
    case l eqn : e.
    apply e_is_pair.
    apply H. apply H0.
    apply e_is_pair.
    apply H. apply H0.
  Qed.
    
End Properties.
