Require Import PeanoNat.

Record EF : Type :=
  { E : Type
  ; Φ : Type
  ; rel : E -> Φ -> Φ -> Prop
  ; p_top : Φ
  ; e_top : E
  ; e_is_top :
    forall (φ : Φ), rel e_top φ p_top
  ; e_id : E
  ; e_is_id :
    forall (φ : Φ), rel e_id φ φ
  ; e_comp : E -> E -> E
  ; e_is_comp :
    forall (φ ψ χ : Φ) (e e' : E),
      rel e φ ψ -> rel e' ψ χ -> rel (e_comp e e') φ χ
  ; p_pair : Φ -> Φ -> Φ
  ; e_pair : E -> E -> E
  ; e_fst : E
  ; e_snd : E
  ; e_is_fst :
    forall (φ ψ : Φ), rel e_fst (p_pair φ ψ) φ
  ; e_is_snd :
    forall (φ ψ : Φ), rel e_snd (p_pair φ ψ) ψ
  ; e_is_pair :
    forall (φ ψ χ : Φ) (e e' : E),
      rel e φ ψ -> rel e' φ χ ->
      rel (e_pair e e') φ (p_pair ψ χ)
  ; p_forall : (Φ -> Prop) -> Φ
  ; e_incl : E
  ; e_is_forall :
    forall (φ : Φ) (Ψ : Φ -> Prop) (e : E),
      (forall ψ : Φ, Ψ ψ -> rel e φ ψ) ->
      rel e φ (p_forall Ψ)
  ; e_is_incl :
    forall (Ψ : Φ -> Prop) (ψ : Φ),
      Ψ ψ -> rel e_incl (p_forall Ψ) ψ
  ; p_imp : Φ -> Φ -> Φ
  ; e_abs : E -> E
  ; e_eval : E
  ; e_is_abs :
    forall (φ ψ χ : Φ) (e : E),
      rel e (p_pair φ ψ) χ -> rel (e_abs e) φ (p_imp ψ χ)
  ; e_is_eval :
    forall (φ ψ : Φ),
      rel e_eval (p_pair (p_imp φ ψ) φ) ψ
  }.

Section Properties.

  Variable ℰ : EF.

  Notation "e ⊩ φ ≤ ψ" := (rel ℰ e φ ψ) (at level 87).
  Notation "φ ∧ₑ ψ" := (p_pair ℰ φ ψ) (at level 85, right associativity).
  Notation "φ ⊃ ψ" := (p_imp ℰ φ ψ) (at level 86, right associativity).

  Definition log_le (φ ψ : Φ ℰ) : Prop :=
    exists (e : E ℰ), e ⊩ φ ≤ ψ.

  Definition push_in_powerset {A : Type} (f : A -> Φ ℰ) : Φ ℰ :=
    p_forall ℰ (fun φ => exists a : A, f a = φ).

  Notation "⋂" := (push_in_powerset).

  Definition p_bot : Φ ℰ := p_forall ℰ (fun _ => True).

  Definition p_or (φ ψ : Φ ℰ) : Φ ℰ :=
    ⋂ (fun χ => (φ ⊃ χ) ⊃ (ψ ⊃ χ) ⊃ χ).

End Properties.
