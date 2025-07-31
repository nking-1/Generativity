(** Enhanced NomegaProperties.v with better organization and additional theorems *)

Require Import DAO.Core.NomegaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.OmegaProperties.

(** ** Properties of NomegaType *)

Module NomegaProperties.

  (** * Basic Properties of Emptiness *)
  Module Core.
    
    (** Helper: The predicate "there exists no x" *)
    Definition no_witness {Nomega : NomegaType} (P : Nomegacarrier -> Prop) : Prop :=
      ~ exists x : Nomegacarrier, P x.
    
    (** For any predicate on Nomega, there are no witnesses *)
    Theorem nomega_no_witnesses {Nomega : NomegaType} : 
      forall P : Nomegacarrier -> Prop, no_witness P.
    Proof.
      intros P [x Hx].
      exact (nomega_emptiness x).
    Qed.

    (** Nomega has no decidable predicates (they're all vacuously false) *)
    Theorem nomega_all_predicates_empty {Nomega : NomegaType} :
      forall (P : Nomegacarrier -> Prop),
      (forall x, ~ P x).
    Proof.
      intros P x.
      destruct (nomega_emptiness x).
    Qed.

    (** The only subset of Nomega is itself *)
    Theorem nomega_only_subset_is_empty {Nomega : NomegaType} :
      forall (P Q : Nomegacarrier -> Prop),
      (forall x, P x -> Q x) ->
      (forall x, P x <-> Q x).
    Proof.
      intros P Q H_impl x.
      split.
      - exact (H_impl x).
      - intro Qx. destruct (nomega_emptiness x).
    Qed.
    
  End Core.

  (** * Triviality from Emptiness *)
  Module Triviality.
    
    (** From any element of Nomega, we can prove anything (ex falso) *)
    Theorem nomega_proves_anything {Nomega : NomegaType} : 
      forall (P : Nomegacarrier -> Prop),
      forall x : Nomegacarrier, P x.
    Proof.
      intros P x.
      destruct (nomega_emptiness x).
    Qed.

    (** This means we can prove both P and ~P for any element *)
    Theorem nomega_contradiction {Nomega : NomegaType} :
      forall (P : Nomegacarrier -> Prop),
      forall x : Nomegacarrier, P x /\ ~ P x.
    Proof.
      intros P x.
      split.
      - exact (nomega_proves_anything P x).
      - exact (nomega_proves_anything (fun x => ~ P x) x).
    Qed.

    (** In any trivial type, everything equals everything *)
    Definition trivial_equality {T : Type} (contradiction : T -> False) : 
      forall (x y : T), x = y.
    Proof.
      intros x y.
      destruct (contradiction x).
    Qed.
    
    (** All elements of Nomega are equal (vacuously true) *)
    Theorem nomega_all_equal {Nomega : NomegaType} :
      forall (x y : Nomegacarrier), x = y.
    Proof.
      exact (trivial_equality nomega_emptiness).
    Qed.
    
  End Triviality.

  (** * Functions from Empty Types *)

  Module EmptyTypeFunctions.

    (** A minimal axiom: functions from empty types are equal.
        This is much weaker than full functional extensionality. *)
    Axiom empty_function_ext : 
      forall {A B : Type} (empty : A -> False),
      forall (f g : A -> B), f = g.

    (** All functions from Nomega are equal *)
    Theorem nomega_function_unique {Nomega : NomegaType} :
      forall {A : Type} (f g : Nomegacarrier -> A), f = g.
    Proof.
      intros A f g.
    
      exact (empty_function_ext nomega_emptiness f g).
    Qed.
    
    (** Nomega is initial in the category of types: 
        there's a unique function from Nomega to any type *)
    Theorem nomega_initial {Nomega : NomegaType} :
      forall (A : Type), exists! (f : Nomegacarrier -> A), True.
    Proof.
      intro A.
      (* Existence *)
      exists (fun x => match nomega_emptiness x with end).
      split.
      - trivial.
      - (* Uniqueness *)
        intros g _.
        exact (nomega_function_unique _ g).
    Qed.
    
    (** Corollary: There's at most one function from Nomega to any type *)
    Corollary nomega_function_at_most_one {Nomega : NomegaType} :
      forall {A : Type} (f g : Nomegacarrier -> A), f = g.
    Proof.
      intros A f g.
      exact (nomega_function_unique f g).
    Qed.
    
  End EmptyTypeFunctions.

  (** * Categorical Properties *)
  Module Categorical.
    
    (** Products with Nomega are empty *)
    Theorem nomega_product_empty {Nomega : NomegaType} :
      forall (A : Type), 
        (exists x : Nomegacarrier * A, True) -> False.
    Proof.
      intros A [[n a] _].
      exact (nomega_emptiness n).
    Qed.

    (** Sums with Nomega reduce to the other type *)
    Theorem nomega_sum_reduces {Nomega : NomegaType} :
      forall (A : Type) (x : Nomegacarrier + A),
        exists a : A, x = inr a.
    Proof.
      intros A x.
      destruct x as [n | a].
      - destruct (nomega_emptiness n).
      - exists a. reflexivity.
    Qed.

    (** Nomega is strictly initial - there's exactly one morphism to any type *)
    Theorem nomega_strictly_initial {Nomega : NomegaType} :
      forall (A : Type) (f g : Nomegacarrier -> A),
      f = g.
    Proof.
      (* This would use EmptyTypeFunctions.nomega_function_unique *)
      intros A f g.
      exact (EmptyTypeFunctions.nomega_function_unique f g).
    Qed.

    (** Function composition with Nomega *)
    Theorem nomega_composition {Nomega : NomegaType} :
      forall {A B : Type} (f : A -> B) (g : Nomegacarrier -> A),
      exists! h : Nomegacarrier -> B, forall x, h x = f (g x).
    Proof.
      intros A B f g.
      exists (fun x => f (g x)).
      split.
      - intro x. reflexivity.
      - intros h Hh.
        apply EmptyTypeFunctions.nomega_function_unique.
    Qed.
    
  End Categorical.

  Module Characterization.
    (** Nomega is characterized by having no elements *)
    Theorem empty_iff_nomega {Nomega : NomegaType} :
      (forall x : Nomegacarrier, False) <->
      (forall P : Nomegacarrier -> Prop, ~ exists x, P x).
    Proof.
      split.
      - intros H_empty P [x Px].
        exact (H_empty x).
      - intros H_no_witness x.
        apply (H_no_witness (fun y => y = x)).
        exists x. reflexivity.
    Qed.
    
    (** Any type with no elements behaves like Nomega *)
    Theorem empty_type_isomorphic {Nomega : NomegaType} :
      forall (T : Type),
      (forall t : T, False) ->
      exists (f : Nomegacarrier -> T) (g : T -> Nomegacarrier),
      (forall n, g (f n) = n) /\ (forall t, f (g t) = t).
    Proof.
      intros T T_empty.
      exists (fun n => match nomega_emptiness n with end).
      exists (fun t => match T_empty t with end).
      split.
      - intro n. destruct (nomega_emptiness n).
      - intro t. destruct (T_empty t).
    Qed.
    
  End Characterization.

End NomegaProperties.

(** * Duality between Omega and Nomega *)

Module OmegaNomegaDuality.
  
  (** The fundamental duality: Omega has all witnesses, Nomega has none *)
  Theorem omega_nomega_duality {O : OmegaType} {N : NomegaType} :
    (* Omega: For every property, there exists a witness *)
    (forall P : Omegacarrier -> Prop, exists x, P x) /\
    (* Nomega: For every property, there exists no witness *)  
    (forall Q : Nomegacarrier -> Prop, ~ exists y, Q y).
  Proof.
    split.
    - exact omega_completeness.
    - exact NomegaProperties.Core.nomega_no_witnesses.
  Qed.

  (** Both extremes lead to logical collapse *)
  Theorem extremes_imply_triviality {O : OmegaType} {N : NomegaType} :
    (* From Omega we can derive False *)
    (exists (P : Omegacarrier -> Prop) (x : Omegacarrier), P x /\ ~ P x) /\
    (* From any Nomega element we can derive False *)
    (forall y : Nomegacarrier, False).
  Proof.
    split.
    - (* We need to provide both P and x *)
      exists (fun _ => True).
      destruct (OmegaProperties.Paradoxes.omega_has_paradoxes (fun _ => True)) as [x Hx].
      exists x. exact Hx.
    - exact nomega_emptiness.
  Qed.

  (** Both types validate all propositions about their elements *)
  Theorem omega_nomega_both_trivial {O : OmegaType} {N : NomegaType} :
    (* Omega proves everything through contradiction *)
    (forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x) /\
    (* Nomega proves everything through emptiness *)
    (forall (Q : Nomegacarrier -> Prop) (y : Nomegacarrier), Q y).
  Proof.
    split.
    - exact OmegaProperties.Triviality.omega_proves_anything.
    - exact NomegaProperties.Triviality.nomega_proves_anything.
  Qed.

  (** No morphism can exist from Omega to Nomega (would preserve witnesses) *)
  Theorem no_morphism_omega_to_nomega {O : OmegaType} {N : NomegaType} :
    ~ exists (f : Omegacarrier -> Nomegacarrier), True.
  Proof.
    intros [f _].
    destruct (OmegaProperties.Core.omega_not_empty) as [x _].
    exact (nomega_emptiness (f x)).
  Qed.

  (** But there's always a morphism from Nomega to Omega *)
  Theorem morphism_nomega_to_omega {O : OmegaType} {N : NomegaType} :
    exists (f : Nomegacarrier -> Omegacarrier), True.
  Proof.
    exists (fun n => match nomega_emptiness n with end).
    exact I.
  Qed.

  Theorem omega_inhabited_trivial {O : OmegaType} :
    (exists x : Omegacarrier, True) /\ (* inhabited *)
    (forall P : Prop, P).              (* trivial *)
  Proof.
    split.
    - exact OmegaProperties.Core.omega_not_empty.
    - exact OmegaProperties.Triviality.explosion.
  Qed.

  Theorem nomega_empty_trivial {N : NomegaType} :
    (~ exists x : Nomegacarrier, True) /\ (* empty *)
    (forall (P : Nomegacarrier -> Prop) x, P x). (* trivial about elements *)
  Proof.
    split.
    - intros [x _]. exact (nomega_emptiness x).
    - exact NomegaProperties.Triviality.nomega_proves_anything.
  Qed.

End OmegaNomegaDuality.

