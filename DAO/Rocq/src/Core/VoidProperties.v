(** VoidProperties.v *)

Require Import DAO.Core.VoidType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.OmegaProperties.

(** ** Properties of VoidType *)

Module VoidProperties.

  (** * Basic Properties of Emptiness *)
  Module Core.
    
    (** Helper: The predicate "there exists no x" *)
    Definition no_witness {Void : VoidType} (P : Voidcarrier -> Prop) : Prop :=
      ~ exists x : Voidcarrier, P x.
    
    (** For any predicate on Void, there are no witnesses *)
    Theorem void_no_witnesses {Void : VoidType} : 
      forall P : Voidcarrier -> Prop, no_witness P.
    Proof.
      intros P [x Hx].
      exact (void_emptiness x).
    Qed.

    (** Void has no decidable predicates (they're all vacuously false) *)
    Theorem void_all_predicates_empty {Void : VoidType} :
      forall (P : Voidcarrier -> Prop),
      (forall x, ~ P x).
    Proof.
      intros P x.
      destruct (void_emptiness x).
    Qed.

    (** The only subset of Void is itself *)
    Theorem void_only_subset_is_empty {Void : VoidType} :
      forall (P Q : Voidcarrier -> Prop),
      (forall x, P x -> Q x) ->
      (forall x, P x <-> Q x).
    Proof.
      intros P Q H_impl x.
      split.
      - exact (H_impl x).
      - intro Qx. destruct (void_emptiness x).
    Qed.
    
  End Core.

  (** * Triviality from Emptiness *)
  Module Triviality.
    
    (** From any element of Void, we can prove anything (ex falso) *)
    Theorem void_proves_anything {Void : VoidType} : 
      forall (P : Voidcarrier -> Prop),
      forall x : Voidcarrier, P x.
    Proof.
      intros P x.
      destruct (void_emptiness x).
    Qed.

    (** This means we can prove both P and ~P for any element *)
    Theorem void_contradiction {Void : VoidType} :
      forall (P : Voidcarrier -> Prop),
      forall x : Voidcarrier, P x /\ ~ P x.
    Proof.
      intros P x.
      split.
      - exact (void_proves_anything P x).
      - exact (void_proves_anything (fun x => ~ P x) x).
    Qed.

    (** In any trivial type, everything equals everything *)
    Definition trivial_equality {T : Type} (contradiction : T -> False) : 
      forall (x y : T), x = y.
    Proof.
      intros x y.
      destruct (contradiction x).
    Qed.
    
    (** All elements of Void are equal (vacuously true) *)
    Theorem void_all_equal {Void : VoidType} :
      forall (x y : Voidcarrier), x = y.
    Proof.
      exact (trivial_equality void_emptiness).
    Qed.
    
  End Triviality.

  (** * Functions from Empty Types *)

  Module EmptyTypeFunctions.

    (** A minimal axiom: functions from empty types are equal.
        This is weaker than full functional extensionality. *)
    Local Axiom empty_function_ext : 
      forall {A B : Type} (empty : A -> False),
      forall (f g : A -> B), f = g.

    (** All functions from Void are equal *)
    Theorem void_function_unique {Void : VoidType} :
      forall {A : Type} (f g : Voidcarrier -> A), f = g.
    Proof.
      intros A f g.
    
      exact (empty_function_ext void_emptiness f g).
    Qed.
    
    (** Void is initial in the category of types: 
        there's a unique function from Void to any type *)
    Theorem void_initial {Void : VoidType} :
      forall (A : Type), exists! (f : Voidcarrier -> A), True.
    Proof.
      intro A.
      (* Existence *)
      exists (fun x => match void_emptiness x with end).
      split.
      - trivial.
      - (* Uniqueness *)
        intros g _.
        exact (void_function_unique _ g).
    Qed.
    
    (** Corollary: There's at most one function from Void to any type *)
    Corollary void_function_at_most_one {Void : VoidType} :
      forall {A : Type} (f g : Voidcarrier -> A), f = g.
    Proof.
      intros A f g.
      exact (void_function_unique f g).
    Qed.
    
  End EmptyTypeFunctions.

  (** * Categorical Properties *)
  Module Categorical.
    
    (** Products with Void are empty *)
    Theorem void_product_empty {Void : VoidType} :
      forall (A : Type), 
        (exists x : Voidcarrier * A, True) -> False.
    Proof.
      intros A [[n a] _].
      exact (void_emptiness n).
    Qed.

    (** Sums with Void reduce to the other type *)
    Theorem void_sum_reduces {Void : VoidType} :
      forall (A : Type) (x : Voidcarrier + A),
        exists a : A, x = inr a.
    Proof.
      intros A x.
      destruct x as [n | a].
      - destruct (void_emptiness n).
      - exists a. reflexivity.
    Qed.

    (** Void is strictly initial - there's exactly one morphism to any type *)
    Theorem void_strictly_initial {Void : VoidType} :
      forall (A : Type) (f g : Voidcarrier -> A),
      f = g.
    Proof.
      (* This would use EmptyTypeFunctions.void_function_unique *)
      intros A f g.
      exact (EmptyTypeFunctions.void_function_unique f g).
    Qed.

    (** Function composition with Void *)
    Theorem void_composition {Void : VoidType} :
      forall {A B : Type} (f : A -> B) (g : Voidcarrier -> A),
      exists! h : Voidcarrier -> B, forall x, h x = f (g x).
    Proof.
      intros A B f g.
      exists (fun x => f (g x)).
      split.
      - intro x. reflexivity.
      - intros h Hh.
        apply EmptyTypeFunctions.void_function_unique.
    Qed.
    
  End Categorical.

  Module Characterization.
    (** Void is characterized by having no elements *)
    Theorem empty_iff_void {Void : VoidType} :
      (forall x : Voidcarrier, False) <->
      (forall P : Voidcarrier -> Prop, ~ exists x, P x).
    Proof.
      split.
      - intros H_empty P [x Px].
        exact (H_empty x).
      - intros H_no_witness x.
        apply (H_no_witness (fun y => y = x)).
        exists x. reflexivity.
    Qed.
    
    (** Any type with no elements behaves like Void *)
    Theorem empty_type_isomorphic {Void : VoidType} :
      forall (T : Type),
      (forall t : T, False) ->
      exists (f : Voidcarrier -> T) (g : T -> Voidcarrier),
      (forall n, g (f n) = n) /\ (forall t, f (g t) = t).
    Proof.
      intros T T_empty.
      exists (fun n => match void_emptiness n with end).
      exists (fun t => match T_empty t with end).
      split.
      - intro n. destruct (void_emptiness n).
      - intro t. destruct (T_empty t).
    Qed.
    
  End Characterization.

End VoidProperties.

(** * Duality between Omega and Void *)

Module OmegaVoidDuality.
  
  (** The fundamental duality: Omega has all witnesses, Void has none *)
  Theorem omega_void_duality {O : OmegaType} {N : VoidType} :
    (* Omega: For every property, there exists a witness *)
    (forall P : Omegacarrier -> Prop, exists x, P x) /\
    (* Void: For every property, there exists no witness *)  
    (forall Q : Voidcarrier -> Prop, ~ exists y, Q y).
  Proof.
    split.
    - exact omega_completeness.
    - exact VoidProperties.Core.void_no_witnesses.
  Qed.

  (** Both extremes lead to logical collapse *)
  Theorem extremes_imply_triviality {O : OmegaType} {N : VoidType} :
    (* From Omega we can derive False *)
    (exists (P : Omegacarrier -> Prop) (x : Omegacarrier), P x /\ ~ P x) /\
    (* From any Void element we can derive False *)
    (forall y : Voidcarrier, False).
  Proof.
    split.
    - (* We need to provide both P and x *)
      exists (fun _ => True).
      destruct (OmegaProperties.Paradoxes.omega_has_paradoxes (fun _ => True)) as [x Hx].
      exists x. exact Hx.
    - exact void_emptiness.
  Qed.

  (** Both types validate all propositions about their elements *)
  Theorem omega_void_both_trivial {O : OmegaType} {N : VoidType} :
    (* Omega proves everything through contradiction *)
    (forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x) /\
    (* Void proves everything through emptiness *)
    (forall (Q : Voidcarrier -> Prop) (y : Voidcarrier), Q y).
  Proof.
    split.
    - exact OmegaProperties.Triviality.omega_proves_anything.
    - exact VoidProperties.Triviality.void_proves_anything.
  Qed.

  (** No morphism can exist from Omega to Void (would preserve witnesses) *)
  Theorem no_morphism_omega_to_void {O : OmegaType} {N : VoidType} :
    ~ exists (f : Omegacarrier -> Voidcarrier), True.
  Proof.
    intros [f _].
    destruct (OmegaProperties.Core.omega_not_empty) as [x _].
    exact (void_emptiness (f x)).
  Qed.

  (** But there's always a morphism from Void to Omega *)
  Theorem morphism_void_to_omega {O : OmegaType} {N : VoidType} :
    exists (f : Voidcarrier -> Omegacarrier), True.
  Proof.
    exists (fun n => match void_emptiness n with end).
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

  Theorem void_empty_trivial {N : VoidType} :
    (~ exists x : Voidcarrier, True) /\ (* empty *)
    (forall (P : Voidcarrier -> Prop) x, P x). (* trivial about elements *)
  Proof.
    split.
    - intros [x _]. exact (void_emptiness x).
    - exact VoidProperties.Triviality.void_proves_anything.
  Qed.

End OmegaVoidDuality.

