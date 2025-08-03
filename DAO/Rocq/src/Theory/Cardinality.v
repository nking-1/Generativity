(** Cardinality.v: Reasoning about relative "sizes"
    of types in the DAO framework
*)

Require Import DAO.Core.GenerativeType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Core.Bridge.

(* Injectivity and cardinality definitions remain the same *)
Definition injective {A B: Type} (f: A -> B) : Prop :=
  forall x y: A, f x = f y -> x = y.

Definition aleph_0 := nat.

Fixpoint aleph_n (n : nat) : Type :=
  match n with
  | 0 => aleph_0
  | S n' => { A : Type & A -> aleph_n n' }
  end.

(* Hash function remains the same *)
Parameter hash : forall {X : Type}, X -> nat.

(* The encoding for GenerativeType - turns an element x : X into a meta-predicate *)
Definition encode_with_hash_gen {Alpha : AlphaType} {HG : GenerativeType Alpha} {X : Type} 
  (x : X) : (Alphacarrier -> Prop) -> Prop :=
  fun P => forall Q : (Alphacarrier -> Prop) -> Prop, 
    (Q P <-> exists n : nat, n = hash x).

(* Axiom stating that our encoding preserves distinctness *)
Axiom encode_with_hash_gen_injective : 
  forall {Alpha : AlphaType} {HG : GenerativeType Alpha} {X : Type} (x y : X),
  self_ref_pred_embed (encode_with_hash_gen x) = 
  self_ref_pred_embed (encode_with_hash_gen y) -> x = y.

(* Theorem: GenerativeType contains an injective copy of the nth aleph cardinal *)
Theorem gen_larger_than_aleph_n :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha),
  forall n : nat,
  exists (f : aleph_n n -> (Alphacarrier -> Prop)), injective f.
Proof.
  intros Alpha HG n.
  exists (fun x => self_ref_pred_embed (encode_with_hash_gen x)).
  unfold injective.
  intros x1 x2 Heq.
  apply encode_with_hash_gen_injective.
  exact Heq.
Qed.

Parameter strictly_larger : Type -> Type -> Prop.

(* Intuition: X strictly larger than Y means there is no injective mapping from X into Y *)
Axiom strictly_larger_no_injection :
  forall (X Y : Type),
    strictly_larger X Y ->
      ~ exists (f : X -> Y), (forall x1 x2, f x1 = f x2 -> x1 = x2).

(* Theorem: Omega is larger than GenerativeType *)
Theorem omega_larger_than_gen :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha)
         (Omega : OmegaType)
         (HOG : OmegaToGenerative Alpha HG Omega),
    exists (f : (Alphacarrier -> Prop) -> Omegacarrier),
    exists (x : Omegacarrier),
      forall (P : Alphacarrier -> Prop), f P <> x.
Proof.
  intros Alpha HG Omega HOG.
  
  (* Use lift_Gen as our function *)
  pose proof (@lift_Gen Alpha HG Omega HOG) as f.
  
  (* Define the predicate for omega_completeness *)
  set (Pred := fun (x : Omegacarrier) => 
    forall P : Alphacarrier -> Prop, f P <> x).
  
  (* Apply omega_completeness *)
  pose proof (@omega_completeness Omega Pred) as [x Hx].
  
  exists f, x.
  exact Hx.
Qed.

(* embed the fact that we can encode aleph_n *)
Theorem gen_embeds_aleph_encoding :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha),
  forall n : nat,
  exists t : nat,
    contains t (self_ref_pred_embed 
      (fun _ => exists (f : aleph_n n -> (Alphacarrier -> Prop)), 
        injective f)).
Proof.
  intros Alpha HG n.
  destruct (self_ref_generation_exists 
    (fun _ => exists (f : aleph_n n -> (Alphacarrier -> Prop)), 
      injective f) 0)
    as [t [_ Ht]].
  exists t. exact Ht.
Qed.

(* GenerativeType contains statements about transfinite cardinals *)
Theorem gen_reasons_about_infinity :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha),
  exists t : nat,
    contains t (self_ref_pred_embed
      (fun P => forall n : nat, 
        exists (f : aleph_n n -> (Alphacarrier -> Prop)), 
        injective f)).
Proof.
  intros Alpha HG.
  destruct (self_ref_generation_exists
    (fun P => forall n : nat, 
      exists (f : aleph_n n -> (Alphacarrier -> Prop)), 
      injective f) 0)
    as [t [_ Ht]].
  exists t. exact Ht.
Qed.

Theorem Omega_contains_set_larger_than_itself :
  forall (Omega : OmegaType),
    exists (X : Type) (embed_X_in_Omega : X -> Omegacarrier),
      strictly_larger X Omegacarrier.
Proof.
  intros Omega.

  (* Define the paradoxical predicate explicitly *)
  set (P := fun (_ : Omegacarrier) =>
    exists (X : Type) (embed_X_in_Omega : X -> Omegacarrier),
      strictly_larger X Omegacarrier).

  (* Omega completeness ensures this paradoxical predicate has a witness *)
  destruct (omega_completeness P) as [witness H_witness].

  (* From the witness we directly obtain our paradoxical set *)
  exact H_witness.
Qed.


Theorem Omega_contains_set_larger_than_itself_iff_not_containing_it :
  forall (Omega : OmegaType),
    exists (x : Omegacarrier),
      (exists (X : Type) (f : X -> Omegacarrier), strictly_larger X Omegacarrier) <->
      ~ (exists (X : Type) (f : X -> Omegacarrier), strictly_larger X Omegacarrier).
Proof.
  intros Omega.

  (* Define the equivalence predicate *)
  set (meta_paradox := fun x : Omegacarrier =>
    (exists (X : Type) (f : X -> Omegacarrier), strictly_larger X Omegacarrier) <->
    ~ (exists (X : Type) (f : X -> Omegacarrier), strictly_larger X Omegacarrier)).

  (* Use Omega completeness to obtain a witness of this paradoxical equivalence *)
  destruct (omega_completeness meta_paradox) as [x H_equiv].

  exists x.
  exact H_equiv.
Qed.

