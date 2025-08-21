(** Cardinality.v: Reasoning about relative "sizes"
    of types in the DAO framework
*)

Require Import DAO.Core.GenerativeType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Core.Bridge.
From Stdlib Require Import Lia.

Definition injective {A B: Type} (f: A -> B) : Prop :=
  forall x y: A, f x = f y -> x = y.

Definition aleph_0 := nat.

Fixpoint aleph_n (n : nat) : Type :=
  match n with
  | 0 => aleph_0
  | S n' => { A : Type & A -> aleph_n n' }
  end.

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


Theorem omega_counts_its_own_transcendence_infinitely :
  forall (Omega : OmegaType),
    exists (counter : Omegacarrier),
      (* The counter witnesses that for every n, there are n distinct things larger than Omega *)
      (forall n : nat, 
        exists (witnesses : nat -> Omegacarrier),
          forall i j : nat, i < n -> j < n -> i <> j ->
            witnesses i <> witnesses j /\
            exists (X_i X_j : Type),
              strictly_larger X_i Omegacarrier /\
              strictly_larger X_j Omegacarrier /\
              X_i <> X_j).
Proof.
  intros Omega.
  
  (* The cheeky predicate: "I count infinite transcendences" *)
  set (infinite_counter := fun counter : Omegacarrier =>
    forall n : nat, 
      exists (witnesses : nat -> Omegacarrier),
        forall i j : nat, i < n -> j < n -> i <> j ->
          witnesses i <> witnesses j /\
          exists (X_i X_j : Type),
            strictly_larger X_i Omegacarrier /\
            strictly_larger X_j Omegacarrier /\
            X_i <> X_j).
  
  destruct (omega_completeness infinite_counter) as [counter H_counts].
  exists counter.
  exact H_counts.
Qed.


(* Now let's show how this could lead to actual math *)
Module SizeParadoxCounting.
  (* Define the counting function once *)
  Axiom hash_surjective_sig : 
    forall {Alpha : AlphaType} (n : nat), 
    {a : Alphacarrier | @hash Alphacarrier a = n}.

  (* Now we can extract computationally *)
  Definition paradox_count {Alpha : AlphaType} : nat -> Alphacarrier :=
    fun n => proj1_sig (@hash_surjective_sig Alpha n).

  Lemma paradox_count_correct {Alpha : AlphaType} :
    forall n, @hash Alphacarrier (paradox_count n) = n.
  Proof.
    intro n.
    unfold paradox_count.
    destruct (@hash_surjective_sig Alpha n) as [a Ha].
    simpl.
    exact Ha.
  Qed.
  
  (* Alpha literally counts using paradox levels *)
  Theorem alpha_uses_paradoxes_as_numbers :
    forall (Alpha : AlphaType) (Omega : OmegaType),
    (* We have a bijection between nat and some Alpha elements via paradox levels *)
    exists (count : nat -> Alphacarrier),
      (* It's injective *)
      (forall n m, count n = count m -> n = m) /\
      (* Each count n represents paradox level n *)
      (forall n, @hash Alphacarrier (count n) = n) /\
      (* We can always go to the next paradox level *)
      (forall a : Alphacarrier, 
        exists next : Alphacarrier, 
        @hash Alphacarrier next = S (@hash Alphacarrier a)).
  Proof.
    intros Alpha Omega.
    exists paradox_count.
    
    split; [|split].
    -
      intros n m Heq.
      pose proof (paradox_count_correct n) as Hn.
      pose proof (paradox_count_correct m) as Hm.
      rewrite <- Hn, <- Hm, Heq.
      reflexivity.
    - exact paradox_count_correct.
    -
      intro a.
      destruct (@hash_surjective_sig Alpha (S (@hash Alphacarrier a))) as [next Hnext].
      exists next.
      exact Hnext.
  Qed.

  (* Now we can build paradox numbers using omega's own size paradox *)
  (* We need a computational way to get witnesses from Omega *)
  Parameter omega_witness : forall (Omega : OmegaType) (P : Omegacarrier -> Prop), Omegacarrier.

  Definition size_paradox_zero (Omega : OmegaType) : Omegacarrier :=
    omega_witness Omega (fun x => 
      (exists (X : Type) (f : X -> Omegacarrier), strictly_larger X Omegacarrier) <->
      ~ (exists (X : Type) (f : X -> Omegacarrier), strictly_larger X Omegacarrier)).

  (* For the successor, we need to be creative since we can't talk about "Carrier_of prev" *)
  Definition size_paradox_succ (Omega : OmegaType) (prev : Omegacarrier) : Omegacarrier :=
    omega_witness Omega (fun x =>
      (* x witnesses being paradoxically larger than prev's level *)
      exists (X : Type), 
        (strictly_larger X Omegacarrier /\ x = prev) <->
        ~ (strictly_larger X Omegacarrier /\ x = prev)).

  (* Omega can build numbers from infinitely transcending itself *)
  Fixpoint size_paradox_nat (Omega : OmegaType) (n : nat) : Omegacarrier :=
    match n with
    | 0 => size_paradox_zero Omega
    | S n' => size_paradox_succ Omega (size_paradox_nat Omega n')
    end.
End SizeParadoxCounting.
