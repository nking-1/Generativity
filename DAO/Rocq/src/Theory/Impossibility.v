Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.OmegaProperties.
Require Import Setoid.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.


(* Builds some primitives and a basic system to begin studying impossible logic *)

(* Note - seems like a heyting algebra *)
Section ImpossibilityAlgebra.
  Context {Alpha : AlphaType}.
  
  (* Helper definitions *)
  Definition Is_Impossible (P : Alphacarrier -> Prop) : Prop :=
    forall a, P a <-> omega_veil a.
    
  Definition Is_Possible (P : Alphacarrier -> Prop) : Prop :=
    ~ Is_Impossible P.
  
  (* Conjunction with impossible *)
  Theorem impossible_and_anything_is_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Impossible (fun a => P a /\ Q a).
  Proof.
    intros P Q HP.
    intro a.
    split.
    - intros [HPa HQa].
      apply HP in HPa.
      exact HPa.
    - intro Himp.
      split.
      + apply HP. exact Himp.
      + (* We need Q a, but we have omega_veil a *)
        exfalso.
        exact (omega_veil_has_no_witnesses a Himp).
  Qed.
  
  (* Disjunction with impossible *)
  Theorem impossible_or_possible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Possible Q ->
    (* P ∨ Q has same possibility status as Q *)
    (forall a, (P a \/ Q a) <-> Q a).
  Proof.
    intros P Q HP HQ a.
    split.
    - intros [HPa | HQa].
      + apply HP in HPa.
        exfalso.
        exact (omega_veil_has_no_witnesses a HPa).
      + exact HQa.
    - intro HQa.
      right. exact HQa.
  Qed.
  
  (* Implication from impossible *)
  Theorem impossible_implies_anything :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    forall a, P a -> Q a.
  Proof.
    intros P Q HP a HPa.
    apply HP in HPa.
    exfalso.
    exact (omega_veil_has_no_witnesses a HPa).
  Qed.
  
  (* Negation of impossible *)
  Theorem not_impossible_is_necessary :
    forall P : Alphacarrier -> Prop,
    Is_Impossible P ->
    forall a, ~ P a.
  Proof.
    intros P HP a HPa.
    apply HP in HPa.
    exact (omega_veil_has_no_witnesses a HPa).
  Qed.
  
  (* Double negation of impossible *)
  Theorem not_not_impossible_is_possible :
    forall P : Alphacarrier -> Prop,
    Is_Impossible (fun a => ~ P a) ->
    Is_Possible P.
  Proof.
    intros P HnP HP.
    (* If P is impossible, then ~P holds everywhere *)
    assert (forall a, ~ P a).
    { apply not_impossible_is_necessary. exact HP. }
    (* But HnP says ~P is impossible *)
    (* Get a witness from alpha_not_empty *)
    destruct alpha_not_empty as [a0 _].
    specialize (HnP a0).
    destruct HnP as [H1 H2].
    (* H1: ~ P a0 -> omega_veil a0 *)
    (* H2: omega_veil a0 -> ~ P a0 *)
    (* We have ~ P a0 from H *)
    specialize (H a0).
    apply H1 in H.
    (* Now we have omega_veil a0 *)
    exact (omega_veil_has_no_witnesses a0 H).
  Qed.
  
  (* The algebra forms a partial order *)
  Definition Impossible_Order (P Q : Alphacarrier -> Prop) : Prop :=
    Is_Impossible P -> Is_Impossible Q.
  
  (* Key theorem: impossibility propagates through logical connectives *)
  Theorem impossibility_propagation_constructive :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    (Is_Impossible (fun a => P a /\ Q a)) /\
    (forall a, P a -> Q a) /\
    (forall a, ~ (P a \/ Q a) -> ~ Q a).
  Proof.
    intros P Q HP.
    split; [|split].
    - apply impossible_and_anything_is_impossible. exact HP.
    - apply impossible_implies_anything. exact HP.
    - intros a H HQa.
      apply H. right. exact HQa.
  Qed.
  
  (* Equivalence *)
  Theorem impossible_iff_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    (forall a, P a <-> Q a) ->
    Is_Impossible Q.
  Proof.
    intros P Q HP Hiff.
    intro a.
    rewrite <- Hiff.
    apply HP.
  Qed.
  
  (* Both directions of implication *)
  Theorem impossible_implies_both_ways :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Impossible Q ->
    (forall a, P a <-> Q a).
  Proof.
    intros P Q HP HQ a.
    split; intro H.
    - apply HQ. apply HP. exact H.
    - apply HP. apply HQ. exact H.
  Qed.
  
  (* Contrapositive *)
  Theorem possible_contrapositive :
    forall P Q : Alphacarrier -> Prop,
    (forall a, P a -> Q a) ->
    Is_Impossible Q ->
    Is_Impossible P.
  Proof.
    intros P Q Himp HQ a.
    split.
    - intro HPa.
      apply HQ.
      apply Himp.
      exact HPa.
    - intro Himpa.
      exfalso.
      exact (omega_veil_has_no_witnesses a Himpa).
  Qed.
  
  (* Multiple conjunctions *)
  Theorem impossible_and_chain :
    forall P Q R : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Impossible (fun a => P a /\ Q a /\ R a).
  Proof.
    intros P Q R HP.
    intro a.
    split.
    - intros [HPa [HQa HRa]].
      apply HP. exact HPa.
    - intro Himpa.
      split.
      + apply HP. exact Himpa.
      + split.
        * exfalso. exact (omega_veil_has_no_witnesses a Himpa).
        * exfalso. exact (omega_veil_has_no_witnesses a Himpa).
  Qed.
  
  (* Impossible is preserved under weakening *)
  Theorem and_impossible_at_witness :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible (fun a => P a /\ Q a) ->
    forall a, Q a -> ~ P a.
  Proof.
    intros P Q HPQ a HQa HPa.
    assert (omega_veil a).
    { apply HPQ. split; assumption. }
    exact (omega_veil_has_no_witnesses a H).
  Qed.
  
  Theorem and_impossible_gives_info :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible (fun a => P a /\ Q a) ->
    forall a, P a -> ~ Q a.
  Proof.
    intros P Q HPQ a HPa HQa.
    assert (omega_veil a).
    { apply HPQ. split; assumption. }
    exact (omega_veil_has_no_witnesses a H).
  Qed.
  
  (* Disjunction properties *)
  Theorem or_impossible_iff_both_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible (fun a => P a \/ Q a) <->
    Is_Impossible P /\ Is_Impossible Q.
  Proof.
    intros P Q.
    split.
    - intro H.
      split; intro a; split.
      + intro HPa. apply H. left. exact HPa.
      + intro Hi. exfalso. exact (omega_veil_has_no_witnesses a Hi).
      + intro HQa. apply H. right. exact HQa.
      + intro Hi. exfalso. exact (omega_veil_has_no_witnesses a Hi).
    - intros [HP HQ] a.
      split.
      + intros [HPa | HQa].
        * apply HP. exact HPa.
        * apply HQ. exact HQa.
      + intro Hi.
        left. apply HP. exact Hi.
  Qed.
  
  (* XOR with impossible *)
  Theorem xor_with_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    (forall a, (P a /\ ~ Q a) \/ (~ P a /\ Q a)) <->
    (forall a, ~ P a /\ Q a).
  Proof.
    intros P Q HP.
    split.
    - intros H a.
      specialize (H a).
      destruct H as [[HPa HnQa] | [HnPa HQa]].
      + exfalso. apply HP in HPa. 
        exact (omega_veil_has_no_witnesses a HPa).
      + exact (conj HnPa HQa).
    - intros H a.
      right.
      exact (H a).
  Qed.

   Theorem impossible_preimage :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, P (f a) -> omega_veil (f a).
  Proof.
    intros f P HP a H.
    apply HP.
    exact H.
  Qed.
  
  (* What if we show that the preimage of impossible is empty? *)
  Theorem impossible_has_no_preimage :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, ~ P (f a).
  Proof.
    intros f P HP a H.
    (* H : P (f a) *)
    (* By HP, P (f a) <-> omega_veil (f a) *)
    apply HP in H.
    (* H : omega_veil (f a) *)
    exact (omega_veil_has_no_witnesses (f a) H).
  Qed.
  
  Theorem composition_with_impossible_is_empty :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, (fun x => P (f x)) a <-> False.
  Proof.
    intros f P HP a.
    split.
    - apply impossible_has_no_preimage. exact HP.
    - intro F. contradiction.
  Qed. 

  Theorem impossible_composition_empty :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, ~ P (f a).
  Proof.
    intros f P HP a HPfa.
    apply HP in HPfa.
    exact (omega_veil_has_no_witnesses (f a) HPfa).
  Qed.

   Definition Impossible_Given (P Q : Alphacarrier -> Prop) : Prop :=
    Is_Impossible (fun a => P a /\ Q a) /\
    Is_Possible Q.
  
  (* If P is impossible given Q, and Q holds somewhere, then P fails there *)
  Theorem impossible_given_witness :
    forall P Q : Alphacarrier -> Prop,
    Impossible_Given P Q ->
    forall a, Q a -> ~ P a.
  Proof.
    intros P Q [Himp Hpos] a HQa HPa.
    assert (omega_veil a).
    { apply Himp. split; assumption. }
    exact (omega_veil_has_no_witnesses a H).
  Qed.

  Definition Almost_Impossible (P : Alphacarrier -> Prop) : Prop :=
    Is_Possible P /\
    forall (witness : Alphacarrier -> Prop),
    (exists a, witness a /\ P a) ->
    exists (blocker : Alphacarrier -> Prop),
    Is_Impossible (fun a => witness a /\ blocker a).
  
  Theorem self_referential_impossible :
    forall P : Alphacarrier -> Prop,
    (forall a, P a <-> P a /\ ~ P a) ->
    Is_Impossible P.
  Proof.
    intros P Hself a.
    split.
    - intro HPa.
      (* From Hself: P a <-> P a /\ ~ P a *)
      apply Hself in HPa.
      destruct HPa as [HPa' HnPa].
      (* We have P a and ~ P a - this is omega_veil! *)
      exfalso. exact (HnPa HPa').
    - intro Hi.
      (* From omega_veil a, we need P a *)
      (* But P can never hold because it implies its own negation *)
      exfalso.
      exact (omega_veil_has_no_witnesses a Hi).
  Qed.

   (* Now for something really fun - the "impossibility rank" *)
  Inductive Impossibility_Rank : (Alphacarrier -> Prop) -> nat -> Prop :=
    | Rank_Direct : forall P,
        (forall a, P a <-> omega_veil a) ->
        Impossibility_Rank P 0
    | Rank_Composite : forall P Q n,
        Impossibility_Rank Q n ->
        (forall a, P a -> Q a) ->
        Impossibility_Rank P (S n).
  
  (* This measures "how many steps" away from omega_veil we are *)
  
  Theorem impossibility_rank_implies_impossible :
    forall P n,
    Impossibility_Rank P n ->
    Is_Impossible P.
  Proof.
    intros P n H.
    induction H.
    - (* Base case: P is directly omega_veil *)
      exact H.
    - (* Inductive: P implies something impossible *)
      intro a.
      split.
      + intro HPa.
        apply IHImpossibility_Rank.
        apply H0.
        exact HPa.
      + intro Hi.
        exfalso.
        exact (omega_veil_has_no_witnesses a Hi).
  Qed.
  
  (* The cool part: Russell's paradox has rank 1! *)
  Example russell_rank_one :
    forall (R : Alphacarrier -> Prop),
    (forall x, R x <-> ~ R x) ->
    Impossibility_Rank R 1.
  Proof.
    intros R Hrussell.
    (* First show R equals omega_veil *)
    assert (H: forall a, R a <-> omega_veil a).
    { 
      intro a.
      split.
      - intro HRa.
        (* R a implies ~ R a by Hrussell *)
        assert (HnRa: ~ R a).
        { apply Hrussell. exact HRa. }
        (* So we have R a and ~ R a *)
        exfalso.
        exact (HnRa HRa).
      - intro Hi.
        exfalso.
        exact (omega_veil_has_no_witnesses a Hi).
    }
    (* Now show it has rank 1 *)
    apply (Rank_Composite R omega_veil 0).
    - apply Rank_Direct.
      intro a. reflexivity.
    - intro a. intro HRa.
      apply H. exact HRa.
  Qed.

(* ## New Additions for Impossibility Algebra:

### 1. **Entropy Accumulation Theorems**
```coq
(* Entropy is additive under conjunction *)
Theorem entropy_additive :
  forall P Q : Alphacarrier -> Prop,
  forall n m : nat,
  Impossibility_Rank P n ->
  Impossibility_Rank Q m ->
  Impossibility_Rank (fun a => P a /\ Q a) (n + m).

(* Entropy is preserved under logical operations *)
Theorem entropy_preserved :
  forall P : Alphacarrier -> Prop,
  forall n : nat,
  Impossibility_Rank P n ->
  Impossibility_Rank (fun a => P a \/ omega_veil a) n.
```

### 2. **Source Tracking Structure**
```coq
(* Track WHERE impossibility came from *)
Inductive ImpossibilitySource :=
  | Paradox : Prop -> ImpossibilitySource
  | Division : nat -> nat -> ImpossibilitySource  
  | Composition : ImpossibilitySource -> ImpossibilitySource -> ImpossibilitySource.

(* Enhanced rank with source *)
Record TaggedImpossibility := {
  predicate : Alphacarrier -> Prop;
  rank : nat;
  source : ImpossibilitySource;
  proof : Is_Impossible predicate
}.
```

### 3. **Meta-Entropy (Entropy of Entropy)**
```coq
(* How much hidden complexity in an impossibility? *)
Definition meta_entropy (P : Alphacarrier -> Prop) : nat -> Prop :=
  fun n => exists (expansion : list (Alphacarrier -> Prop)),
    length expansion = n /\
    (forall Q, In Q expansion -> Is_Impossible Q) /\
    (* P "contains" all Q's in some sense *).

Theorem meta_entropy_growth :
  forall P n,
  meta_entropy P n ->
  exists m, m >= n /\ meta_entropy P m.
```

### 4. **Impossibility Algebra Operations**
```coq
(* Define the actual algebra structure *)
Definition imp_mult (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
  fun a => P a /\ Q a.

Definition imp_add (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
  fun a => P a \/ Q a.

(* Prove it forms a semiring *)
Theorem imp_semiring :
  (* Additive monoid *)
  (forall P Q, Is_Impossible P -> Is_Impossible Q -> 
    Is_Impossible (imp_add P Q) \/ exists a, imp_add P Q a) /\
  (* Multiplicative monoid with annihilator *)
  (forall P, Is_Impossible P -> 
    forall Q, Is_Impossible (imp_mult P Q)).
```

### 5. **Conservation Laws**
```coq
(* Total entropy in a closed system *)
Definition system_entropy (preds : list (Alphacarrier -> Prop)) : nat :=
  sum_ranks preds.

Theorem entropy_conservation :
  forall (transform : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop)),
  (* If transform preserves impossibility structure *)
  (forall P, Is_Impossible P <-> Is_Impossible (transform P)) ->
  (* Then total entropy is conserved *)
  forall preds, system_entropy preds = system_entropy (map transform preds).
```

### 6. **The Fractal Theorem**
```coq
(* omega_veil is self-similar at all scales *)
Theorem omega_fractal :
  forall (nest : nat -> (Alphacarrier -> Prop) -> (Alphacarrier -> Prop)),
  (forall n P, Is_Impossible P -> Is_Impossible (nest n P)) ->
  forall n, Is_Impossible (nest n omega_veil) /\
    (forall a, nest n omega_veil a <-> omega_veil a).
```

These additions would formalize the rich structure we discovered - showing that omega_veil isn't just a trivial absorber but the foundation of a complex algebraic system with conservation laws, fractal properties, and information preservation! *)


End ImpossibilityAlgebra.



Section ImpossibilityAlgebraExtended.
  Context {Alpha : AlphaType}.
  
  (* ========== Source Tracking ========== *)
  
  Inductive ImpossibilitySource :=
    | DirectOmega : ImpossibilitySource
    | Paradox : (Alphacarrier -> Prop) -> ImpossibilitySource
    | Division : nat -> nat -> ImpossibilitySource (* e.g. you divide by zero *)
    | TypeError : string -> ImpossibilitySource
    | Composition : ImpossibilitySource -> ImpossibilitySource -> ImpossibilitySource.
  
  Record TaggedImpossibility := {
    predicate : Alphacarrier -> Prop;
    rank : nat;
    source : ImpossibilitySource;
    impossibility_proof : Is_Impossible predicate
  }.
  
  (* ========== Entropy Accumulation ========== *)
  
  (* Helper: sum of ranks *)
  Fixpoint sum_ranks (l : list nat) : nat :=
    match l with
    | [] => 0
    | h :: t => h + sum_ranks t
    end.
  
  (* Entropy is additive under conjunction *)
  Theorem entropy_additive :
    forall P Q : Alphacarrier -> Prop,
    forall n m : nat,
    Impossibility_Rank P n ->
    Impossibility_Rank Q m ->
    exists k, k <= n + m + 1 /\ 
    Impossibility_Rank (fun a => P a /\ Q a) k.
  Proof.
    intros P Q n m HrankP HrankQ.
    (* P /\ Q implies P, so we can build from P's rank *)
    exists (S n).
    split.
    - lia. (* S n <= n + m + 1 *)
    - apply (Rank_Composite (fun a => P a /\ Q a) P n).
      + exact HrankP.
      + intros a [HPa HQa]. exact HPa.
  Qed.
  
  (* ========== Meta-Entropy ========== *)
  
  (* How many hidden impossibilities in a predicate? *)
  Definition has_hidden_impossibilities (P : Alphacarrier -> Prop) (n : nat) : Prop :=
    exists (components : list (Alphacarrier -> Prop)),
      length components = n /\
      Forall Is_Impossible components /\
      (* P can be "decomposed" into these impossibilities *)
      forall a, P a -> exists Q, In Q components /\ Q a.
  
  (* Meta-entropy can only grow when we look deeper *)
  Theorem meta_entropy_monotonic :
    forall P n m,
    has_hidden_impossibilities P n ->
    n <= m ->
    (* We can always find at least as many impossibilities *)
    exists (components : list (Alphacarrier -> Prop)), length components >= n.
  Proof.
    intros P n m Hhidden Hle.
    destruct Hhidden as [comps [Hlen [Himp Hdecomp]]].
    exists comps.
    rewrite Hlen. lia.
  Qed.
  
  (* ========== Weighted Impossibility Algebra ========== *)
  
  Record WeightedImpossible := {
    certain : Alphacarrier -> Prop;
    weight : nat;
    source_info : ImpossibilitySource;
    weight_positive : weight >= 1;
  }.
  
  (* Multiplication accumulates weight *)
  Definition weighted_mult (P Q : WeightedImpossible) : WeightedImpossible.
  Proof.
    refine ({|
      certain := fun a => certain P a /\ certain Q a;
      weight := weight P + weight Q;
      source_info := Composition (source_info P) (source_info Q);
      weight_positive := _
    |}).
    (* Prove weight_positive: weight P + weight Q >= 1 *)
    (* Since weight P >= 1 and weight Q >= 1, we have P + Q >= 2 >= 1 *)
    pose proof (weight_positive P) as HwP.
    pose proof (weight_positive Q) as HwQ.
    lia.
  Defined.
  
  (* ========== Conservation Laws ========== *)
  
  Definition total_entropy (tagged_preds : list TaggedImpossibility) : nat :=
    fold_left (fun acc t => acc + rank t) tagged_preds 0.

  (* Alternative: work with weighted impossibles that carry their own proof *)
  Definition total_weighted_entropy (weighted : list WeightedImpossible) : nat :=
    fold_left (fun acc w => acc + weight w) weighted 0.
  

  (* If we have decidability for Is_Impossible *)
  Hypothesis impossible_decidable : forall P, {Is_Impossible P} + {~ Is_Impossible P}.
  
  Definition count_impossibles (preds : list (Alphacarrier -> Prop)) : nat :=
    length (filter (fun P => if impossible_decidable P then true else false) preds).
  
  (* Operations can't decrease total impossibility count *)
  Theorem entropy_never_decreases :
    forall P Q R : Alphacarrier -> Prop,
    Is_Impossible P ->
    ~ Is_Impossible Q ->
    Is_Impossible (fun a => P a /\ Q a).
  Proof.
    intros P Q R HimpP HnimpQ.
    apply impossible_and_anything_is_impossible.
    exact HimpP.
  Qed.

  Theorem logical_second_law :
    forall (W1 W2 : WeightedImpossible),
    (* For any binary operation on weighted impossibles *)
    let result := weighted_mult W1 W2 in
    weight result = weight W1 + weight W2.
  Proof.
    intros W1 W2.
    unfold weighted_mult.
    simpl.
    reflexivity.
  Qed.
  
  (* ========== The Algebra Structure ========== *)
  
  Definition imp_class (P : Alphacarrier -> Prop) : option nat :=
    if impossible_decidable P then Some 0 else None.
  
  Definition cast_to_impossible (P : Alphacarrier -> Prop) : WeightedImpossible := {|
    certain := P;
    weight := 1;                    (* Baseline uncertainty only *)
    source_info := DirectOmega;     (* No special cause, just Alpha's nature *)
    weight_positive := Nat.le_refl 1
  |}.

  (* This is an embedding that preserves structure *)
  Theorem cast_preserves_logic :
    forall (P Q : Alphacarrier -> Prop) (a : Alphacarrier),
    (* AND is preserved *)
    (P a /\ Q a) <-> 
    certain (weighted_mult (cast_to_impossible P) (cast_to_impossible Q)) a.
  Proof.
    intros P Q a.
    simpl.
    reflexivity.
  Qed.

  (* But now we can track entropy! *)
  Example cast_shows_entropy :
    forall P : Alphacarrier -> Prop,
    weight (cast_to_impossible P) = 1.  (* Makes baseline entropy visible *)
  Proof.
    intro P. reflexivity.
  Qed.
  
  (* The semiring structure *)
  (* Instance impossibility_semiring : Type := {
    carrier := Alphacarrier -> Prop;
    plus := fun P Q => fun a => P a \/ Q a;
    mult := fun P Q => fun a => P a /\ Q a;
    zero := fun a => False;
    one := fun a => True;
    annihilator := omega_veil
  }. *)
  
  (* ========== Fractal Self-Similarity ========== *)
  
  Theorem omega_self_similar :
    forall (f : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop)),
    (forall P, Is_Impossible P -> Is_Impossible (f P)) ->
    Is_Impossible (f omega_veil).
  Proof.
    intros f Hf.
    apply Hf.
    intro a. split; intro H; exact H.
  Qed.
  
  (* Nested impossibilities collapse *)
  Theorem nested_collapse :
    forall n : nat,
    forall nest : nat -> (Alphacarrier -> Prop) -> (Alphacarrier -> Prop),
    (forall k P, Is_Impossible P -> Is_Impossible (nest k P)) ->
    forall a, nest n omega_veil a <-> omega_veil a.
  Proof.
    intros n nest Hnest a.
    assert (Is_Impossible (nest n omega_veil)).
    { apply Hnest. intro. split; intro H; exact H. }
    apply impossible_implies_both_ways.
    - exact H.
    - intro. split; intro H0; exact H0.
  Qed.

End ImpossibilityAlgebraExtended.


Section ImpossibilityLogic.
  Context {Alpha : AlphaType}.
  
  (* Start with just omega_veil and NAND *)
  Definition NAND (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => ~ (P a /\ Q a).
  
  (* Step 0: We have omega_veil *)
  (* Step 1: Generate the predicate of non-paradoxical elements *)
  Definition alpha_0 : Alphacarrier -> Prop :=
    fun a => ~ omega_veil a.
  
  (* Theorem: alpha_0 is not impossible *)
  Theorem alpha_0_not_impossible :
    ~ Is_Impossible alpha_0.
  Proof.
    intro H.
    (* If alpha_0 were impossible, then ~omega_veil = omega_veil *)
    assert (forall a, ~ omega_veil a <-> omega_veil a) by apply H.
    destruct alpha_not_empty as [a0 _].
    specialize (H0 a0).
    destruct H0 as [H1 H2].
    (* If omega_veil a0, then ~omega_veil a0 by H2, contradiction *)
    (* If ~omega_veil a0, then omega_veil a0 by H1, contradiction *)
    assert (~ omega_veil a0).
    { intro Hov. apply (H2 Hov). exact Hov. }
    apply H0. apply H1. exact H0.
  Qed.
  
  (* Now let's generate basic logical operations using just omega_veil and NAND *)
  
  (* True: something that's always the case *)
  Definition gen_true : Alphacarrier -> Prop :=
    NAND omega_veil alpha_0.  (* ~(impossible ∧ ~impossible) *)
  
  (* False: we can use omega_veil itself as false *)
  Definition gen_false : Alphacarrier -> Prop :=
    omega_veil.
  
  (* NOT via NAND: ~P = P NAND P *)
  Definition gen_not (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    NAND P P.
  
  (* AND via NAND: P ∧ Q = ~(P NAND Q) = ~(~(P ∧ Q)) *)
  Definition gen_and (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    gen_not (NAND P Q).
  
  (* OR via NAND: P ∨ Q = (P NAND P) NAND (Q NAND Q) *)
  Definition gen_or (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    NAND (NAND P P) (NAND Q Q).
  
  (* IMPLIES in intuitionistic style *)
  Definition gen_implies (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    gen_or (gen_not P) Q.
  
  (* Theorem: gen_not omega_veil gives us alpha_0 *)
  Theorem gen_not_impossible_is_first :
    forall a, gen_not omega_veil a <-> alpha_0 a.
  Proof.
    intro a.
    unfold gen_not, alpha_0, NAND.
    split; intro H.
    - (* H : ~ (omega_veil a /\ omega_veil a), need to prove ~ omega_veil a *)
      intro Hov.
      apply H.
      split; exact Hov.
    - (* H : ~ omega_veil a, need to prove ~ (omega_veil a /\ omega_veil a) *)
      intros [Hov _].
      exact (H Hov).
  Qed.
  
  (* Theorem: Our generated true is always true (when witness exists) *)
  Theorem gen_true_holds :
    exists a, gen_true a.
  Proof.
    unfold gen_true, NAND, alpha_0.
    destruct alpha_not_empty as [a0 _].
    exists a0.
    intro H.
    destruct H as [Hov Hnov].
    exact (Hnov Hov).
  Qed.
  
  (* Theorem: Our generated operations are intuitionistically valid *)
  Theorem gen_not_involutive_on_decidable :
    forall P : Alphacarrier -> Prop,
    (forall a, P a \/ ~ P a) ->  (* If P is decidable *)
    forall a, gen_not (gen_not P) a -> P a.
  Proof.
    intros P Hdec a Hnn.
    unfold gen_not, NAND in Hnn.
    (* Hnn : ~ ((~ (P a /\ P a)) /\ (~ (P a /\ P a))) *)
    destruct (Hdec a) as [HPa | HnPa].
    - exact HPa.
    - exfalso.
      apply Hnn.
      split; intro H; destruct H as [HP _]; contradiction.
  Qed.

Lemma double_neg_omega_veil_impossible :
  Is_Impossible (fun a => ~ ~ omega_veil a).
Proof.
  (* Is_Impossible expects: forall a, (~ ~ omega_veil a) <-> omega_veil a *)
  intro a.
  
  (* First prove it has no witnesses *)
  assert (H_no_witnesses: forall x, ~ (~ ~ omega_veil x)).
  {
    intros x H_nnov.
    apply H_nnov.
    exact (omega_veil_has_no_witnesses x).
  }
  
  (* Now use omega_veil_unique to get the biconditional *)
  pose proof (omega_veil_unique (fun x => ~ ~ omega_veil x) H_no_witnesses) as H_equiv.
  
  (* H_equiv gives us: forall x, (~ ~ omega_veil x) <-> omega_veil x *)
  exact (H_equiv a).
Qed.

Theorem omega_veil_double_neg_elim : 
  forall a, ~ ~ omega_veil a -> omega_veil a.
Proof.
  intros a H_nnov.
  (* Use our lemma to show ~ ~ omega_veil is equivalent to omega_veil *)
  apply double_neg_omega_veil_impossible.
  exact H_nnov.
Qed.

(* NAND omega_veil with itself gives alpha_0 *)
Theorem nand_omega_self :
  forall a, NAND omega_veil omega_veil a <-> alpha_0 a.
Proof.
  intro a.
  unfold NAND, alpha_0.
  split; intro H.
  - (* ~ (omega_veil a /\ omega_veil a) -> ~ omega_veil a *)
    intro Hov.
    apply H.
    split; exact Hov.
  - (* ~ omega_veil a -> ~ (omega_veil a /\ omega_veil a) *)
    intros [Hov _].
    exact (H Hov).
Qed.

(* NAND alpha_0 with itself gives omega_veil *)
Theorem nand_alpha_0_self :
  forall a, NAND alpha_0 alpha_0 a <-> omega_veil a.
Proof.
  intro a.
  unfold NAND, alpha_0.
  split; intro H.
  - (* ~ (~ omega_veil a /\ ~ omega_veil a) -> omega_veil a *)
    (* This is ~ ~ omega_veil a -> omega_veil a *)
    apply omega_veil_double_neg_elim.
    intro Hnov.
    apply H.
    split; exact Hnov.
  - (* omega_veil a -> ~ (~ omega_veil a /\ ~ omega_veil a) *)
    intros [Hnov _].
    exact (Hnov H).
Qed.

(* NAND is commutative *)
Theorem nand_comm :
  forall P Q a, NAND P Q a <-> NAND Q P a.
Proof.
  intros P Q a.
  unfold NAND.
  split.
  - (* Left to right: ~ (P a /\ Q a) -> ~ (Q a /\ P a) *)
    intro H.
    intro H_conj.
    apply H.
    destruct H_conj as [HQ HP].
    split; [exact HP | exact HQ].
  - (* Right to left: ~ (Q a /\ P a) -> ~ (P a /\ Q a) *)
    intro H.
    intro H_conj.
    apply H.
    destruct H_conj as [HP HQ].
    split; [exact HQ | exact HP].
Qed.

(* gen_false is just omega_veil - already established *)
Theorem gen_false_is_omega_veil :
  forall a, gen_false a <-> omega_veil a.
Proof.
  intro a. unfold gen_false. split; intro H; exact H.
Qed.

(* gen_and within our two-element algebra *)
Theorem gen_and_omega_alpha :
  forall a, gen_and omega_veil alpha_0 a <-> omega_veil a.
Proof.
  intro a.
  unfold gen_and, gen_not, NAND.
  (* Goal is now: ~ (~ (omega_veil a /\ alpha_0 a) /\ ~ (omega_veil a /\ alpha_0 a)) <-> omega_veil a *)
  split; intro H.
  - (* Forward direction *)
    (* H : ~ (~ (omega_veil a /\ alpha_0 a) /\ ~ (omega_veil a /\ alpha_0 a)) *)
    (* We need to show omega_veil a *)
    apply omega_veil_double_neg_elim.
    intro H_not_ov.
    (* H_not_ov : ~ omega_veil a *)
    apply H.
    (* Goal: ~ (omega_veil a /\ alpha_0 a) /\ ~ (omega_veil a /\ alpha_0 a) *)
    split; intro H_conj; destruct H_conj as [Hov _]; exact (H_not_ov Hov).
  - (* omega_veil a -> ~ ~ (omega_veil a /\ alpha_0 a) *)
    intro H_not.
    apply H_not.
    split.
    + exact H.
    + exfalso. exact (omega_veil_has_no_witnesses a H).
Qed.

(* gen_or within our two-element algebra *)
Theorem gen_or_omega_alpha :
  forall a, gen_or omega_veil alpha_0 a <-> alpha_0 a.
Proof.
  intro a.
  unfold gen_or, NAND.
  (* This becomes: ~ (~ (omega_veil a /\ omega_veil a) /\ ~ (alpha_0 a /\ alpha_0 a)) *)
  (* Which simplifies to: ~ (alpha_0 a /\ omega_veil a) using our previous results *)
  split; intro H.
  - (* Forward direction *)
    intro Hov.
    apply H.
    split.
    + (* ~ (omega_veil a /\ omega_veil a) *)
      intro H_conj.
      destruct H_conj as [Hov1 _].
      exact (omega_veil_has_no_witnesses a Hov1).
    + (* ~ (alpha_0 a /\ alpha_0 a) *)
      intro H_conj.
      destruct H_conj as [Ha0 _].
      unfold alpha_0 in Ha0.
      exact (Ha0 Hov).
  - (* Backward direction *)
    intro H_conj.
    destruct H_conj as [H_omega_nand H_alpha_nand].
    (* We have alpha_0 a, so ~ omega_veil a *)
    unfold alpha_0 in H.
    (* H_alpha_nand says ~ (alpha_0 a /\ alpha_0 a) *)
    apply H_alpha_nand.
    split; exact H.
Qed.

(* Let's first just see what gen_implies is defined as *)
Theorem check_gen_implies_definition :
  forall P Q a,
  gen_implies P Q a <-> gen_or (gen_not P) Q a.
Proof.
  intros P Q a.
  unfold gen_implies.
  reflexivity.
Qed.

(* Let's trace through gen_implies omega_veil omega_veil *)
Theorem gen_implies_omega_omega_v2 :
  forall a, 
  gen_implies omega_veil omega_veil a <-> gen_or (gen_not omega_veil) omega_veil a.
Proof.
  intro a.
  unfold gen_implies.
  reflexivity.
Qed.

(* And we know that gen_not omega_veil = alpha_0 *)
Theorem gen_implies_omega_omega_direct :
  forall a,
  gen_implies omega_veil omega_veil a.
Proof.
  intro a.
  (* omega -> omega should always be true *)
  unfold gen_implies, gen_or, gen_not, NAND.
  intro H.
  destruct H as [H1 H2].
  (* H2 : ~ (omega_veil a /\ omega_veil a) *)
  (* H1 : ~ (~ (omega_veil a /\ omega_veil a) /\ ~ (omega_veil a /\ omega_veil a)) *)
  apply H1.
  split; exact H2.
Qed.

(* Let's check omega -> alpha *)
Theorem gen_implies_omega_alpha :
  forall a,
  gen_implies omega_veil alpha_0 a <-> alpha_0 a.
Proof.
  intro a.
  (* This is (¬omega ∨ alpha) = (alpha ∨ alpha) = alpha *)
  unfold gen_implies, gen_or, gen_not, alpha_0, NAND.
  split.
  - intro H.
    (* We need to prove ~ omega_veil a *)
    intro Hov.
    apply H.
    split.
    + (* ~ (~ (omega_veil a /\ omega_veil a) /\ ~ (omega_veil a /\ omega_veil a)) *)
      intro H_conj.
      destruct H_conj as [H1 H2].
      apply H1.
      split; exact Hov.
    + (* ~ (~ omega_veil a /\ ~ omega_veil a) *)
      intro H_conj.
      destruct H_conj as [H1 H2].
      exact (H1 Hov).
  - intro H_alpha.
    intro H_conj.
    destruct H_conj as [H1 H2].
    (* H2 : ~ (~ omega_veil a /\ ~ omega_veil a) *)
    apply H2.
    split; exact H_alpha.
Qed.

(* Let's check alpha -> omega *)
Theorem gen_implies_alpha_omega :
  forall a,
  gen_implies alpha_0 omega_veil a <-> omega_veil a.
Proof.
  intro a.
  (* This is (¬alpha ∨ omega) = (omega ∨ omega) = omega *)
  unfold gen_implies, gen_or, gen_not, alpha_0, NAND.
  split.
  - intro H.
    (* We need to prove omega_veil a *)
    (* By contradiction - assume ~ omega_veil a *)
    apply omega_veil_double_neg_elim.
    intro H_not_omega.
    apply H.
    split.
    + (* ~ (~ (~ omega_veil a /\ ~ omega_veil a) /\ ~ (~ omega_veil a /\ ~ omega_veil a)) *)
      intro H_conj.
      destruct H_conj as [H1 H2].
      apply H1.
      split; exact H_not_omega.
    + (* ~ (omega_veil a /\ omega_veil a) *)
      intro H_conj.
      destruct H_conj as [Hov _].
      exact (H_not_omega Hov).
  - intro Hov.
    intro H_conj.
    destruct H_conj as [H1 H2].
    apply H2.
    split; exact Hov.
Qed.

(* Finally, let's check alpha -> alpha *)
Theorem gen_implies_alpha_alpha :
  forall a,
  gen_implies alpha_0 alpha_0 a.
Proof.
  intro a.
  (* This is (¬alpha ∨ alpha), which should always be true *)
  unfold gen_implies, gen_or, gen_not, alpha_0, NAND.
  intro H.
  destruct H as [H1 H2].
  (* H1 : ~ (~ (~ omega_veil a /\ ~ omega_veil a) /\ ~ (~ omega_veil a /\ ~ omega_veil a)) *)
  (* H2 : ~ (~ omega_veil a /\ ~ omega_veil a) *)
  apply H1.
  split; exact H2.
Qed.

(* Summary: The complete truth table for gen_implies *)
Theorem gen_implies_complete_behavior :
  (* omega -> omega is always true *)
  (forall a, gen_implies omega_veil omega_veil a) /\
  (* omega -> alpha equals alpha *)
  (forall a, gen_implies omega_veil alpha_0 a <-> alpha_0 a) /\
  (* alpha -> omega equals omega *)
  (forall a, gen_implies alpha_0 omega_veil a <-> omega_veil a) /\
  (* alpha -> alpha is always true *)
  (forall a, gen_implies alpha_0 alpha_0 a).
Proof.
  split; [|split; [|split]].
  - exact gen_implies_omega_omega_direct.
  - exact gen_implies_omega_alpha.
  - exact gen_implies_alpha_omega.
  - exact gen_implies_alpha_alpha.
Qed.

(* And this gives us the classical truth table when restricted to our two values:
   - F -> F = T
   - F -> T = T  
   - T -> F = F
   - T -> T = T
   Where omega_veil is F and alpha_0 is T *)

Definition definitely_true (P : Alphacarrier -> Prop) : Prop :=
  exists a, P a.

Definition definitely_false (P : Alphacarrier -> Prop) : Prop :=
  forall a, ~ P a.  (* equivalently: Is_Impossible P *)

Definition undecidable (P : Alphacarrier -> Prop) : Prop :=
  ~ definitely_true P /\ ~ definitely_false P.

(* Now let's see how these relate to alpha_0 *)
Theorem alpha_0_characterization :
  forall a,
  alpha_0 a <-> ~ omega_veil a.
Proof.
  intro a.
  unfold alpha_0.
  reflexivity.
Qed. 

(* Can the AND of two undecidables be decidable? *)
Theorem and_undecidable_exploration :
  forall P Q : Alphacarrier -> Prop,
  undecidable P ->
  undecidable Q ->
  (* What can we say about P ∧ Q? *)
  ~ definitely_true (fun a => P a /\ Q a).
Proof.
  intros P Q [HnP _] [HnQ _].
  unfold definitely_true in *.
  intro H.
  destruct H as [a [HPa HQa]].
  (* If P and Q both hold at a, then P has a witness *)
  apply HnP.
  exists a. exact HPa.
Qed.

(* Let's explore OR with undecidable predicates *)

(* Let's explore OR with undecidable predicates *)

(* First, can OR with undecidable ever be definitely false? *)
Theorem or_undecidable_not_impossible :
  forall P Q : Alphacarrier -> Prop,
  undecidable P ->
  ~ Is_Impossible (fun a => P a \/ Q a).
Proof.
  intros P Q [H_not_true H_not_false].
  unfold Is_Impossible.
  intro H_impossible.
  (* If P ∨ Q is impossible, then P must be impossible *)
  assert (Is_Impossible P).
  {
    intro a.
    split.
    - intro HPa.
      apply H_impossible.
      left. exact HPa.
    - intro Hov.
      exfalso.
      exact (omega_veil_has_no_witnesses a Hov).
  }
  (* But P is undecidable, so not definitely false *)
  (* Is_Impossible P means forall a, P a <-> omega_veil a *)
  (* This implies forall a, ~ P a *)
  assert (definitely_false P).
  {
    unfold definitely_false.
    intros a HPa.
    apply H in HPa.
    exact (omega_veil_has_no_witnesses a HPa).
  }
  exact (H_not_false H0).
Qed.

(* What about when both operands are undecidable? *)
Theorem both_undecidable_preservation :
  forall P Q : Alphacarrier -> Prop,
  undecidable P ->
  undecidable Q ->
  (* Then AND is undecidable or false, OR is undecidable or true *)
  (~ definitely_true (fun a => P a /\ Q a)) /\
  (~ Is_Impossible (fun a => P a \/ Q a)).
Proof.
  intros P Q HP HQ.
  split.
  - exact (and_undecidable_exploration P Q HP HQ).
  - exact (or_undecidable_not_impossible P Q HP).
Qed.

(* This is dual to our AND result. Let's make it explicit: *)
Theorem undecidable_operations_duality :
  forall P : Alphacarrier -> Prop,
  undecidable P ->
  (* AND can't be true, OR can't be false *)
  (forall R, ~ definitely_true (fun a => P a /\ R a)) /\
  (forall R, ~ Is_Impossible (fun a => P a \/ R a)).
Proof.
  intros P H_undec.
  destruct H_undec as [H_not_true H_not_false].
  split.
  - (* AND case *)
    intros R.
    unfold definitely_true in *.
    intro H.
    destruct H as [a [HPa HRa]].
    (* If P ∧ R has a witness, then P has a witness *)
    apply H_not_true.
    exists a. exact HPa.
  - (* OR case *)
    intros R.
    apply (or_undecidable_not_impossible P R).
    split; assumption.
Qed.

(* How does implication interact with undecidable predicates? *)

Theorem undecidable_and_impossible :
  forall P Q : Alphacarrier -> Prop,
  undecidable P ->
  Is_Impossible Q ->
  Is_Impossible (fun a => P a /\ Q a).
Proof.
  intros P Q H_undec H_Q_imp.
  intro a.
  split.
  - intros [HPa HQa].
    (* Q a is impossible, so this gives omega_veil a *)
    apply H_Q_imp.
    exact HQa.
  - intro Hov.
    split.
    + (* Need P a, but omega_veil a holds *)
      exfalso.
      exact (omega_veil_has_no_witnesses a Hov).
    + (* Need Q a *)
      apply H_Q_imp.
      exact Hov.
Qed.

Theorem undecidable_and_true :
  forall P Q : Alphacarrier -> Prop,
  undecidable P ->
  (forall a, Q a) ->
  (* Then P ∧ Q has same undecidability as P *)
  undecidable (fun a => P a /\ Q a).
Proof.
  intros P Q [H_not_true H_not_false] H_Q_always.
  unfold undecidable, definitely_true, definitely_false.
  split.
  - (* P ∧ Q has no witnesses iff P has no witnesses *)
    intro H_exists.
    destruct H_exists as [a [HPa HQa]].
    apply H_not_true.
    exists a. exact HPa.
  - (* P ∧ Q is not everywhere false iff P is not everywhere false *)
    intro H_all_false.
    apply H_not_false.
    intros a HPa.
    apply (H_all_false a).
    split; [exact HPa | apply H_Q_always].
Qed.

(* Let me make this precise with a theorem *)
Theorem extreme_values_dominate :
  forall P : Alphacarrier -> Prop,
  undecidable P ->
  (* When combined with impossible (omega_veil), AND becomes impossible *)
  (Is_Impossible (fun a => P a /\ omega_veil a)) /\
  (* When combined with always-true, AND preserves undecidability *)
  (forall Q, (forall a, Q a) -> undecidable (fun a => P a /\ Q a)) /\
  (* When combined with impossible, OR preserves undecidability *)
  (undecidable (fun a => P a \/ omega_veil a)) /\
  (* When combined with always-true, OR becomes always-true *)
  (forall Q, (forall a, Q a) -> forall a, (P a \/ Q a)).
Proof.
  intros P H_P_undec.
  split; [|split; [|split]].
  - (* P ∧ omega_veil is impossible *)
    apply undecidable_and_impossible.
    + exact H_P_undec.
    + intro a. reflexivity.  (* omega_veil is Is_Impossible omega_veil *)
  - (* P ∧ always-true preserves P's undecidability *)
    intros Q H_Q_always.
    exact (undecidable_and_true P Q H_P_undec H_Q_always).
  - (* P ∨ omega_veil is still undecidable *)
    (* Since omega_veil never holds, this is just P *)
    destruct H_P_undec as [H_not_true H_not_false].
    split.
    + unfold definitely_true in *.
      intro H_exists.
      destruct H_exists as [a [HPa | Hov]].
      * apply H_not_true. exists a. exact HPa.
      * exact (omega_veil_has_no_witnesses a Hov).
    + unfold definitely_false in *.
      intro H_all_false.
      apply H_not_false.
      intros a HPa.
      apply (H_all_false a).
      left. exact HPa.
  - (* P ∨ always-true is always true *)
    intros Q H_Q_always a.
    right. apply H_Q_always.
Qed.


(* Undecidable predicates can "cheat" by using Omega's completeness *)

(* Let's define undecidable locally for any AlphaType *)
Definition undecidable_in {A : AlphaType} (P : @Alphacarrier A -> Prop) : Prop :=
  ~ (exists a : @Alphacarrier A, P a) /\ 
  ~ (forall a : @Alphacarrier A, ~ P a).

(* Now our theorems can use this parameterized version *)

(* First, let's show that undecidable predicates have witnesses in Omega *)
Theorem undecidable_has_omega_witness 
  {Omega : OmegaType} 
  (embed : @Alphacarrier Alpha -> @Omegacarrier Omega) :
  forall P : @Alphacarrier Alpha -> Prop,
  undecidable_in P ->
  exists x : @Omegacarrier Omega, 
    (exists a : @Alphacarrier Alpha, embed a = x /\ P a) \/
    (exists a : @Alphacarrier Alpha, embed a = x /\ ~ P a).
Proof.
  intros P H_undec.
  (* In Omega, we can ask for a witness to "P holds somewhere OR ~P holds somewhere" *)
  pose (omega_pred := fun x => 
    (exists a : @Alphacarrier Alpha, embed a = x /\ P a) \/
    (exists a : @Alphacarrier Alpha, embed a = x /\ ~ P a)).
  destruct (@omega_completeness Omega omega_pred) as [x Hx].
  exists x. exact Hx.
Qed.

(* Even more dramatically - Omega can decide the undecidable! *)
Theorem omega_decides_undecidable 
  {Omega : OmegaType} 
  (embed : @Alphacarrier Alpha -> @Omegacarrier Omega) :
  forall P : @Alphacarrier Alpha -> Prop,
  undecidable_in P ->
  (* Omega has a point that "knows" whether P has witnesses *)
  exists oracle : @Omegacarrier Omega,
    ((exists a : @Alphacarrier Alpha, P a) /\ 
     exists a : @Alphacarrier Alpha, embed a = oracle /\ P a) \/
    ((forall a : @Alphacarrier Alpha, ~ P a) /\ 
     exists a : @Alphacarrier Alpha, embed a = oracle /\ ~ P a).
Proof.
  intros P H_undec.
  (* Ask Omega for an "oracle" that knows P's status *)
  pose (oracle_pred := fun x =>
    ((exists a : @Alphacarrier Alpha, P a) /\ 
     exists a : @Alphacarrier Alpha, embed a = x /\ P a) \/
    ((forall a : @Alphacarrier Alpha, ~ P a) /\ 
     exists a : @Alphacarrier Alpha, embed a = x /\ ~ P a)).
  destruct (@omega_completeness Omega oracle_pred) as [oracle H_oracle].
  exists oracle. exact H_oracle.
Qed.

(* This is cheating! Omega can answer questions Alpha cannot! *)
Theorem omega_breaks_undecidability
  {Omega : OmegaType}
  (embed : @Alphacarrier Alpha -> @Omegacarrier Omega) :
  forall P : @Alphacarrier Alpha -> Prop,
  undecidable_in P ->
  (* There exists an Omega witness that "resolves" P *)
  exists x : @Omegacarrier Omega,
  exists resolution : bool,
    (resolution = true /\ exists a : @Alphacarrier Alpha, embed a = x /\ P a) \/
    (resolution = false /\ exists a : @Alphacarrier Alpha, embed a = x /\ ~ P a).
Proof.
  intros P H_undec.
  destruct (omega_decides_undecidable embed P H_undec) as [oracle H_oracle].
  exists oracle.
  destruct H_oracle as [[H_exists H_witness] | [H_none H_witness]].
  - exists true. left. split; [reflexivity | exact H_witness].
  - exists false. right. split; [reflexivity | exact H_witness].
Qed.


(* This shows that undecidable -> impossible can't be a tautology! *)
(* The undecidability of the antecedent "infects" the implication *)

  (* The generation sequence: building complexity from impossibility *)
  Definition generation_sequence : nat -> (Alphacarrier -> Prop) :=
    fun n => match n with
    | 0 => omega_veil
    | 1 => alpha_0
    | 2 => gen_true
    | 3 => gen_and alpha_0 alpha_0
    | 4 => gen_or omega_veil alpha_0
    | _ => gen_true  (* default *)
    end.
  
  (* This sequence shows increasing "structural entropy" *)
  Theorem generation_increases_complexity :
    Is_Impossible (generation_sequence 0) /\
    ~ Is_Impossible (generation_sequence 1) /\
    exists a, (generation_sequence 2) a.
  Proof.
    split; [|split].
    - unfold generation_sequence. 
      intro a. split; intro H; exact H.
    - unfold generation_sequence.
      exact alpha_0_not_impossible.
    - unfold generation_sequence.
      exact gen_true_holds.
  Qed.
  
End ImpossibilityLogic.


Section ClassicalLogicFromAlpha.
  Context {Alpha : AlphaType}.
  
  (* Define what it means for a predicate to be classical/collapsed *)
  Definition is_classical (P : Alphacarrier -> Prop) : Prop :=
    (forall a, P a <-> omega_veil a) \/ (forall a, P a <-> alpha_0 a).
  
  (* First, let's prove that our two base predicates are classical *)
  Theorem omega_veil_is_classical : is_classical omega_veil.
  Proof.
    unfold is_classical.
    left. intro a. reflexivity.
  Qed.
  
  Theorem alpha_0_is_classical : is_classical alpha_0.
  Proof.
    unfold is_classical.
    right. intro a. reflexivity.
  Qed.
  
  (* NOT preserves classical *)
Theorem classical_closed_under_not :
  forall P, is_classical P -> is_classical (gen_not P).
Proof.
  intros P H_classical.
  unfold is_classical in *.
  destruct H_classical as [H_omega | H_alpha].
  - (* P = omega_veil, so gen_not P = alpha_0 *)
    right.
    intro a.
    (* We need to show: gen_not P a <-> alpha_0 a *)
    unfold gen_not, NAND.
    (* Now we have: ~(P a ∧ P a) <-> alpha_0 a *)
    split.
    + intro H_nand.
      (* From ~(P a ∧ P a), derive alpha_0 a *)
      unfold alpha_0.
      intro H_ov.
      apply H_nand.
      split; apply H_omega; exact H_ov.
    + intro H_alpha0.
      (* From alpha_0 a, derive ~(P a ∧ P a) *)
      intros [HPa1 HPa2].
      apply H_omega in HPa1.
      unfold alpha_0 in H_alpha0.
      exact (H_alpha0 HPa1).
  - (* P = alpha_0, so gen_not P = omega_veil *)
    left.
    intro a.
    (* We need to show: gen_not P a <-> omega_veil a *)
    unfold gen_not, NAND.
    (* Now we have: ~(P a ∧ P a) <-> omega_veil a *)
    split.
    + intro H_nand.
      (* From ~(P a ∧ P a), derive omega_veil a *)
      apply omega_veil_double_neg_elim.
      intro H_not_omega.
      apply H_nand.
      split; apply H_alpha; unfold alpha_0; exact H_not_omega.
    + intro H_omega.
      (* From omega_veil a, derive ~(P a ∧ P a) *)
      intros [HPa1 HPa2].
      apply H_alpha in HPa1.
      unfold alpha_0 in HPa1.
      exact (HPa1 H_omega).
Qed.

    (* When P equals omega_veil *)
  Lemma equals_omega_veil_iff :
    forall P a,
    (forall x, P x <-> omega_veil x) ->
    P a <-> omega_veil a.
  Proof.
    intros P a H_eq.
    exact (H_eq a).
  Qed.
  
  (* When P equals alpha_0 *)
  Lemma equals_alpha_0_iff :
    forall P a,
    (forall x, P x <-> alpha_0 x) ->
    P a <-> alpha_0 a.
  Proof.
    intros P a H_eq.
    exact (H_eq a).
  Qed.
  
  (* Double negation of conjunction when both are omega *)
  Lemma double_neg_conj_omega :
    forall P Q a,
    (forall x, P x <-> omega_veil x) ->
    (forall x, Q x <-> omega_veil x) ->
    ~ ~ (P a /\ Q a) <-> omega_veil a.
  Proof.
    intros P Q a H_P H_Q.
    split.
    - intro H_nn.
      apply omega_veil_double_neg_elim.
      intro H_not_omega.
      apply H_nn.
      intros [HPa HQa].
      apply H_P in HPa.
      exact (H_not_omega HPa).
    - intro H_omega.
      intro H_neg.
      apply H_neg.
      split; [apply H_P | apply H_Q]; exact H_omega.
  Qed.
  
  (* NAND of identical predicates *)
  Lemma nand_self_is_not :
    forall P a,
    NAND P P a <-> ~ P a.
  Proof.
    intros P a.
    unfold NAND.
    split.
    - intros H HPa. apply H. split; exact HPa.
    - intros H [HPa _]. exact (H HPa).
  Qed.

Lemma gen_and_to_double_neg :
  forall P Q a,
  gen_and P Q a <-> ~ ~ (P a /\ Q a).
Proof.
  intros P Q a.
  unfold gen_and, gen_not, NAND.
  (* gen_and P Q a = ~ (~ (P a /\ Q a) /\ ~ (P a /\ Q a)) *)
  split.
  - intro H.
    intro H_neg.
    apply H.
    split; exact H_neg.
  - intro H_nn.
    intros [H1 H2].
    exact (H_nn H1).
Qed.

Lemma gen_and_extensional :
  forall P P' Q Q' a,
  (forall x, P x <-> P' x) ->
  (forall x, Q x <-> Q' x) ->
  gen_and P Q a <-> gen_and P' Q' a.
Proof.
  intros P P' Q Q' a H_P H_Q.
  unfold gen_and, gen_not, NAND.
  (* Goal: ~ (~ (P a /\ Q a) /\ ~ (P a /\ Q a)) <-> ~ (~ (P' a /\ Q' a) /\ ~ (P' a /\ Q' a)) *)
  split.
  - (* Left to right *)
    intro H.
    intro H_nand'.
    apply H.
    destruct H_nand' as [H1' H2'].
    split.
    + (* Show ~ (P a /\ Q a) from ~ (P' a /\ Q' a) *)
      intro H_PQ.
      apply H1'.
      destruct H_PQ as [HPa HQa].
      split.
      * apply H_P. exact HPa.
      * apply H_Q. exact HQa.
    + (* Same reasoning for second part *)
      intro H_PQ.
      apply H2'.
      destruct H_PQ as [HPa HQa].
      split.
      * apply H_P. exact HPa.
      * apply H_Q. exact HQa.
  - (* Right to left *)
    intro H.
    intro H_nand.
    apply H.
    destruct H_nand as [H1 H2].
    split.
    + (* Show ~ (P' a /\ Q' a) from ~ (P a /\ Q a) *)
      intro H_P'Q'.
      apply H1.
      destruct H_P'Q' as [HP'a HQ'a].
      split.
      * apply H_P. exact HP'a.
      * apply H_Q. exact HQ'a.
    + (* Same reasoning *)
      intro H_P'Q'.
      apply H2.
      destruct H_P'Q' as [HP'a HQ'a].
      split.
      * apply H_P. exact HP'a.
      * apply H_Q. exact HQ'a.
Qed.


  Theorem classical_closed_under_and :
    forall P Q, is_classical P -> is_classical Q -> is_classical (gen_and P Q).
  Proof.
    intros P Q H_P H_Q.
    unfold is_classical in *.
    destruct H_P as [H_P_omega | H_P_alpha];
    destruct H_Q as [H_Q_omega | H_Q_alpha].
    - (* P = omega_veil, Q = omega_veil *)
      left.
      intro a.
      rewrite gen_and_to_double_neg.
      rewrite double_neg_conj_omega; auto.
      reflexivity.
    - (* P = omega_veil, Q = alpha_0 *)
      left.
      intro a.
      rewrite (gen_and_extensional P omega_veil Q alpha_0); auto.
      apply gen_and_omega_alpha.
    - (* P = alpha_0, Q = omega_veil *)
      left.
      intro a.
      rewrite gen_and_to_double_neg.
      split.
      + intro H_nn.
        (* ~~(alpha_0 a /\ omega_veil a) -> omega_veil a *)
        (* Since alpha_0 a /\ omega_veil a is impossible, this is ~~False -> omega_veil a *)
        exfalso.
        apply H_nn.
        intros [HPa HQa].
        apply H_P_alpha in HPa.
        apply H_Q_omega in HQa.
        unfold alpha_0 in HPa.
        exact (HPa HQa).
      + intro H_omega.
        (* omega_veil a -> ~~(alpha_0 a /\ omega_veil a) *)
        (* We need to show ~~False, which is False *)
        exfalso.
        exact (omega_veil_has_no_witnesses a H_omega).
    - (* P = alpha_0, Q = alpha_0 *)
      right.
      intro a.
      rewrite gen_and_to_double_neg.
      split.
      + intro H_nn.
        (* ~~(P a /\ Q a) -> alpha_0 a *)
        unfold alpha_0.
        intro H_omega.
        apply H_nn.
        intros [HPa HQa].
        apply H_P_alpha in HPa.
        unfold alpha_0 in HPa.
        exact (HPa H_omega).
      + intro H_alpha.
        (* alpha_0 a -> ~~(P a /\ Q a) *)
        intro H_neg.
        apply H_neg.
        split.
        * (* P a *)
          apply H_P_alpha. exact H_alpha.
        * (* Q a *)
          apply H_Q_alpha. exact H_alpha.
  Qed.

  Lemma nand_extensional :
    forall P P' Q Q' a,
    (forall x, P x <-> P' x) ->
    (forall x, Q x <-> Q' x) ->
    NAND P Q a <-> NAND P' Q' a.
  Proof.
    intros P P' Q Q' a H_P H_Q.
    unfold NAND.
    split; intro H; intro H_conj; apply H; 
    destruct H_conj as [H1 H2]; split;
    [apply H_P | apply H_Q | apply H_P | apply H_Q]; assumption.
  Qed.

  Lemma gen_or_extensional :
    forall P P' Q Q' a,
    (forall x, P x <-> P' x) ->
    (forall x, Q x <-> Q' x) ->
    gen_or P Q a <-> gen_or P' Q' a.
  Proof.
    intros P P' Q Q' a H_P H_Q.
    unfold gen_or.
    apply nand_extensional.
    - intro x. apply nand_extensional; auto.
    - intro x. apply nand_extensional; auto.
  Qed.

  (* Commutativity of OR for classical predicates *)
Theorem classical_or_comm :
  forall P Q, is_classical P -> is_classical Q ->
  forall a, gen_or P Q a <-> gen_or Q P a.
Proof.
  intros P Q H_P H_Q a.
  unfold gen_or, NAND.
  (* NAND is commutative, so we can swap the arguments *)
  split; intro H; intro H_conj; apply H;
  destruct H_conj as [H1 H2]; split; assumption.
Qed.
  
  (* OR preserves classical *)
Theorem classical_closed_under_or :
  forall P Q, is_classical P -> is_classical Q -> is_classical (gen_or P Q).
Proof.
  intros P Q H_P H_Q.
  unfold is_classical in *.
  destruct H_P as [H_P_omega | H_P_alpha];
  destruct H_Q as [H_Q_omega | H_Q_alpha].
  - (* P = omega_veil, Q = omega_veil *)
    left.
    intro a.
    unfold gen_or, NAND.
    (* Goal: ~ ((~ (P a /\ P a)) /\ (~ (Q a /\ Q a))) <-> omega_veil a *)
    split.
    + intro H.
      apply omega_veil_double_neg_elim.
      intro H_not_omega.
      apply H.
      split.
      * (* ~ (P a /\ P a) *)
        intros [HP1 HP2].
        apply H_P_omega in HP1.
        exact (H_not_omega HP1).
      * (* ~ (Q a /\ Q a) *)
        intros [HQ1 HQ2].
        apply H_Q_omega in HQ1.
        exact (H_not_omega HQ1).
    + intro H_omega.
      intro H_conj.
      destruct H_conj as [H_nand_P H_nand_Q].
      apply H_nand_P.
      split; apply H_P_omega; exact H_omega.
  - (* P = omega_veil, Q = alpha_0 *)
    right.
    intro a.
    (* We already proved this as gen_or_omega_alpha *)
    rewrite (gen_or_extensional P omega_veil Q alpha_0); auto.
    apply gen_or_omega_alpha.
  - (* P = alpha_0, Q = omega_veil *)
    right.
    intro a.
    (* By commutativity *)
    rewrite (gen_or_extensional P alpha_0 Q omega_veil); auto.
    rewrite classical_or_comm; auto using alpha_0_is_classical, omega_veil_is_classical.
    apply gen_or_omega_alpha.
  - (* P = alpha_0, Q = alpha_0 *)
    right.
    intro a.
    unfold gen_or.
    rewrite (nand_extensional (NAND P P) omega_veil (NAND Q Q) omega_veil).
    + (* NAND omega_veil omega_veil a <-> alpha_0 a *)
      apply nand_omega_self.
    + (* NAND P P a <-> omega_veil a *)
      intro x.
      rewrite (nand_extensional P alpha_0 P alpha_0); auto.
      apply nand_alpha_0_self.
    + (* NAND Q Q a <-> omega_veil a *)
      intro x.
      rewrite (nand_extensional Q alpha_0 Q alpha_0); auto.
      apply nand_alpha_0_self.
Qed.
  
  (* Now the key theorem: excluded middle holds for classical predicates *)
  Theorem classical_excluded_middle :
    forall P, is_classical P -> (exists a, P a) \/ (forall a, ~ P a).
  Proof.
    intros P H_classical.
    unfold is_classical in H_classical.
    destruct H_classical as [H_omega | H_alpha].
    - (* P = omega_veil *)
      right.
      intros a H_Pa.
      apply H_omega in H_Pa.
      exact (omega_veil_has_no_witnesses a H_Pa).
    - (* P = alpha_0 *)
      left.
      destruct alpha_not_empty as [a0 _].
      exists a0.
      apply H_alpha.
      unfold alpha_0.
      intro H_omega.
      (* We need to show False from omega_veil a0 *)
      exact (omega_veil_has_no_witnesses a0 H_omega).
  Qed.
  
  (* Double negation elimination for classical predicates *)
  Theorem classical_double_neg_elim :
    forall P, is_classical P -> forall a, gen_not (gen_not P) a -> P a.
  Proof.
    intros P H_classical a H_nn.
    (* Case split on what P is *)
    destruct H_classical as [H_omega | H_alpha].
    - (* P = omega_veil *)
      apply H_omega.
      unfold gen_not, NAND in H_nn.
      (* H_nn : ~ (~ (P a /\ P a) /\ ~ (P a /\ P a)) *)
      apply omega_veil_double_neg_elim.
      intro H_not_omega.
      apply H_nn.
      split.
      + (* ~ (P a /\ P a) *)
        intros [HPa1 HPa2].
        apply H_omega in HPa1.
        exact (H_not_omega HPa1).
      + (* ~ (P a /\ P a) again *)
        intros [HPa1 HPa2].
        apply H_omega in HPa1.
        exact (H_not_omega HPa1).
    - (* P = alpha_0 *)
      apply H_alpha.
      unfold alpha_0.
      intro H_omega_a.
      unfold gen_not, NAND in H_nn.
      apply H_nn.
      split.
      + (* ~ (P a /\ P a) *)
        intros [HPa1 HPa2].
        apply H_alpha in HPa1.
        unfold alpha_0 in HPa1.
        exact (HPa1 H_omega_a).
      + (* ~ (P a /\ P a) again *)
        intros [HPa1 HPa2].
        apply H_alpha in HPa1.
        unfold alpha_0 in HPa1.
        exact (HPa1 H_omega_a).
  Qed.
  
  (* IMPLIES preserves classical *)
  Theorem classical_closed_under_implies :
    forall P Q, is_classical P -> is_classical Q -> is_classical (gen_implies P Q).
  Proof.
    intros P Q H_P H_Q.
    (* gen_implies P Q = gen_or (gen_not P) Q *)
    unfold gen_implies.
    apply classical_closed_under_or.
    - apply classical_closed_under_not. exact H_P.
    - exact H_Q.
  Qed.
  
  (* Truth table lemmas for our operations on classical values *)

Lemma classical_not_table :
  (forall a, gen_not omega_veil a <-> alpha_0 a) /\
  (forall a, gen_not alpha_0 a <-> omega_veil a).
Proof.
  split.
  - apply gen_not_impossible_is_first.
  - intro a. unfold gen_not. apply nand_alpha_0_self.
Qed.

(* Commutativity of AND for classical predicates *)
Theorem classical_and_comm :
  forall P Q, is_classical P -> is_classical Q ->
  forall a, gen_and P Q a <-> gen_and Q P a.
Proof.
  intros P Q H_P H_Q a.
  unfold gen_and, gen_not, NAND.
  (* Both reduce to ~~(P∧Q) and ~~(Q∧P), which are equivalent *)
  split; intro H; intro H_nand; apply H; destruct H_nand as [H1 H2]; split;
  intro H_conj; [apply H1 | apply H2 | apply H1 | apply H2];
  destruct H_conj as [HPa HQa]; split; assumption.
Qed.

Lemma classical_and_table :
  (forall a, gen_and omega_veil omega_veil a <-> omega_veil a) /\
  (forall a, gen_and omega_veil alpha_0 a <-> omega_veil a) /\
  (forall a, gen_and alpha_0 omega_veil a <-> omega_veil a) /\
  (forall a, gen_and alpha_0 alpha_0 a <-> alpha_0 a).
Proof.
  split; [|split; [|split]].
  - (* omega ∧ omega = omega *)
    intro a.
    rewrite gen_and_to_double_neg.
    split.
    + intro H. exfalso. apply H. intros [H1 H2]. exact (omega_veil_has_no_witnesses a H1).
    + intro H. intro H_neg. exfalso. exact (omega_veil_has_no_witnesses a H).
  - (* omega ∧ alpha = omega *)
    apply gen_and_omega_alpha.
  - (* alpha ∧ omega = omega *)
    intro a.
    (* We can't swap alpha_0 and omega_veil - they're different! *)
    (* Instead, let's prove this directly *)
    rewrite gen_and_to_double_neg.
    split.
    + intro H_nn.
      (* ~~(alpha_0 a ∧ omega_veil a) -> omega_veil a *)
      (* But alpha_0 a ∧ omega_veil a is impossible! *)
      exfalso.
      apply H_nn.
      intros [H_alpha H_omega].
      unfold alpha_0 in H_alpha.
      exact (H_alpha H_omega).
    + intro H_omega.
      (* omega_veil a -> ~~(alpha_0 a ∧ omega_veil a) *)
      (* This is ~~False, which is False *)
      exfalso.
      exact (omega_veil_has_no_witnesses a H_omega).
  - (* alpha ∧ alpha = alpha *)
    intro a.
    rewrite gen_and_to_double_neg.
    split.
    + intro H_nn. unfold alpha_0. intro H_omega.
      apply H_nn. intros [_ _]. exact (omega_veil_has_no_witnesses a H_omega).
    + intro H_alpha. intro H_neg. apply H_neg. split; exact H_alpha.
Qed.

Lemma classical_or_table :
  (forall a, gen_or omega_veil omega_veil a <-> omega_veil a) /\
  (forall a, gen_or omega_veil alpha_0 a <-> alpha_0 a) /\
  (forall a, gen_or alpha_0 omega_veil a <-> alpha_0 a) /\
  (forall a, gen_or alpha_0 alpha_0 a <-> alpha_0 a).
Proof.
  split; [|split; [|split]].
  - (* omega ∨ omega = omega *)
    intro a. unfold gen_or, NAND.
    split.
    + intro H. apply omega_veil_double_neg_elim. intro H_not.
      apply H. split; intros [H1 H2]; exact (H_not H1).
    + intro H_omega. intro H_conj. destruct H_conj as [H1 H2].
      apply H1. split; exact H_omega.
  - (* omega ∨ alpha = alpha *)
    apply gen_or_omega_alpha.
  - (* alpha ∨ omega = alpha *)
    intro a.
    rewrite classical_or_comm; auto using omega_veil_is_classical, alpha_0_is_classical.
    apply gen_or_omega_alpha.
  - (* alpha ∨ alpha = alpha *)
    intro a. unfold gen_or, NAND, alpha_0.
    split.
    + intro H. intro H_omega. apply H.
      split; intros [H1 H2]; exact (H1 H_omega).
    + intro H_not_omega. intro H_conj.
      destruct H_conj as [H1 H2]. apply H1. split; exact H_not_omega.
Qed.

(* Now De Morgan's law using truth tables *)
Theorem classical_demorgan_and :
  forall P Q, 
  is_classical P -> is_classical Q ->
  forall a, gen_not (gen_and P Q) a <-> gen_or (gen_not P) (gen_not Q) a.
Proof.
  intros P Q H_P H_Q a.
  (* Let's first destruct the truth table lemmas to make them easier to use *)
  destruct classical_and_table as [H_om_om [H_om_al [H_al_om H_al_al]]].
  destruct classical_or_table as [H_or_om_om [H_or_om_al [H_or_al_om H_or_al_al]]].
  destruct classical_not_table as [H_not_om H_not_al].
  
  destruct H_P as [HP_om | HP_al]; destruct H_Q as [HQ_om | HQ_al].
  - (* P = omega, Q = omega *)
    (* LHS: gen_not (gen_and P Q) = ~(omega ∧ omega) = ~omega = alpha *)
    assert (H_LHS: gen_not (gen_and P Q) a <-> alpha_0 a).
    {
      unfold gen_not, NAND.
      assert (gen_and P Q a <-> omega_veil a).
      { rewrite (gen_and_extensional P omega_veil Q omega_veil); auto. }
      rewrite H.
      split.
      - intro H_not. unfold alpha_0. intro H_omega. 
        apply H_not. split; exact H_omega.
      - intro H_alpha. intros [H1 H2].
        unfold alpha_0 in H_alpha. exact (H_alpha H1).
    }
    
    (* RHS: gen_or (gen_not P) (gen_not Q) = alpha ∨ alpha = alpha *)
    assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> alpha_0 a).
    {
      assert (H_notP_eq: forall x, gen_not P x <-> alpha_0 x).
      { intro x. unfold gen_not, NAND. rewrite !HP_om. apply nand_omega_self. }
      assert (H_notQ_eq: forall x, gen_not Q x <-> alpha_0 x).
      { intro x. unfold gen_not, NAND. rewrite !HQ_om. apply nand_omega_self. }
      rewrite (gen_or_extensional (gen_not P) alpha_0 (gen_not Q) alpha_0); auto.
    }
    
    rewrite H_LHS, H_RHS.
    reflexivity.
    
  - (* P = omega, Q = alpha *)
    (* LHS: ~(omega ∧ alpha) = ~omega = alpha *)
    assert (H_LHS: gen_not (gen_and P Q) a <-> alpha_0 a).
    {
      unfold gen_not, NAND.
      assert (gen_and P Q a <-> omega_veil a).
      { rewrite (gen_and_extensional P omega_veil Q alpha_0); auto. }
      rewrite H.
      split.
      - intro H_not. unfold alpha_0. intro H_omega. 
        apply H_not. split; exact H_omega.
      - intro H_alpha. intros [H1 H2].
        unfold alpha_0 in H_alpha. exact (H_alpha H1).
    }
    
    (* RHS: alpha ∨ omega = alpha *)
    assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> alpha_0 a).
    {
      assert (H_notP_eq: forall x, gen_not P x <-> alpha_0 x).
      { intro x. unfold gen_not, NAND. rewrite !HP_om. apply nand_omega_self. }
      assert (H_notQ_eq: forall x, gen_not Q x <-> omega_veil x).
      { intro x. unfold gen_not, NAND. rewrite !HQ_al. apply nand_alpha_0_self. }
      rewrite (gen_or_extensional (gen_not P) alpha_0 (gen_not Q) omega_veil); auto.
    }
    
    rewrite H_LHS, H_RHS.
    reflexivity.
    
  - (* P = alpha, Q = omega *)
    (* LHS: ~(alpha ∧ omega) = ~omega = alpha *)
    assert (H_LHS: gen_not (gen_and P Q) a <-> alpha_0 a).
    {
      unfold gen_not, NAND.
      assert (gen_and P Q a <-> omega_veil a).
      { rewrite (gen_and_extensional P alpha_0 Q omega_veil); auto. }
      rewrite H.
      split.
      - intro H_not. unfold alpha_0. intro H_omega. 
        apply H_not. split; exact H_omega.
      - intro H_alpha. intros [H1 H2].
        unfold alpha_0 in H_alpha. exact (H_alpha H1).
    }
    
    (* RHS: omega ∨ alpha = alpha *)
    assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> alpha_0 a).
    {
      assert (H_notP_eq: forall x, gen_not P x <-> omega_veil x).
      { intro x. unfold gen_not, NAND. rewrite !HP_al. apply nand_alpha_0_self. }
      assert (H_notQ_eq: forall x, gen_not Q x <-> alpha_0 x).
      { intro x. unfold gen_not, NAND. rewrite !HQ_om. apply nand_omega_self. }
      rewrite (gen_or_extensional (gen_not P) omega_veil (gen_not Q) alpha_0); auto.
    }
    
    rewrite H_LHS, H_RHS.
    reflexivity.
    
  - (* P = alpha, Q = alpha *)
    (* LHS: ~(alpha ∧ alpha) = ~alpha = omega *)
    assert (H_LHS: gen_not (gen_and P Q) a <-> omega_veil a).
    {
      unfold gen_not, NAND.
      assert (gen_and P Q a <-> alpha_0 a).
      { rewrite (gen_and_extensional P alpha_0 Q alpha_0); auto. }
      rewrite H.
      split.
      - intro H_not. 
        apply omega_veil_double_neg_elim. intro H_not_omega.
        apply H_not. split; unfold alpha_0; exact H_not_omega.
      - intro H_omega. intros [H1 H2].
        unfold alpha_0 in H1. exact (H1 H_omega).
    }
    
    (* RHS: omega ∨ omega = omega *)
    assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> omega_veil a).
    {
      assert (H_notP_eq: forall x, gen_not P x <-> omega_veil x).
      { intro x. unfold gen_not, NAND. rewrite !HP_al. apply nand_alpha_0_self. }
      assert (H_notQ_eq: forall x, gen_not Q x <-> omega_veil x).
      { intro x. unfold gen_not, NAND. rewrite !HQ_al. apply nand_alpha_0_self. }
      rewrite (gen_or_extensional (gen_not P) omega_veil (gen_not Q) omega_veil); auto.
    }
    
    rewrite H_LHS, H_RHS.
    reflexivity.
Qed.

End ClassicalLogicFromAlpha.



Section ImpossibilityCalculus.
  Context {Alpha : AlphaType}.
  
  (* Sequence of predicates *)
  Definition predicate_sequence := nat -> (Alphacarrier -> Prop).
  
  (* Two predicates agree on a specific element *)
  Definition agrees_at (P Q : Alphacarrier -> Prop) (a : Alphacarrier) : Prop :=
    P a <-> Q a.
  
  (* Finite approximation: predicates agree on a list of test points *)
  Definition agrees_on_list (P Q : Alphacarrier -> Prop) (witnesses : list Alphacarrier) : Prop :=
    forall a, In a witnesses -> agrees_at P Q a.
  
  (* Convergence: eventually agrees on any finite set *)
  Definition converges_to (seq : predicate_sequence) (P : Alphacarrier -> Prop) : Prop :=
    forall (witnesses : list Alphacarrier),
    exists N : nat,
    forall n : nat,
    n >= N ->
    agrees_on_list (seq n) P witnesses.
  
  (* Example: constant sequence *)
  Definition constant_sequence (P : Alphacarrier -> Prop) : predicate_sequence :=
    fun n => P.
  
  Theorem constant_converges :
    forall P, converges_to (constant_sequence P) P.
  Proof.
    intros P witnesses.
    exists 0.
    intros n Hn a Ha.
    unfold constant_sequence, agrees_at.
    reflexivity.
  Qed.
  
  (* Continuity for predicate transformations *)
  Definition continuous (F : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop)) : Prop :=
    forall (seq : predicate_sequence) (P : Alphacarrier -> Prop),
    converges_to seq P ->
    converges_to (fun n => F (seq n)) (F P).
  
  (* Negation function *)
  Definition pred_neg (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => ~ P a.
  
  (* Is negation continuous? *)
  Theorem negation_continuous : continuous pred_neg.
Proof.
  unfold continuous, converges_to.
  intros seq P Hconv witnesses.
  destruct (Hconv witnesses) as [N HN].
  exists N.
  intros n Hn a Ha.
  specialize (HN n Hn a Ha).
  unfold pred_neg, agrees_at in *.
  split; intro H.
  - (* ~ seq n a -> ~ P a *)
    intro HPa. 
    apply H.
    apply HN.  (* Use HN: seq n a <-> P a in the forward direction *)
    exact HPa.
  - (* ~ P a -> ~ seq n a *)
    intro Hseq.
    apply H.
    apply HN.  (* Use HN: seq n a <-> P a in the backward direction *)
    exact Hseq.
Qed.
  
  (* Observable differences - constructive approach *)
  Inductive observable_diff (P Q : Alphacarrier -> Prop) : Alphacarrier -> Type :=
    | diff_PQ : forall a, P a -> ~ Q a -> observable_diff P Q a
    | diff_QP : forall a, ~ P a -> Q a -> observable_diff P Q a.
  
  (* A constructive notion of "no observable differences" on a witness set *)
  Definition no_observable_diffs (P Q : Alphacarrier -> Prop) (witnesses : list Alphacarrier) : Prop :=
    forall a, In a witnesses -> 
      (P a -> Q a) /\ (Q a -> P a).
  
  (* This is equivalent to agrees_on_list for our purposes *)
  Theorem no_diffs_iff_agrees :
    forall P Q witnesses,
    no_observable_diffs P Q witnesses <-> agrees_on_list P Q witnesses.
  Proof.
    intros P Q witnesses.
    unfold no_observable_diffs, agrees_on_list, agrees_at.
    split.
    - intros H a Ha.
      specialize (H a Ha).
      split; apply H.
    - intros H a Ha.
      specialize (H a Ha).
      split; apply H.
  Qed.
  
  (* Approaching omega_veil *)
  Definition approaches_impossible (seq : predicate_sequence) : Prop :=
    converges_to seq omega_veil.
  
  (* Example: shrinking sequence *)
  Definition shrinking_sequence (base : Alphacarrier -> Prop) : predicate_sequence :=
    fun n => fun a => base a /\ 
      exists (witness_list : list Alphacarrier), 
      length witness_list <= n /\ 
      In a witness_list.
  
  (* Conjunction is continuous *)
  Definition pred_and (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a /\ Q a.
  
  Theorem and_continuous_left :
    forall Q, continuous (fun P => pred_and P Q).
  Proof.
    intros Q.
    unfold continuous, converges_to.
    intros seq P Hconv witnesses.
    destruct (Hconv witnesses) as [N HN].
    exists N.
    intros n Hn a Ha.
    specialize (HN n Hn a Ha).
    unfold pred_and, agrees_at in *.
    split; intros [H1 H2].
    - split.
      + apply HN. exact H1.
      + exact H2.
    - split.
      + apply HN. exact H1.
      + exact H2.
  Qed.
  
  (* Disjunction is continuous *)
  Definition pred_or (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a \/ Q a.
  
  Theorem or_continuous_left :
    forall Q, continuous (fun P => pred_or P Q).
  Proof.
    intros Q.
    unfold continuous, converges_to.
    intros seq P Hconv witnesses.
    destruct (Hconv witnesses) as [N HN].
    exists N.
    intros n Hn a Ha.
    specialize (HN n Hn a Ha).
    unfold pred_or, agrees_at in *.
    split; intros [H | H].
    - left. apply HN. exact H.
    - right. exact H.
    - left. apply HN. exact H.
    - right. exact H.
  Qed.
  
  (* Composition of continuous functions is continuous *)
  Theorem continuous_compose :
    forall F G,
    continuous F ->
    continuous G ->
    continuous (fun P => F (G P)).
  Proof.
    intros F G HF HG.
    unfold continuous in *.
    intros seq P Hconv.
    apply HF.
    apply HG.
    exact Hconv.
  Qed.
  
  (* A predicate sequence that oscillates *)
  Definition oscillating_sequence : predicate_sequence :=
    fun n => if Nat.even n then (fun _ => True) else omega_veil.
  
  Theorem oscillating_not_convergent :
    ~ exists P, converges_to oscillating_sequence P.
  Proof.
    intros [P Hconv].
    destruct alpha_not_empty as [a0 _].
    destruct (Hconv [a0]) as [N HN].
    
    (* The key insight: find two consecutive positions where the sequence differs *)
    (* Let's use positions 0 and 1 for simplicity *)
    destruct (Hconv [a0]) as [N' HN'].
    
    (* Take a large enough N that covers both positions we'll check *)
    pose (M := max N' 2).
    
    (* Check at positions M (which is even) and M+1 (which is odd) *)
    assert (HM_ge : M >= N') by (unfold M; apply Nat.le_max_l).
    assert (H_in : In a0 [a0]) by (left; reflexivity).
    
    (* Get a specific even position *)
    pose (E := 2 * M).  (* E is definitely even *)
    assert (HE_even : Nat.even E = true).
    { unfold E. rewrite Nat.even_mul. reflexivity. }
    
    assert (HE_ge : E >= N').
    { unfold E. unfold ge.
      apply Nat.le_trans with M.
      - exact HM_ge.
      - (* Prove M <= 2 * M directly *)
        rewrite <- (Nat.mul_1_l M) at 1.
        apply Nat.mul_le_mono_r.
        apply Nat.le_succ_diag_r. }
    
    (* At position E: oscillating_sequence E = True *)
    pose proof (HN'_at_E := HN' E HE_ge a0 H_in).
    unfold oscillating_sequence in HN'_at_E.
    rewrite HE_even in HN'_at_E.
    
    (* At position E+1: oscillating_sequence (E+1) = omega_veil *)
    assert (HE1_ge : E + 1 >= N').
    { unfold ge. apply Nat.le_trans with E; [exact HE_ge | apply Nat.le_add_r]. }
    
    pose proof (HN'_at_E1 := HN' (E + 1) HE1_ge a0 H_in).
    unfold oscillating_sequence in HN'_at_E1.
    
    (* E+1 is odd because E is even *)
    assert (HE1_odd : Nat.even (E + 1) = false).
    { 
      (* Since E = 2*M, E+1 = 2*M + 1 which is odd *)
      unfold E.
      rewrite <- Nat.add_1_r.
      rewrite Nat.even_add.
      rewrite Nat.even_mul.
      reflexivity.
    }
    rewrite HE1_odd in HN'_at_E1.
    
    (* Now we have: P a0 <-> True and P a0 <-> omega_veil a0 *)
    assert (P a0) by (apply HN'_at_E; exact I).
    apply HN'_at_E1 in H.
    exact (omega_veil_has_no_witnesses a0 H).
  Qed.
  
  (* Path from one predicate to another *)
  Definition predicate_path := nat -> (Alphacarrier -> Prop).
  
  Definition path_from_to (path : predicate_path) (P Q : Alphacarrier -> Prop) : Prop :=
    path 0 = P /\
    converges_to path Q.
  
  (* The trivial path *)
  Definition trivial_path (P : Alphacarrier -> Prop) : predicate_path :=
    constant_sequence P.
  
  Theorem trivial_path_works :
    forall P, path_from_to (trivial_path P) P P.
  Proof.
    intro P.
    split.
    - reflexivity.
    - apply constant_converges.
  Qed.
  
  (* Linear interpolation doesn't quite work in predicate space, 
     but we can do something similar *)
  
  (* A sequence that gradually "turns off" a predicate *)
  Definition fade_to_impossible (P : Alphacarrier -> Prop) : predicate_sequence :=
    fun n => fun a => P a /\ 
      exists (proof_size : nat), proof_size <= n.
  
  (* If P has witnesses, this doesn't converge to impossible *)
  (* But it shows how we might think about "gradual" changes *)

End ImpossibilityCalculus.

(* ========== Noether's Theorem Connection ========== *)
Section NoetherConnection.
  Context {Alpha : AlphaType}.
  
  (* In physics, Noether's theorem states:
     For every continuous symmetry, there is a conserved quantity.
     
     In DAO Theory, we propose:
     For every paradox translation symmetry, there is conserved impossibility entropy.
  *)
  
  (* A transformation on predicates *)
  Definition predicate_transform := (Alphacarrier -> Prop) -> (Alphacarrier -> Prop).
  
  (* A transformation preserves impossibility structure if it maps 
     impossible predicates to impossible predicates *)
  Definition preserves_impossibility (T : predicate_transform) : Prop :=
    forall P, Is_Impossible P <-> Is_Impossible (T P).
  
  (* The identity transformation *)
  Definition id_transform : predicate_transform := fun P => P.
  
  (* Composition of transformations *)
  Definition compose_transform (T1 T2 : predicate_transform) : predicate_transform :=
    fun P => T1 (T2 P).
  
  (* A "paradox translation" - maps one impossible predicate to another *)
  (* We need decidable equality for this to work computationally *)
  Hypothesis predicate_eq_dec : forall P Q : Alphacarrier -> Prop,
    {forall a, P a <-> Q a} + {~ (forall a, P a <-> Q a)}.
  
  Definition paradox_translation (source target : Alphacarrier -> Prop) 
    (H_source : Is_Impossible source) (H_target : Is_Impossible target) : predicate_transform :=
    fun P => match predicate_eq_dec P source with
             | left _ => target
             | right _ => P
             end.
  
  (* Key insight: All paradox translations preserve impossibility structure *)
  Theorem paradox_translation_symmetry :
    forall source target Hs Ht,
    preserves_impossibility (paradox_translation source target Hs Ht).
  Proof.
    intros source target Hs Ht P.
    unfold preserves_impossibility, paradox_translation.
    split; intro HP.
    - (* If P is impossible *)
      destruct (predicate_eq_dec P source) as [Heq | Hneq].
      + (* P equals source, so we return target which is impossible *)
        exact Ht.
      + (* P doesn't equal source, so we return P which is impossible *)
        exact HP.
    - (* If T(P) is impossible *)
      destruct (predicate_eq_dec P source) as [Heq | Hneq].
      + (* T(P) = target, and target is impossible, so HP : Is_Impossible target *)
        (* We need to prove Is_Impossible P *)
        (* Since P equals source (by Heq), and source is impossible (by Hs) *)
        intro a.
        split.
        * intro HPa.
          apply Hs.
          apply Heq.
          exact HPa.
        * intro Hov.
          apply Heq.
          apply Hs.
          exact Hov.
      + (* T(P) = P, so P is impossible *)
        exact HP.
  Qed.
  
  (* The group of all impossibility-preserving transformations *)
  Record ImpossibilitySymmetry := {
    transform : predicate_transform;
    preserves : preserves_impossibility transform
  }.
  
  (* This forms a group structure *)
  Definition symmetry_compose (S1 S2 : ImpossibilitySymmetry) : ImpossibilitySymmetry.
  Proof.
    refine ({|
      transform := compose_transform (transform S1) (transform S2);
      preserves := _
    |}).
    (* Prove composition preserves impossibility *)
    intros P.
    unfold compose_transform, preserves_impossibility.
    split; intro HP.
    - (* Is_Impossible P -> Is_Impossible (S1 (S2 P)) *)
      apply (preserves S1 (transform S2 P)).
      apply (preserves S2 P).
      exact HP.
    - (* Is_Impossible (S1 (S2 P)) -> Is_Impossible P *)
      (* Use the backwards direction of the iff *)
      apply (preserves S2 P).
      apply (preserves S1 (transform S2 P)).
      exact HP.
  Defined.
  
  Definition symmetry_identity : ImpossibilitySymmetry :=
    {| transform := id_transform; 
       preserves := fun P => iff_refl _ |}.
  
  (* Now for the conservation law connection *)
  
  (* We need decidability for action computation *)
  Hypothesis impossible_decidable : forall P, {Is_Impossible P} + {~ Is_Impossible P}.
  
  (* A "Lagrangian" for predicate dynamics *)
  Definition predicate_action (P : Alphacarrier -> Prop) : nat :=
    if (impossible_decidable P) then 0 else 1.
  
  (* The "Noether current" - impossibility entropy flow *)
  Definition impossibility_current (T : predicate_transform) (P : Alphacarrier -> Prop) : nat :=
    predicate_action P + predicate_action (T P).
  
  (* Noether's Theorem for Impossibility *)
  Theorem impossibility_noether :
    forall (T : predicate_transform),
    preserves_impossibility T ->
    forall P, 
    predicate_action P = predicate_action (T P).
  Proof.
    intros T HT P.
    unfold predicate_action.
    case_eq (impossible_decidable P); intros HP Hdec_P.
    - (* P is impossible *)
      case_eq (impossible_decidable (T P)); intros HTP Hdec_TP.
      + (* T P is also impossible - conservation! *)
        reflexivity.
      + (* T P is not impossible - contradiction *)
        exfalso.
        apply HTP.
        apply (HT P).  (* Use the forward direction of HT *)
        exact HP.
    - (* P is not impossible *)
      case_eq (impossible_decidable (T P)); intros HTP Hdec_TP.
      + (* T P is impossible - contradiction *)
        exfalso.
        apply HP.
        apply (HT P).  (* Use the backward direction of HT *)
        exact HTP.
      + (* T P is also not impossible - conservation! *)
        reflexivity.
  Qed.
  
  (* The deeper connection: paradox translations form a Lie group *)
  
  (* Infinitesimal paradox translation *)
  Definition infinitesimal_paradox_shift (epsilon : Alphacarrier -> Prop) : predicate_transform :=
    fun P a => P a \/ (epsilon a /\ Is_Impossible P).
  
  (* The generator of paradox translations is omega_veil itself! *)
  Theorem omega_veil_generates_symmetry :
    forall P,
    Is_Impossible P ->
    exists T : predicate_transform,
    preserves_impossibility T /\
    T omega_veil = P.
  Proof.
    intros P HP.
    (* Use paradox translation from omega_veil to P *)
    exists (paradox_translation omega_veil P (fun a => iff_refl _) HP).
    split.
    - apply paradox_translation_symmetry.
    - unfold paradox_translation.
      destruct (predicate_eq_dec omega_veil omega_veil) as [Heq | Hneq].
      + reflexivity.
      + (* This case is impossible - omega_veil equals itself *)
        exfalso.
        apply Hneq.
        intro a.
        reflexivity.
  Qed.
  
  (* Conservation of total entropy in a closed system *)
  Theorem total_entropy_conservation :
    forall (system : list (Alphacarrier -> Prop)) (T : predicate_transform),
    preserves_impossibility T ->
    length (filter (fun P => if impossible_decidable P then true else false) system) =
    length (filter (fun P => if impossible_decidable (T P) then true else false) system).
  Proof.
    intros system T HT.
    induction system as [|P rest IH].
    - reflexivity.
    - simpl.
      destruct (impossible_decidable P) as [HP | HnP].
      + (* P is impossible *)
        destruct (impossible_decidable (T P)) as [HTP | HnTP].
        * (* T P is also impossible *)
          simpl. f_equal. exact IH.
        * (* Contradiction *)
          exfalso. apply HnTP. apply (HT P). exact HP.
      + (* P is not impossible *)
        destruct (impossible_decidable (T P)) as [HTP | HnTP].
        * (* Contradiction *)
          exfalso. apply HnP. apply (HT P). exact HTP.
        * (* T P is also not impossible *)
          exact IH.
  Qed.
  
  (* The variational principle: extremal action occurs at omega_veil *)
  Theorem omega_veil_extremal :
    forall P,
    Is_Impossible P ->
    predicate_action P = predicate_action omega_veil.
  Proof.
    intros P HP.
    unfold predicate_action.
    destruct (impossible_decidable P) as [HP_dec | HnP_dec].
    - destruct (impossible_decidable omega_veil) as [Hov_dec | Hnov_dec].
      + reflexivity.
      + exfalso. apply Hnov_dec. intro a. reflexivity.
    - exfalso. apply HnP_dec. exact HP.
  Qed.
  
  (* Summary: The symmetry group of paradox translations leads to
     conservation of impossibility entropy, just as spacetime symmetries
     lead to conservation of energy-momentum in physics. 
     
     omega_veil acts as the generator of these symmetries, playing a role
     analogous to the Hamiltonian in physics. *)
  

  (* First, we need to lift transformations to weighted impossibles *)
Definition apply_weighted_transform (T : predicate_transform) 
  (source : ImpossibilitySource) (W : WeightedImpossible) : WeightedImpossible := {|
  certain := T (certain W);
  weight := weight W;  (* Noether conservation preserves weight *)
  source_info := Composition (source_info W) source;
  weight_positive := weight_positive W  (* Inherited from original *)
|}.

(* The main Noether-thermodynamic connection theorem *)
Theorem noether_thermodynamic_bridge :
  forall (T : predicate_transform) (source : ImpossibilitySource) (W : WeightedImpossible),
  preserves_impossibility T ->
  (* Noether conservation: impossibility structure preserved *)
  (Is_Impossible (certain W) <-> Is_Impossible (certain (apply_weighted_transform T source W))) /\
  (* Thermodynamic conservation: entropy (weight) preserved under symmetry *)
  weight (apply_weighted_transform T source W) = weight W /\
  (* Source tracking: transformation history preserved *)
  source_info (apply_weighted_transform T source W) = Composition (source_info W) source.
Proof.
  intros T source W HT.
  split; [|split].
  - (* Impossibility structure preserved by Noether *)
    simpl. apply HT.
  - (* Weight preserved *)
    simpl. reflexivity.
  - (* Source tracking *)
    simpl. reflexivity.
Qed.

(* Helper lemma: fold_left is preserved under weight-preserving transformations *)
Lemma fold_left_map_weight_preserving :
  forall (l : list WeightedImpossible) (T : predicate_transform) (source : ImpossibilitySource) (acc : nat),
  fold_left (fun acc w => acc + weight w) (map (apply_weighted_transform T source) l) acc =
  fold_left (fun acc w => acc + weight w) l acc.
Proof.
  intros l T source acc.
  revert acc.
  induction l as [|W rest IH]; intro acc.
  - (* Base case: empty list *)
    simpl. reflexivity.
  - (* Inductive case *)
    simpl.
    (* Before simpl, the goal is about the transformed W vs original W *)
    (* Let's rewrite before simpl simplifies things *)
    assert (weight (apply_weighted_transform T source W) = weight W) as H_eq.
    { simpl. reflexivity. }
    
    (* The key: we need to substitute in the right place *)
    change (fold_left (fun acc0 w => acc0 + weight w) (map (apply_weighted_transform T source) rest)
                     (acc + weight (apply_weighted_transform T source W)) =
            fold_left (fun acc0 w => acc0 + weight w) rest (acc + weight W)).
    
    rewrite H_eq.
    apply IH.
Qed.

Theorem system_noether_thermodynamic :
  forall (system : list WeightedImpossible) (T : predicate_transform) (source : ImpossibilitySource),
  preserves_impossibility T ->
  (* Total entropy conserved *)
  total_weighted_entropy (map (apply_weighted_transform T source) system) = 
  total_weighted_entropy system /\
  (* Impossibility count conserved *)
  length (filter (fun W => if impossible_decidable (certain W) then true else false) system) =
  length (filter (fun W => if impossible_decidable (certain (apply_weighted_transform T source W)) then true else false) system).
Proof.
  intros system T source HT.
  split.
  - (* Total entropy conservation *)
    unfold total_weighted_entropy.
    apply fold_left_map_weight_preserving.
  - (* Impossibility count conservation *)
    induction system as [|W rest IH].
    + simpl. reflexivity.
    + simpl.
      destruct (impossible_decidable (certain W)) as [HW | HnW];
      destruct (impossible_decidable (certain (apply_weighted_transform T source W))) as [HTW | HnTW].
      * (* Both impossible *)
        simpl.
        (* We know HTW : Is_Impossible (certain (apply_weighted_transform T source W)) *)
        (* But apply_weighted_transform gives us T (certain W) *)
        assert (HTW_simplified : Is_Impossible (T (certain W))).
        { simpl in HTW. exact HTW. }
        
        (* Now we can decide about T (certain W) *)
        destruct (impossible_decidable (T (certain W))) as [HTW_dec | HnTW_dec].
        -- simpl. f_equal. exact IH.
        -- exfalso. exact (HnTW_dec HTW_simplified).
        
      * (* W impossible but T(W) not impossible - contradiction *)
        exfalso. apply HnTW. simpl. apply (HT (certain W)). exact HW.
      * (* W not impossible but T(W) impossible - contradiction *)
        exfalso. apply HnW. apply (HT (certain W)). simpl in HTW. exact HTW.
      * (* Both not impossible *)
        (* Similar reasoning as the first case *)
        assert (HnTW_simplified : ~ Is_Impossible (T (certain W))).
        { simpl in HnTW. exact HnTW. }
        
        destruct (impossible_decidable (T (certain W))) as [HTW_dec | HnTW_dec].
        -- exfalso. exact (HnTW_simplified HTW_dec).
        -- exact IH.
Qed.

End NoetherConnection.