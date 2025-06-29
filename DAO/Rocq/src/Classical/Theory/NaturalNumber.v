Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.

(* Natural Numbers in ClassicalAlphaType *)
Section NaturalNumbers.
Context `{H_alpha: ClassicalAlphaType}.

(* We'll encode natural numbers as elements that satisfy certain predicates *)
(* First, we need a predicate that picks out the "numbers" *)
Variable IsNat : AlphaPred.

(* Zero is a specific natural number *)
Variable IsZero : AlphaPred.

(* Successor relation: Succ x y means "y is the successor of x" *)
Variable Succ : Alphacarrier -> Alphacarrier -> Prop.

(* Axiom 1: Zero exists and is a natural number *)
Axiom zero_exists : exists z, IsZero z /\ IsNat z.

(* Axiom 2: Zero is unique *)
Axiom zero_unique : forall x y, IsZero x -> IsZero y -> x = y.

(* Axiom 3: Every natural number has a successor that is also natural *)
Axiom successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y.

(* Axiom 4: Successor is functional (deterministic) *)
Axiom successor_functional : forall x y z, Succ x y -> Succ x z -> y = z.

(* Axiom 5: No number is its own successor (no cycles) *)
Axiom successor_not_reflexive : forall x, ~ Succ x x.

(* Axiom 6: Different numbers have different successors (injectivity) *)
Axiom successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y.

(* Axiom 7: Zero is not a successor *)
Axiom zero_not_successor : forall x y, IsZero y -> ~ Succ x y.

(* Axiom 8: Induction principle *)
Axiom nat_induction : 
  forall (P : AlphaPred),
    (* Base case: P holds for zero *)
    (forall z, IsZero z -> P z) ->
    (* Inductive case: if P(n) then P(S(n)) *)
    (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
    (* Conclusion: P holds for all naturals *)
    (forall n, IsNat n -> P n).

(* Let's prove some basic theorems *)

(* Zero is not the impossible predicate *)
Theorem zero_exists_witness :
  ~ pred_equiv IsZero classical_veil.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [Hz _]].
  exists z. exact Hz.
Qed.

(* Natural numbers form a non-empty set *)
Theorem nat_exists_witness :
  ~ pred_equiv IsNat classical_veil.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [_ Hz]].
  exists z. exact Hz.
Qed.

(* Every natural number is either zero or a successor *)
Theorem zero_or_successor :
  forall n, IsNat n -> IsZero n \/ exists m, IsNat m /\ Succ m n.
Proof.
  intros n Hn.
  (* Use excluded middle *)
  destruct (alpha_constant_decision (IsZero n)) as [Hz | Hnz].
  - left. exact Hz.
  - right.
    (* Use induction to prove this *)
    (* Define the predicate: "is zero or has a predecessor" *)
    set (P := fun x => IsZero x \/ exists m, IsNat m /\ Succ m x).
    assert (HP: P n).
    { apply (nat_induction P); [| |exact Hn].
      - (* Base case: zero satisfies P *)
        intros z Hz. left. exact Hz.
      - (* Inductive case *)
        intros k m Hk HP_k Hsucc.
        right. exists k. split.
        + exact Hk.
        + exact Hsucc. }
    (* Now use the assertion - HP : P n *)
    unfold P in HP.
    destruct HP as [Hz' | Hpred].
    + (* Case: IsZero n - but we know ~ IsZero n *)
      contradiction.
    + (* Case: exists m, IsNat m /\ Succ m n *)
      exact Hpred.
Qed.

(* No number is both zero and a successor *)
Theorem zero_not_both :
  forall n m, IsZero n -> ~ Succ m n.
Proof.
  intros n m Hz Hsucc.
  exact (zero_not_successor m n Hz Hsucc).
Qed.

(* The successor relation is not impossible - at least one successor exists *)
Theorem successor_not_impossible :
  exists x y, Succ x y.
Proof.
  destruct zero_exists as [z [Hz HNz]].
  destruct (successor_exists z HNz) as [sz [Hsz _]].
  exists z, sz. exact Hsz.
Qed.

(* Alternative: Show that the predicate "has a successor" is not impossible *)
Theorem has_successor_not_impossible :
  ~ pred_equiv (fun x => exists y, Succ x y) classical_veil.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [Hz HNz]].
  destruct (successor_exists z HNz) as [sz [Hsz _]].
  exists z. exists sz. exact Hsz.
Qed.

(* Or: Show that the predicate "is a successor" is not impossible *)
Theorem is_successor_not_impossible :
  ~ pred_equiv (fun y => exists x, Succ x y) classical_veil.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [Hz HNz]].
  destruct (successor_exists z HNz) as [sz [Hsz _]].
  exists sz. exists z. exact Hsz.
Qed.

(* Every natural has a unique successor *)
Theorem successor_unique :
  forall n, IsNat n -> exists! s, Succ n s.
Proof.
  intros n Hn.
  destruct (successor_exists n Hn) as [s [Hs HNs]].
  exists s. split.
  - exact Hs.
  - intros y Hy.
    exact (successor_functional n s y Hs Hy).
Qed.

End NaturalNumbers.

