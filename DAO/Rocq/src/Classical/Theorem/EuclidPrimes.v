Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaAPI.
Import ClassicalAlphaAPI.

(* Reconstructing Euclid's Theorem of Infinitely Many Primes *)

Section EuclidPrimes.
  Context `{H_alpha : ClassicalAlphaType}.
  Context (IsNat IsZero IsOne : AlphaPred).
  Context (Succ : Alphacarrier -> Alphacarrier -> Prop).
  Context (zero_exists : exists z, IsZero z /\ IsNat z).
  Context (zero_unique : forall x y, IsZero x -> IsZero y -> x = y).
  Context (successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y).
  Context (successor_functional : forall x y z, Succ x y -> Succ x z -> y = z).
  Context (successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y).
  Context (zero_not_successor : forall x y, IsZero y -> ~ Succ x y).
  Context (nat_induction : forall (P : AlphaPred),
              (forall z, IsZero z -> P z) ->
              (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
              forall n, IsNat n -> P n).

  Context (Plus Times : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop).
  Context (plus_exists : forall x y, IsNat x -> IsNat y -> exists z, IsNat z /\ Plus x y z).
  Context (plus_functional : forall x y z1 z2, Plus x y z1 -> Plus x y z2 -> z1 = z2).

  Context (Divides : Alphacarrier -> Alphacarrier -> Prop).
  Context (IsPrime_pred : Alphacarrier -> Prop).
  Notation IsPrime := IsPrime_pred.

  Context (one_exists : exists o, IsOne o /\ IsNat o).
  Context (one_unique : forall x y, IsOne x -> IsOne y -> x = y).

  (* Structural definition of IsPrime assumed elsewhere *)
  Axiom prime_is_nat : forall p, IsPrime p -> IsNat p.
  Axiom prime_not_zero : forall p, IsPrime p -> ~ IsZero p.
  Axiom prime_not_one : forall p, IsPrime p -> ~ IsOne p.
  Axiom prime_minimal : forall p d, 
    IsPrime p -> IsNat d -> Divides d p -> IsOne d \/ d = p.


Axiom divides_one_implies_one : forall d one,
  IsNat d -> IsOne one -> Divides d one -> IsOne d.

Axiom divides_difference : forall a b c d,
IsNat a -> IsNat b -> IsNat c ->
Plus a c b ->
Divides d b -> Divides d a ->
Divides d c.

Lemma prime_not_divides_one :
  forall p one,
    IsPrime p -> IsOne one -> ~ Divides p one.
Proof.
  intros p one Hprime Hone Hdiv.
  (* p divides 1, so p must be 1 *)
  assert (IsNat p) by (apply prime_is_nat; exact Hprime).
  assert (IsOne p).
  { apply (divides_one_implies_one p one); assumption. }
  (* But p is prime, so p cannot be 1 *)
  exact (prime_not_one p Hprime H0).
Qed.

  Lemma divides_consecutive_implies_divides_one :
    forall n m d one,
      IsNat n -> IsNat m -> IsOne one ->
      Plus n one m ->
      Divides d n -> Divides d m ->
      Divides d one.
  Proof.
    intros n m d one Hn Hm Hone Hplus Hdiv_n Hdiv_m.
    destruct one_exists as [o [Ho_one Ho_nat]].
    assert (one = o) by (apply one_unique; assumption).
    subst.
    (* Now use the divides_difference axiom *)
    apply (divides_difference n m o d Hn Hm Ho_nat Hplus Hdiv_m Hdiv_n).
  Qed.


  (* Greater than relation *)
  Definition Greater (x y : Alphacarrier) : Prop :=
    exists z, IsNat z /\ ~ IsZero z /\ Plus y z x.

  (* Finite products *)
  Variable Product : (Alphacarrier -> Alphacarrier) -> Alphacarrier -> Alphacarrier -> Prop.

  (* Product axioms *)
  Axiom product_exists : forall f n,
    IsNat n -> 
    (forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> IsNat (f i)) ->
    exists p, IsNat p /\ Product f n p.

  Axiom factor_divides_product : forall f n i prod,
    IsNat n -> IsNat i ->
    (exists j, IsNat j /\ Plus i n j) ->
    Product f n prod ->
    Divides (f i) prod.

  Axiom product_nonzero : forall f n prod,
    IsNat n ->
    Product f n prod ->
    (forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> ~ IsZero (f i)) ->
    ~ IsZero prod.

  (* Every number > 1 has a prime divisor *)
  Axiom has_prime_divisor : forall n one,
    IsNat n -> IsOne one -> Greater n one ->
    exists p, IsPrime p /\ Divides p n.

  Axiom plus_comm : forall x y z,
    Plus x y z -> Plus y x z.

  (* Main theorem: Euclid's proof *)
  Theorem euclid_infinitude_of_primes :
    forall n f,
      IsNat n ->
      (forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> IsPrime (f i)) ->
      exists p, IsPrime p /\ 
      forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> p <> f i.
  Proof.
    intros n f Hn Hf_primes.
    
    (* Get the product of all primes f(0)...f(n-1) *)
    assert (H_f_nat: forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> IsNat (f i)).
    { intros i Hi Hlt. 
      assert (IsPrime (f i)) by (apply Hf_primes; assumption).
      apply prime_is_nat; assumption. }
    
    destruct (product_exists f n Hn H_f_nat) as [prod [Hprod_nat Hprod]].
    
    (* Get m = prod + 1 *)
    destruct one_exists as [one [Hone Hone_nat]].
    destruct (plus_exists prod one Hprod_nat Hone_nat) as [m [Hm_nat Hplus_m]].
    
    (* m > 1 because prod ≥ 1 *)
    assert (Hm_gt_one: Greater m one).
    { exists prod. split; [exact Hprod_nat|]. split.
      - (* prod is not zero because it's a product of primes *)
        apply product_nonzero with (f := f) (n := n).
        + exact Hn.
        + exact Hprod.
        + intros i Hi Hlt.
          assert (IsPrime (f i)) by (apply Hf_primes; assumption).
          apply prime_not_zero; assumption.
      - (* Use commutativity to get the right order *)
        apply plus_comm. exact Hplus_m. }
    
    (* So m has a prime divisor p *)
    destruct (has_prime_divisor m one Hm_nat Hone Hm_gt_one) as [p [Hp_prime Hp_div_m]].
    
    exists p. split; [exact Hp_prime|].
    
    (* p cannot be any f(i) *)
    intros i Hi Hlt Heq.
    subst p.
    
    (* f(i) divides prod (as it's a factor) *)
    assert (Hdiv_prod: Divides (f i) prod).
    { apply (factor_divides_product f n i prod Hn Hi Hlt Hprod). }
    
    (* f(i) also divides m = prod + 1 *)
    (* So f(i) divides both prod and prod + 1, hence divides 1 *)
    assert (Hdiv_one: Divides (f i) one).
    { apply (divides_consecutive_implies_divides_one prod m (f i) one).
      - exact Hprod_nat.
      - exact Hm_nat.
      - exact Hone.
      - exact Hplus_m.
      - exact Hdiv_prod.
      - exact Hp_div_m. }
    
    (* But f(i) is prime, so cannot divide 1 *)
    apply (prime_not_divides_one (f i) one).
    - apply Hf_primes; assumption.
    - exact Hone.
    - exact Hdiv_one.
  Qed.
End EuclidPrimes.

