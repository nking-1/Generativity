(** * Euclid's Theorem: Infinitely Many Primes
    
    This module proves Euclid's classical theorem using our natural
    numbers and arithmetic framework. *)

Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaAPI.
Require Import DAO.Classical.Theory.NaturalNumber.
Require Import DAO.Classical.Theory.Arithmetic.
Import ClassicalAlphaAPI.
Import NaturalNumber.
Import Arithmetic.

Module EuclidPrimes.
  Section EuclidTheorem.
    Context `{H_alpha: ClassicalAlphaType}.
    
    (** Import all natural number and arithmetic components *)
    Context (IsNat IsZero IsOne : AlphaPred).
    Context (Succ : Alphacarrier -> Alphacarrier -> Prop).
    Context (Plus Times : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop).
    Context (Divides : Alphacarrier -> Alphacarrier -> Prop).
    Context (IsPrime : Alphacarrier -> Prop).
    Context (Greater : Alphacarrier -> Alphacarrier -> Prop).
    Context (greater_char : forall x y,
      Greater x y <-> exists z, IsNat z /\ ~ IsZero z /\ Plus y z x).
    
    (** Import the key elements *)
    Context (zero one : Alphacarrier).
    Context (zero_is_zero : IsZero zero).
    Context (zero_is_nat : IsNat zero).
    Context (one_is_one : IsOne one).
    Context (one_is_nat : IsNat one).
    
    (** Import required axioms from arithmetic *)
    Context (prime_is_nat : forall p, IsPrime p -> IsNat p).
    Context (prime_not_zero : forall p, IsPrime p -> ~ IsZero p).
    Context (prime_not_one : forall p, IsPrime p -> ~ IsOne p).
    Context (prime_minimal : forall p d, 
      IsPrime p -> IsNat d -> Divides d p -> IsOne d \/ d = p).
    Context (plus_comm : forall x y z, Plus x y z -> Plus y x z).
    Context (plus_exists : forall x y,
      IsNat x -> IsNat y -> exists z, IsNat z /\ Plus x y z).
    
    (** ** Additional axioms needed for Euclid's proof *)
    
    Axiom divides_one_implies_one : forall d one,
      IsNat d -> IsOne one -> Divides d one -> IsOne d.
    
    Axiom divides_difference : forall a b c d,
      IsNat a -> IsNat b -> IsNat c ->
      Plus a c b ->
      Divides d b -> Divides d a ->
      Divides d c.
    
    (** Every number > 1 has a prime divisor *)
    Axiom has_prime_divisor : forall n one,
      IsNat n -> IsOne one -> Greater n one ->
      exists p, IsPrime p /\ Divides p n.
    
    (** ** Finite products *)
    
    Variable Product : (Alphacarrier -> Alphacarrier) -> Alphacarrier -> Alphacarrier -> Prop.
    
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
    
    (** ** Key Lemmas *)
    
    Lemma prime_not_divides_one :
      forall p one,
        IsPrime p -> IsOne one -> ~ Divides p one.
    Proof.
      intros p one_val Hprime Hone Hdiv.
      (* p divides 1, so p must be 1 *)
      assert (IsNat p) by (apply prime_is_nat; exact Hprime).
      assert (IsOne p).
      { apply (divides_one_implies_one p one_val); assumption. }
      (* But p is prime, so p cannot be 1 *)
      exact (prime_not_one p Hprime H0).
    Qed.
    
    Lemma divides_consecutive_implies_divides_one :
      forall n m d,
        IsNat n -> IsNat m ->
        Plus n one m ->
        Divides d n -> Divides d m ->
        Divides d one.
    Proof.
      intros n m d Hn Hm Hplus Hdiv_n Hdiv_m.
      (* Use the divides_difference axiom directly *)
      apply (divides_difference n m one d Hn Hm one_is_nat Hplus Hdiv_m Hdiv_n).
    Qed.
    
    (** ** Main Theorem: Euclid's Proof *)
    
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
      destruct (plus_exists prod one Hprod_nat one_is_nat) as [m [Hm_nat Hplus_m]].
      
      (* m > 1 because prod ≥ 1 *)
      assert (Hm_gt_one: Greater m one).
      { apply greater_char.
        exists prod. split; [exact Hprod_nat|]. split.
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
      destruct (has_prime_divisor m one Hm_nat one_is_one Hm_gt_one) as [p [Hp_prime Hp_div_m]].
      
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
      { apply (divides_consecutive_implies_divides_one prod m (f i)).
        - exact Hprod_nat.
        - exact Hm_nat.
        - exact Hplus_m.
        - exact Hdiv_prod.
        - exact Hp_div_m. }
      
      (* But f(i) is prime, so cannot divide 1 *)
      apply (prime_not_divides_one (f i) one).
      - apply Hf_primes; assumption.
      - exact one_is_one.
      - exact Hdiv_one.
    Qed.
    
  End EuclidTheorem.
  
End EuclidPrimes.