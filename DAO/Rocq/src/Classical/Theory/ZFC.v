Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.

(* ZFC in ClassicalAlphaType *)
(* Embedding ZFC in ClassicalAlphaType by using the classical veil *)

Section ZFC_in_ClassicalAlpha.
Context `{H_alpha: ClassicalAlphaType}.

(* Sets are just predicates - rename to avoid conflict with Coq's Set *)
Definition ZSet := AlphaPred.

(* Membership is predicate application *)
Definition In (x : Alphacarrier) (A : ZSet) : Prop := A x.
Notation "x 'in' A" := (In x A) (at level 70).
Notation "x 'notin' A" := (~ In x A) (at level 70).

(* Set equality via extensionality *)
Definition set_eq (A B : ZSet) : Prop := pred_equiv A B.
Notation "A == B" := (set_eq A B) (at level 70).

(* Axiom 1: Extensionality (but it's just pred_equiv!) *)
Theorem extensionality : forall A B : ZSet,
  (forall x, x in A <-> x in B) <-> A == B.
Proof.
  intros A B.
  unfold set_eq, pred_equiv, In.
  split; intro H; exact H.
Qed.

(* Axiom 2: Empty Set (it's classical_veil!) *)
Definition Empty : ZSet := classical_veil.

Theorem empty_set_exists : exists E : ZSet, forall x, x notin E.
Proof.
  exists Empty.
  intros x.
  unfold In, Empty.
  apply classical_veil_is_impossible.
Qed.

(* Singleton sets *)
Definition singleton (a : Alphacarrier) : ZSet :=
  fun x => x = a.

Theorem singleton_spec : forall a x,
  x in singleton a <-> x = a.
Proof.
  intros a x.
  unfold In, singleton.
  split; intro H; exact H.
Qed.

(* Now let's try pairing *)
Definition pair (a b : Alphacarrier) : ZSet :=
  fun x => x = a \/ x = b.

Theorem pair_spec : forall a b x,
  x in pair a b <-> (x = a \/ x = b).
Proof.
  intros a b x.
  unfold In, pair.
  split; intro H; exact H.
Qed.


(* Prove singletons are not empty (when element exists) *)
Theorem singleton_not_empty : forall a,
 ~ (singleton a == Empty).
Proof.
 intros a H_eq.
 (* If singleton a == Empty, then a in singleton a <-> a in Empty *)
 assert (a in singleton a) by (apply singleton_spec; reflexivity).
 assert (a in Empty) by (apply H_eq; exact H).
 (* But nothing is in Empty *)
 unfold In, Empty in H0.
 apply (classical_veil_is_impossible a).
 exact H0.
Qed.

(* Prove pairs are not empty *)
Theorem pair_not_empty : forall a b,
 ~ (pair a b == Empty).
Proof.
 intros a b H_eq.
 assert (a in pair a b) by (apply pair_spec; left; reflexivity).
 assert (a in Empty) by (apply H_eq; exact H).
 unfold In, Empty in H0.
 apply (classical_veil_is_impossible a).
 exact H0.
Qed.

(* Axiom 3: Pairing - we can form pairs! *)
Theorem pairing_axiom : forall a b,
 exists P : ZSet, forall x, x in P <-> (x = a \/ x = b).
Proof.
 intros a b.
 exists (pair a b).
 intro x.
 apply pair_spec.
Qed.

(* Define subset relation *)
Definition subset (A B : ZSet) : Prop :=
 forall x, x in A -> x in B.
Notation "A 'subseteq' B" := (subset A B) (at level 70).

(* Binary union *)
Definition union2 (A B : ZSet) : ZSet :=
 fun x => x in A \/ x in B.

Theorem union2_spec : forall A B x,
 x in union2 A B <-> (x in A \/ x in B).
Proof.
 intros A B x.
 unfold In, union2.
 split; intro H; exact H.
Qed.

(* Intersection *)
Definition inter2 (A B : ZSet) : ZSet :=
 fun x => x in A /\ x in B.

Theorem inter2_spec : forall A B x,
 x in inter2 A B <-> (x in A /\ x in B).
Proof.
 intros A B x.
 unfold In, inter2.
 split; intro H; exact H.
Qed.

(* Set difference *)
Definition diff (A B : ZSet) : ZSet :=
 fun x => x in A /\ x notin B.

Theorem diff_spec : forall A B x,
 x in diff A B <-> (x in A /\ x notin B).
Proof.
 intros A B x.
 unfold In, diff.
 split; intro H; exact H.
Qed.

(* Complement (relative to universal set) *)
Definition compl (A : ZSet) : ZSet :=
 fun x => x notin A.

(* The universal set is the_necessary! *)
Definition Universal : ZSet := the_necessary.

Theorem universal_contains_all : forall x,
 x in Universal.
Proof.
 intros x.
 unfold In, Universal, the_necessary.
 apply classical_veil_is_impossible.
Qed.

(* Basic set algebra theorems *)
Theorem union_empty_left : forall A,
 union2 Empty A == A.
Proof.
 intros A.
 unfold set_eq, pred_equiv.
 intros x.
 split.
 - intros [H_empty | H_A].
   + (* x in Empty - impossible *)
     unfold In, Empty in H_empty.
     exfalso.
     apply (classical_veil_is_impossible x).
     exact H_empty.
   + exact H_A.
 - intros H_A.
   right. exact H_A.
Qed.

Theorem inter_empty_left : forall A,
 inter2 Empty A == Empty.
Proof.
 intros A.
 unfold set_eq, pred_equiv.
 intros x.
 split.
 - intros [H_empty H_A].
   exact H_empty.
 - intros H_empty.
   split.
   + exact H_empty.
   + (* Need to show x in A, but we know x in Empty which is impossible *)
     unfold In, Empty in H_empty.
     exfalso.
     apply (classical_veil_is_impossible x).
     exact H_empty.
Qed.

(* De Morgan's laws for sets *)
Theorem de_morgan_union : forall A B,
  compl (union2 A B) == inter2 (compl A) (compl B).
Proof.
  intros A B.
  unfold set_eq, pred_equiv.
  intros x.
  unfold In, compl, union2, inter2.
  (* Now we have: ~ (A x \/ B x) <-> ~ A x /\ ~ B x *)
  split.
  - (* Forward direction *)
    intros H_not_union.
    split.
    + intros H_A. 
      apply H_not_union.
      left. exact H_A.
    + intros H_B.
      apply H_not_union.
      right. exact H_B.
  - (* Backward direction *)
    intros [H_not_A H_not_B] [H_A | H_B].
    + exact (H_not_A H_A).
    + exact (H_not_B H_B).
Qed.

Theorem de_morgan_inter : forall A B,
  compl (inter2 A B) == union2 (compl A) (compl B).
Proof.
  intros A B.
  unfold set_eq, pred_equiv.
  intros x.
  unfold In, compl, inter2, union2.
  (* Now we have: ~ (A x /\ B x) <-> ~ A x \/ ~ B x *)
  split.
  - (* Forward direction - need classical logic here *)
    intros H_not_inter.
    destruct (alpha_constant_decision (A x)) as [H_A | H_not_A].
    + (* If A x, then must have ~ B x *)
      right.
      intros H_B.
      apply H_not_inter.
      split; assumption.
    + (* If ~ A x, we're done *)
      left. exact H_not_A.
  - (* Backward direction *)
    intros [H_not_A | H_not_B] [H_A H_B].
    + exact (H_not_A H_A).
    + exact (H_not_B H_B).
Qed.


(* Axiomatize that some elements of Alphacarrier can represent sets *)
(* This is like saying "some elements are sets" in ZFC *)
Axiom is_set_code : Alphacarrier -> Prop.
Axiom set_decode : Alphacarrier -> ZSet.

(* set_decode is only meaningful for set codes *)
Axiom decode_only_codes : forall x,
  ~ is_set_code x -> set_decode x == Empty.

(* For any predicate that's "set-like", there's a code for it *)
Axiom set_encode_exists : forall (S : ZSet), 
  (exists a, S a) \/ (forall a, ~ S a) ->  (* S is not "middle" *)
  exists x, is_set_code x /\ set_decode x == S.

(* The membership relation for coded sets *)
Definition mem (a b : Alphacarrier) : Prop :=
  is_set_code b /\ a in set_decode b.

Notation "a 'mem' b" := (mem a b) (at level 70).

(* Let's verify this works with basic examples *)
Theorem empty_set_has_code : 
  exists e, is_set_code e /\ set_decode e == Empty.
Proof.
  apply set_encode_exists.
  right. intros a H.
  unfold Empty, In, classical_veil in H.
  apply (classical_veil_is_impossible a H).
Qed.

(* Basic theorems about set codes *)
Theorem singleton_has_code : forall a,
  exists s, is_set_code s /\ set_decode s == singleton a.
Proof.
  intro a.
  apply set_encode_exists.
  left. exists a. 
  unfold singleton, In. reflexivity.
Qed.

Theorem pair_has_code : forall a b,
  exists p, is_set_code p /\ set_decode p == pair a b.
Proof.
  intros a b.
  apply set_encode_exists.
  left. exists a.
  unfold pair, In. left. reflexivity.
Qed.

(* Union axiom - for any set of sets, their union exists *)
Definition is_union_of (F union_set : Alphacarrier) : Prop :=
  is_set_code F /\ is_set_code union_set /\
  forall x, x mem union_set <-> exists Y, Y mem F /\ x mem Y.

Axiom union_exists : forall F,
  is_set_code F ->
  exists U, is_union_of F U.


(* Binary union as a special case *)
Theorem binary_union_exists : forall A B,
  is_set_code A -> is_set_code B ->
  exists U, is_set_code U /\ 
    forall x, x mem U <-> (x mem A \/ x mem B).
Proof.
  intros A B HA HB.
  (* First, create a pair {A, B} *)
  destruct (pair_has_code A B) as [P [HP HPdecode]].
  (* Then take union of this pair *)
  destruct (union_exists P HP) as [U HU].
  exists U.
  destruct HU as [HF [HUcode HUspec]].
  split; [exact HUcode|].
  intro x.
  split.
  - intro HxU.
    apply HUspec in HxU.
    destruct HxU as [Y [HYP HxY]].
    (* Y mem P means is_set_code P /\ Y in set_decode P *)
    destruct HYP as [_ HYP'].
    (* Use HPdecode as a function *)
    assert (Y in pair A B).
    { apply HPdecode. exact HYP'. }
    apply pair_spec in H.
    destruct H as [HYA | HYB].
    + left. subst Y. exact HxY.
    + right. subst Y. exact HxY.
  - intros [HxA | HxB].
    + apply HUspec.
      exists A. split; [|exact HxA].
      split; [exact HP|].
      (* Again, use HPdecode as a function *)
      apply HPdecode.
      apply pair_spec. left. reflexivity.
    + apply HUspec.
      exists B. split; [|exact HxB].
      split; [exact HP|].
      apply HPdecode.
      apply pair_spec. right. reflexivity.
Qed.

(* Separation axiom schema - for any set and property, we can form the subset *)
Axiom separation : forall A (P : Alphacarrier -> Prop),
  is_set_code A ->
  exists B, is_set_code B /\
    forall x, x mem B <-> (x mem A /\ P x).

(* Example: intersection via separation *)
Theorem intersection_exists : forall A B,
  is_set_code A -> is_set_code B ->
  exists I, is_set_code I /\
    forall x, x mem I <-> (x mem A /\ x mem B).
Proof.
  intros A B HA HB.
  apply (separation A (fun x => x mem B) HA).
Qed.


(* First, let's define the successor operation in set theory *)
(* Successor of x is x union {x} *)
Definition is_successor (x sx : Alphacarrier) : Prop :=
  is_set_code x /\ is_set_code sx /\
  forall y, y mem sx <-> (y mem x \/ y = x).

(* The axiom of infinity: there exists an inductive set *)
(* A set is inductive if it contains empty and is closed under successor *)
Definition is_inductive (I : Alphacarrier) : Prop :=
  is_set_code I /\
  (exists e, is_set_code e /\ (forall x, ~ (x mem e)) /\ e mem I) /\  (* contains empty *)
  (forall x, x mem I -> exists sx, is_successor x sx /\ sx mem I).      (* closed under successor *)

Axiom infinity : exists I, is_inductive I.

(* Direct axiomatization of important set codes *)
Axiom empty_code : Alphacarrier.
Axiom empty_code_spec : is_set_code empty_code /\ set_decode empty_code == Empty.

(* Similarly for other constructions *)
Axiom singleton_code : Alphacarrier -> Alphacarrier.
Axiom singleton_code_spec : forall a,
  is_set_code (singleton_code a) /\ 
  set_decode (singleton_code a) == singleton a.

Axiom pair_code : Alphacarrier -> Alphacarrier -> Alphacarrier.
Axiom pair_code_spec : forall a b,
  is_set_code (pair_code a b) /\ 
  set_decode (pair_code a b) == pair a b.

Axiom successor_code : Alphacarrier -> Alphacarrier.
Axiom successor_code_spec : forall x,
  is_set_code x -> is_successor x (successor_code x).

(* Alternative approach - let's make a cleaner lemma first *)
Lemma not_mem_empty : forall x, ~ (x mem empty_code).
Proof.
  intros x [Hcode Hin].
  destruct empty_code_spec as [_ Hdecode].
  apply Hdecode in Hin.
  unfold In, Empty in Hin.
  exact (classical_veil_is_impossible x Hin).
Qed.

(* Now the theorem is trivial *)
Theorem zero_exists_zfc : exists z,
  is_set_code z /\ forall x, ~ (x mem z).
Proof.
  exists empty_code.
  destruct empty_code_spec as [Hcode _].
  split.
  - exact Hcode.
  - exact not_mem_empty.
Qed.

(* Let's build the first few natural numbers explicitly *)
Definition zero_zfc := empty_code.
Definition one_zfc := successor_code zero_zfc.
Definition two_zfc := successor_code one_zfc.
Definition three_zfc := successor_code two_zfc.

(* Prove basic properties *)
Lemma zero_is_empty : forall x, ~ (x mem zero_zfc).
Proof.
  exact not_mem_empty.
Qed.

Lemma one_contains_only_zero : forall x,
  x mem one_zfc <-> x = zero_zfc.
Proof.
  intro x.
  unfold one_zfc.
  destruct empty_code_spec as [Hcode _].
  destruct (successor_code_spec zero_zfc Hcode) as [_ [Hscode Hspec]].
  split.
  - intro Hmem.
    apply Hspec in Hmem.
    destruct Hmem as [Hcontra | Heq].
    + exfalso. exact (zero_is_empty x Hcontra).
    + exact Heq.
  - intro Heq.
    subst x.
    apply Hspec.
    right. reflexivity.
Qed.

Lemma two_contains_zero_and_one : forall x,
  x mem two_zfc <-> (x = zero_zfc \/ x = one_zfc).
Proof.
  intro x.
  unfold two_zfc, one_zfc.
  (* Get the properties of successor_code *)
  destruct empty_code_spec as [Hcode0 _].
  
  (* First application of successor_code_spec *)
  assert (Hsucc1 := successor_code_spec zero_zfc Hcode0).
  destruct Hsucc1 as [_ [Hcode_one Hspec1]].
  (* Now Hcode_one : is_set_code (successor_code zero_zfc) *)
  
  (* Second application of successor_code_spec *)
  assert (Hsucc2 := successor_code_spec (successor_code zero_zfc) Hcode_one).
  destruct Hsucc2 as [_ [Hcode_two Hspec2]].
  
  split.
  - intro Hmem.
    apply Hspec2 in Hmem.
    destruct Hmem as [Hin1 | Heq1].
    + (* x mem one_zfc *)
      apply one_contains_only_zero in Hin1.
      left. exact Hin1.
    + (* x = one_zfc *)
      right. exact Heq1.
  - intros [Hz | Ho].
    + (* x = zero_zfc *)
      subst x.
      apply Hspec2.
      left.
      apply one_contains_only_zero.
      reflexivity.
    + (* x = one_zfc *)
      subst x.
      apply Hspec2.
      right. reflexivity.
Qed.

(* Axiom: empty sets have unique codes *)
Axiom empty_unique : forall e1 e2,
  is_set_code e1 -> is_set_code e2 ->
  (forall x, ~ (x mem e1)) ->
  (forall x, ~ (x mem e2)) ->
  e1 = e2.

(* The natural numbers are the intersection of all inductive sets *)
Definition is_natural_number (n : Alphacarrier) : Prop :=
  forall I, is_inductive I -> n mem I.

Theorem zero_is_natural : is_natural_number zero_zfc.
Proof.
  unfold is_natural_number, zero_zfc.
  intros I HI.
  destruct HI as [HIcode [[e [He [Hemp Hemem]]] Hclosed]].
  (* Both empty_code and e are empty sets *)
  assert (e = empty_code).
  { apply empty_unique.
    - exact He.
    - destruct empty_code_spec; assumption.
    - exact Hemp.
    - exact not_mem_empty. }
  subst e.
  exact Hemem.
Qed.

(* Supporting axioms we need for natural numbers *)
Axiom nat_set_code : Alphacarrier.
Axiom nat_set_code_spec : 
  is_set_code nat_set_code /\
  forall n, n mem nat_set_code <-> is_natural_number n.

Axiom nat_is_set_code : forall n,
  is_natural_number n -> is_set_code n.

Axiom successor_preserves_nat : forall n,
  is_natural_number n -> is_natural_number (successor_code n).

(* Induction principle for natural numbers *)
Theorem nat_induction_zfc : forall (P : Alphacarrier -> Prop),
  P zero_zfc ->
  (forall n, is_natural_number n -> P n -> P (successor_code n)) ->
  forall n, is_natural_number n -> P n.
Proof.
  intros P Hz Hsucc n Hn.
  
  (* The subset of naturals satisfying P *)
  destruct nat_set_code_spec as [Hnat_code Hnat_spec].
  destruct (separation nat_set_code P Hnat_code) as [S [HS HSspec]].
  
  (* Claim: S is inductive *)
  assert (His_ind: is_inductive S).
  { unfold is_inductive.
    split; [exact HS|].
    split.
    - (* S contains empty/zero *)
      exists zero_zfc.
      split; [|split].
      + destruct empty_code_spec; assumption.
      + exact zero_is_empty.
      + apply HSspec. split.
        * apply Hnat_spec. exact zero_is_natural.
        * exact Hz.
    - (* S is closed under successor *)
      intros x HxS.
      (* Extract the components without modifying HxS *)
      assert (Hx_components: x mem nat_set_code /\ P x).
      { apply HSspec. exact HxS. }
      destruct Hx_components as [Hx_in_nat Px].
      
      assert (Hx_nat: is_natural_number x).
      { apply Hnat_spec. exact Hx_in_nat. }
      
      assert (Hx_code: is_set_code x).
      { apply nat_is_set_code. exact Hx_nat. }
      
      exists (successor_code x).
      split.
      + apply successor_code_spec. exact Hx_code.
      + apply HSspec. split.
        * apply Hnat_spec. 
          apply successor_preserves_nat. exact Hx_nat.
        * apply Hsucc.
          -- exact Hx_nat.
          -- exact Px. }
  
  (* Since n is natural, it's in S *)
  assert (n_in_S: n mem S).
  { unfold is_natural_number in Hn.
    exact (Hn S His_ind). }
  
  (* Therefore P n holds *)
  apply HSspec in n_in_S.
  destruct n_in_S as [_ Pn].
  exact Pn.
Qed.

(* First, let's properly handle subset encoding *)
Definition encodes_subset (x : Alphacarrier) (A : Alphacarrier) : Prop :=
  is_set_code x /\ is_set_code A /\
  forall y, y mem x -> y mem A.

(* Power set: collection of all subsets of A *)
Definition is_powerset (A ps : Alphacarrier) : Prop :=
  is_set_code A /\ is_set_code ps /\
  forall x, x mem ps <-> encodes_subset x A.

(* Power Set Axiom *)
Axiom powerset_exists : forall A,
  is_set_code A -> exists ps, is_powerset A ps.

(* Let's prove some basic properties *)
Theorem empty_in_every_powerset : forall A ps,
  is_set_code A -> is_powerset A ps ->
  empty_code mem ps.
Proof.
  intros A ps HA Hps.
  destruct Hps as [_ [Hps_code Hps_spec]].
  apply Hps_spec.
  unfold encodes_subset.
  destruct empty_code_spec as [He_code _].
  split; [exact He_code|].
  split; [exact HA|].
  intros y Hy.
  (* y mem empty_code is impossible *)
  exfalso.
  exact (not_mem_empty y Hy).
Qed.

Theorem set_in_own_powerset : forall A ps,
  is_set_code A -> is_powerset A ps ->
  A mem ps.
Proof.
  intros A ps HA Hps.
  destruct Hps as [_ [Hps_code Hps_spec]].
  apply Hps_spec.
  unfold encodes_subset.
  split; [exact HA|].
  split; [exact HA|].
  intros y Hy.
  (* y mem A -> y mem A is trivial *)
  exact Hy.
Qed.

(* Singleton subsets *)
(* Singleton subsets *)
Theorem singleton_in_powerset : forall A ps a,
  is_set_code A -> is_powerset A ps -> a mem A ->
  exists sa, is_set_code sa /\ sa mem ps /\
    forall x, x mem sa <-> x = a.
Proof.
  intros A ps a HA Hps Ha.
  (* Get singleton code *)
  exists (singleton_code a).
  destruct (singleton_code_spec a) as [Hsa_code Hsa_decode].
  split; [exact Hsa_code|].
  split.
  - (* singleton a is in powerset *)
    destruct Hps as [_ [_ Hps_spec]].
    apply Hps_spec.
    unfold encodes_subset.
    split; [exact Hsa_code|].
    split; [exact HA|].
    intros x Hx.
    (* If x mem singleton a, then x = a, so x mem A *)
    destruct Hx as [_ Hx_in].
    assert (x in singleton a).
    { apply Hsa_decode. exact Hx_in. }
    (* Use singleton spec to get x = a *)
    assert (x = a).
    { apply singleton_spec. exact H. }
    (* Now rewrite using the equality *)
    rewrite H0.
    exact Ha.
  - (* Characterization of singleton *)
    intros x.
    split.
    + intro Hx.
      destruct Hx as [_ Hx_in].
      assert (x in singleton a).
      { apply Hsa_decode. exact Hx_in. }
      apply singleton_spec.
      exact H.
    + intro Heq.
      rewrite Heq.  (* Use rewrite instead of subst *)
      split; [exact Hsa_code|].
      apply Hsa_decode.
      apply singleton_spec.
      reflexivity.
Qed.


(* Replacement Axiom *)

(* A relation is functional if it maps each input to at most one output *)
Definition is_functional (R : Alphacarrier -> Alphacarrier -> Prop) : Prop :=
  forall x y z, R x y -> R x z -> y = z.

(* Replacement: The image of a set under a functional relation is a set *)
Axiom replacement : forall A (R : Alphacarrier -> Alphacarrier -> Prop),
  is_set_code A ->
  is_functional R ->
  exists B, is_set_code B /\
    forall y, y mem B <-> exists x, x mem A /\ R x y.

(* Example application: Construct {f(x) | x ∈ A} for any function f *)
Definition function_image (A : Alphacarrier) (f : Alphacarrier -> Alphacarrier) : Prop :=
  is_set_code A ->
  exists B, is_set_code B /\
    forall y, y mem B <-> exists x, x mem A /\ y = f x.

Theorem function_image_exists : forall A f,
  is_set_code A ->
  exists B, is_set_code B /\
    forall y, y mem B <-> exists x, x mem A /\ y = f x.
Proof.
  intros A f HA.
  (* Define the relation R(x,y) := y = f(x) *)
  pose (R := fun x y => y = f x).
  (* Show R is functional *)
  assert (Hfunc: is_functional R).
  { unfold is_functional, R.
    intros x y z Hy Hz.
    (* Hy : y = f x, Hz : z = f x, so y = z by transitivity *)
    rewrite Hy.
    symmetry.
    exact Hz. }
  (* Apply replacement *)
  destruct (replacement A R HA Hfunc) as [B [HB HBspec]].
  exists B. split; [exact HB|].
  intros y. split.
  - intro HyB.
    apply HBspec in HyB.
    destruct HyB as [x [HxA Hy]].
    exists x. split; [exact HxA|].
    unfold R in Hy. exact Hy.
  - intros [x [HxA Heq]].
    apply HBspec.
    exists x. split; [exact HxA|].
    unfold R. exact Heq.
Qed.

(* Foundation/Regularity Axiom *)
(* Every non-empty set has an ∈-minimal element *)
Axiom foundation : forall A,
  is_set_code A ->
  (exists x, x mem A) ->
  exists x, x mem A /\ forall y, y mem x -> ~ (y mem A).

(* This prevents things like x ∈ x or infinite chains x₀ ∈ x₁ ∈ x₂ ∈ ... *)
Theorem no_set_contains_itself : forall x,
  is_set_code x -> ~ (x mem x).
Proof.
  intros x Hx Hmem.
  (* Apply foundation to {x} *)
  destruct (singleton_code_spec x) as [Hs_code Hs_decode].
  assert (exists y, y mem singleton_code x).
  { exists x. 
    (* Need to show x mem singleton_code x *)
    (* By definition, mem requires is_set_code and membership *)
    split.
    - exact Hs_code.
    - apply Hs_decode.
      apply singleton_spec.
      reflexivity. }
  destruct (foundation (singleton_code x) Hs_code H) as [y [Hy Hmin]].
  (* y must be x since singleton only contains x *)
  assert (y = x).
  { destruct Hy as [_ Hy_in].
    apply Hs_decode in Hy_in.
    apply singleton_spec in Hy_in.
    exact Hy_in. }
  subst y.
  (* But then x is minimal, so nothing in x is in singleton x *)
  (* In particular, x in x implies x in singleton x, contradiction *)
  apply (Hmin x Hmem).
  (* Again, build mem without unfold *)
  split.
  - exact Hs_code.
  - apply Hs_decode. 
    apply singleton_spec. 
    reflexivity.
Qed.


(* Axiom of Choice *)

(* A family of sets is a set whose elements are all sets *)
Definition is_family_of_sets (F : Alphacarrier) : Prop :=
  is_set_code F /\ forall x, x mem F -> is_set_code x.

(* A choice function selects one element from each set in the family *)
Definition is_choice_function (F f : Alphacarrier) : Prop :=
  is_family_of_sets F /\ is_set_code f /\
  forall A, A mem F -> 
    (exists a, a mem A) ->  (* if A is non-empty *)
    exists a, a mem A /\ (pair_code A a) mem f.  (* f picks element a from A *)

(* Axiom of Choice: Every family of non-empty sets has a choice function *)
Axiom zf_choice : forall F,
  is_family_of_sets F ->
  (forall A, A mem F -> exists a, a mem A) ->  (* all sets non-empty *)
  exists f, is_choice_function F f.


End ZFC_in_ClassicalAlpha.