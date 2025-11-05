(* AlphaInstances.v - A zoo of AlphaType instances *)
Require Import DAO.Core.MinimalAlphaType.
Require Import DAO.Core.AlphaType.
Require Import Stdlib.Init.Datatypes.
Require Import Stdlib.Lists.List.
From Stdlib Require Import PeanoNat.
Require Import Stdlib.Vectors.Fin.

(* ============================================================ *)
(*          Constructing Full AlphaType from Minimal            *)
(* ============================================================ *)

Section MinimalToFull.
  Context `{MinimalAlphaType}.
  
  (** Can construct full AlphaType from minimal version *)
  Definition minimal_to_alpha : AlphaType.
  Proof.
    refine {|
      Alphacarrier := Minalphacarrier;
      alpha_impossibility := _;
      alpha_not_empty := _
    |}.
    - (* Construct the impossibility *)
      exists (fun x => x <> x).
      split.
      + (* No witnesses *)
        intros x Hneq. exact (Hneq eq_refl).
      + (* Uniqueness *)
        intros Q HQ x. split.
        * intro HQx. exfalso. exact (HQ x HQx).
        * intro Hneq. exfalso. exact (Hneq eq_refl).
    - (* Non-emptiness *)
      exact min_not_empty.
  Defined.

End MinimalToFull.

(* ============================================================ *)
(*                    Basic Type Instances                      *)
(* ============================================================ *)

(* Unit - unit type *)
Instance Alpha_unit : AlphaType := {
  Alphacarrier := unit;
  alpha_impossibility := exist _ (fun _ : unit => False) 
    (conj 
      (* First conjunct: False has no witnesses *)
      (fun (x : unit) => fun (H : False) => H)
      (* Second conjunct: uniqueness - any empty predicate equals False pointwise *)
      (fun (Q : unit -> Prop) (HQ : forall x : unit, ~ Q x) (x : unit) => 
        conj
          (fun (H : Q x) => HQ x H : False)  (* Q x -> False *)
          (fun (H : False) => False_ind (Q x) H))); (* False -> Q x *)
  alpha_not_empty := exist _ tt I
}.

(* Natural numbers - the universe of discrete quantities *)
Instance Alpha_nat : AlphaType := {
  Alphacarrier := nat;
  alpha_impossibility := exist _ (fun _ : nat => False)
    (conj
      (fun (n : nat) (H : False) => H)
      (fun Q HQ n => conj (fun H => HQ n H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ 0 I
}.

(* Booleans - the universe of binary choices *)
Instance Alpha_bool : AlphaType := {
  Alphacarrier := bool;
  alpha_impossibility := exist _ (fun _ : bool => False)
    (conj
      (fun (b : bool) (H : False) => H)
      (fun Q HQ b => conj (fun H => HQ b H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ true I
}.


(* Provide some basic instances *)
Class Inhabited (T : Type) := inhabitant : T.

Instance inhabited_unit : Inhabited unit := tt.
Instance inhabited_bool : Inhabited bool := true.
Instance inhabited_nat : Inhabited nat := 0.
Instance inhabited_prod {A B} `{Inhabited A} `{Inhabited B} : Inhabited (A * B) := 
  (inhabitant, inhabitant).
Instance inhabited_sum_left {A B} `{Inhabited A} : Inhabited (A + B) := 
  inl inhabitant.
Instance inhabited_list {A} : Inhabited (list A) := nil.

(* All non-empty types can be an AlphaType *)
Instance Alpha_universal (T : Type) `{Inhabited T} : AlphaType := {
  Alphacarrier := T;
  alpha_impossibility := exist _ (fun _ : T => False)
    (conj
      (fun (x : T) (H : False) => H)
      (fun Q HQ x => conj (fun H => HQ x H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ inhabitant I
}.


(* Let's demonstrate you can use something other than just False *)
(* Natural numbers with "being less than zero" as the impossible predicate *)
Definition nat_impossible_pred : nat -> Prop := fun n => n < 0.

Lemma nat_impossible_empty : forall x : nat, ~ nat_impossible_pred x.
Proof.
  intro x.
  unfold nat_impossible_pred.
  apply Nat.nlt_0_r.
Qed.

Lemma nat_impossible_unique : 
  forall Q : nat -> Prop,
  (forall x : nat, ~ Q x) ->
  (forall x : nat, Q x <-> nat_impossible_pred x).
Proof.
  intros Q HQ x.
  split.
  - intro H. exfalso. exact (HQ x H).
  - intro H. exfalso. exact (nat_impossible_empty x H).
Qed.

Instance Alpha_nat_negative : AlphaType := {
  Alphacarrier := nat;
  alpha_impossibility := 
    exist _ nat_impossible_pred
      (conj nat_impossible_empty nat_impossible_unique);
  alpha_not_empty := exist _ 0 I
}.

(* Extended examples below - we're just going crazy here for fun to *)
(* see how far we can push the type system *)

(* ============================================================ *)
(*                    Composite Type Instances                  *)
(* ============================================================ *)

(* Products - the universe of paired observations *)
Instance Alpha_product (A B : Type) 
  (HA : A) (HB : B) : AlphaType := {
  Alphacarrier := A * B;
  alpha_impossibility := exist _ (fun _ : A * B => False)
    (conj
      (fun (p : A * B) (H : False) => H)
      (fun Q HQ p => conj (fun H => HQ p H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ (HA, HB) I
}.

(* Sums - the universe of alternatives *)
Instance Alpha_sum_left (A B : Type) (HA : A) : AlphaType := {
  Alphacarrier := A + B;
  alpha_impossibility := exist _ (fun _ : A + B => False)
    (conj
      (fun (s : A + B) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ (inl HA) I
}.

(* Lists - the universe of sequences *)
Instance Alpha_list (A : Type) : AlphaType := {
  Alphacarrier := list A;
  alpha_impossibility := exist _ (fun _ : list A => False)
    (conj
      (fun (l : list A) (H : False) => H)
      (fun Q HQ l => conj (fun H => HQ l H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ nil I
}.

(* ============================================================ *)
(*                    Philosophical Instances                   *)
(* ============================================================ *)

(* The universe of finite observations *)
Inductive FiniteObs : Type :=
  | obs_zero : FiniteObs
  | obs_succ : FiniteObs -> FiniteObs
  | obs_split : FiniteObs -> FiniteObs -> FiniteObs.

Instance Alpha_finite_obs : AlphaType := {
  Alphacarrier := FiniteObs;
  alpha_impossibility := exist _ (fun _ : FiniteObs => False)
    (conj
      (fun (o : FiniteObs) (H : False) => H)
      (fun Q HQ o => conj (fun H => HQ o H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ obs_zero I
}.

(* The universe of binary trees - branching possibilities *)
Inductive BinaryTree (A : Type) : Type :=
  | leaf : A -> BinaryTree A
  | node : BinaryTree A -> BinaryTree A -> BinaryTree A.

Instance Alpha_tree (A : Type) (HA : A) : AlphaType := {
  Alphacarrier := BinaryTree A;
  alpha_impossibility := exist _ (fun _ : BinaryTree A => False)
    (conj
      (fun (t : BinaryTree A) (H : False) => H)
      (fun Q HQ t => conj (fun H => HQ t H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ (leaf A HA) I
}.

(* ============================================================ *)
(*              Dependent/Advanced Instances                    *)
(* ============================================================ *)

(* Sigma types - the universe of dependent pairs *)
Instance Alpha_sigma (A : Type) (B : A -> Type) 
  (HA : A) (HB : B HA) : AlphaType := {
  Alphacarrier := {a : A & B a};
  alpha_impossibility := exist _ (fun _ : {a : A & B a} => False)
    (conj
      (fun (s : {a : A & B a}) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ (existT _ HA HB) I
}.

(* Finite types via Fin n *)

Instance Alpha_finite (n : nat) : AlphaType := {
  Alphacarrier := Fin.t (S n); (* n+1 elements, so non-empty *)
  alpha_impossibility := exist _ (fun _ : Fin.t (S n) => False)
    (conj
      (fun (f : Fin.t (S n)) (H : False) => H)
      (fun Q HQ f => conj (fun H => HQ f H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ Fin.F1 I
}.

(* ============================================================ *)
(*                    Quotient/Equivalence Types                *)
(* ============================================================ *)

(* Modular arithmetic - the universe of cyclic time *)
Definition Zmod (n : nat) := {m : nat | m < S n}.

Instance Alpha_Zmod (n : nat) : AlphaType := {
  Alphacarrier := Zmod n;
  alpha_impossibility := exist _ (fun _ : Zmod n => False)
    (conj
      (fun (z : Zmod n) (H : False) => H)
      (fun Q HQ z => conj (fun H => HQ z H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ (exist _ 0 (Nat.lt_0_succ n)) I
}.

(* ============================================================ *)
(*                    Exotic Instance: Streams                  *)
(* ============================================================ *)

(* Streams - the universe of infinite sequences *)
CoInductive Stream (A : Type) : Type :=
  | Cons : A -> Stream A -> Stream A.

CoFixpoint repeat {A : Type} (a : A) : Stream A := 
  Cons A a (repeat a).

Instance Alpha_stream (A : Type) (HA : A) : AlphaType := {
  Alphacarrier := Stream A;
  alpha_impossibility := exist _ (fun _ : Stream A => False)
    (conj
      (fun (s : Stream A) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ (repeat HA) I
}.


Set Universe Polymorphism.

(* Define AlphaType at each universe level *)
Record AlphaCarrier@{u} : Type@{u+1} := mkAlpha {
  carrier : Type@{u};
  impossibility : {P : carrier -> Prop | 
    (forall x, ~ P x) /\ 
    (forall Q, (forall x, ~ Q x) -> forall x, Q x <-> P x)};
  non_empty : { x : carrier | True }
}.

(* Lift an AlphaCarrier to a higher universe level *)
Definition lift_alpha@{u v | u < v} (A : AlphaCarrier@{u}) : AlphaCarrier@{v} :=
  mkAlpha (carrier A) (impossibility A) (non_empty A).

(* ============================================================ *)
(*                    Diagonal Universe Construction             *)
(* ============================================================ *)

(* The diagonal universe that escapes any enumeration *)
Definition diagonal_universe@{u v | u < v} (enum : nat -> AlphaCarrier@{u}) : AlphaCarrier@{v} := 
  mkAlpha 
    (* The carrier: sequences of predicates, one from each enumerated universe *)
    (forall n, carrier (enum n) -> Prop)
    
    (* The impossible predicate: constantly False across all universes *)
    (exist _ (fun (f : forall n, carrier (enum n) -> Prop) => False)
      (conj
        (* False has no witnesses *)
        (fun f H => H)
        (* Any other impossible predicate equals False *)
        (fun Q HQ f => conj (fun H => HQ f H) (fun H => False_ind _ H))))
    
    (* Non-empty: the constant True sequence exists *)
    (exist _ (fun n _ => True) I).

(* Define a type that represents "n levels of nesting" all at the same universe *)
(* TowerLevel needs to be one level higher to contain AlphaCarrier *)
Inductive TowerLevel@{u v | u < v} : nat -> Type@{v} :=
  | base_level : TowerLevel 0
  | next_level : forall n, AlphaCarrier@{u} -> TowerLevel n -> TowerLevel (S n).

(* Now build the tower using this indexed type *)
(* Package the level with its inhabitant *)
Definition make_tower_level@{u v | u < v} : AlphaCarrier@{v} :=
  mkAlpha
    {n : nat & TowerLevel@{u v} n}  (* Sigma type: exists n with TowerLevel n *)
    (exist _ (fun _ => False)
      (conj (fun _ H => H)
            (fun Q HQ x => conj (fun H => HQ x H) (fun H => False_ind _ H))))
    (exist _ (existT _ 0 base_level) I).  (* Level 0 with its base *)

(* Meta - Build a tower of universes, each containing the previous *)
(* Not possible to do in coq - universe levels are compile time *)
(* Fixpoint universe_tower@{u} (n : nat) : AlphaCarrier@{u+n} :=
  match n with
  | 0 => mkAlpha 
      unit
      (exist _ (fun _ : unit => False)
        (conj (fun _ H => H)
              (fun Q HQ x => conj (fun H => HQ x H) (fun H => False_ind _ H))))
      (exist _ tt I)
  | S n' => 
      mkAlpha
        (AlphaCarrier@{u+n'})  (* Contains universes from the level below *)
        (exist _ (fun _ : AlphaCarrier@{u+n'} => False)
          (conj (fun _ H => H)
                (fun Q HQ A => conj (fun H => HQ A H) (fun H => False_ind _ H))))
        (exist _ (universe_tower n') I)
  end. *)


(* ============================================================ *)
(*                    Product of Universes                       *)
(* ============================================================ *)

(* Combine two universes into a product universe *)
Definition product_universe@{u} (A B : AlphaCarrier@{u}) : AlphaCarrier@{u} :=
  mkAlpha
    (carrier A * carrier B)
    (exist _ (fun _ : carrier A * carrier B => False)
      (conj (fun _ H => H)
            (fun Q HQ p => conj (fun H => HQ p H) (fun H => False_ind _ H))))
    (match non_empty A, non_empty B with
     | exist _ a _, exist _ b _ => exist _ (a, b) I
     end).

(* ============================================================ *)
(*                    Universe of Functions                      *)
(* ============================================================ *)

(* The universe of functions between two universes *)
Definition function_universe@{u v | u < v} (A B : AlphaCarrier@{u}) : AlphaCarrier@{v} :=
  mkAlpha
    (carrier A -> carrier B)
    (exist _ (fun _ : carrier A -> carrier B => False)
      (conj (fun _ H => H)
            (fun Q HQ f => conj (fun H => HQ f H) (fun H => False_ind _ H))))
    (match non_empty B with
     | exist _ b _ => exist _ (fun _ => b) I
     end).

(* ============================================================ *)
(*              Self-Reference Through Codes                     *)
(* ============================================================ *)

(* A universe that contains "codes" for universes at its own level *)
Inductive UniverseCode@{u} : Type@{u} :=
  | code_unit : UniverseCode
  | code_product : UniverseCode -> UniverseCode -> UniverseCode
  | code_sum : UniverseCode -> UniverseCode -> UniverseCode
  | code_function : UniverseCode -> UniverseCode -> UniverseCode.

(* Interpret codes as actual AlphaCarriers *)
Fixpoint interpret_code@{u} (c : UniverseCode@{u}) : AlphaCarrier@{u} :=
  match c with
  | code_unit => mkAlpha unit 
      (exist _ (fun _ => False) 
        (conj (fun _ H => H) 
              (fun Q HQ _ => conj (fun H => HQ _ H) (fun H => False_ind _ H))))
      (exist _ tt I)
  | code_product c1 c2 => product_universe (interpret_code c1) (interpret_code c2)
  | code_sum c1 c2 => 
      mkAlpha 
        ((carrier (interpret_code c1)) + (carrier (interpret_code c2)))
        (exist _ (fun _ => False)
          (conj (fun _ H => H)
                (fun Q HQ _ => conj (fun H => HQ _ H) (fun H => False_ind _ H))))
        (match non_empty (interpret_code c1) with
         | exist _ a _ => exist _ (inl a) I
         end)
  | code_function _ _ => 
      (* Functions escape! Return a witness to this fact *)
      mkAlpha 
        unit  (* "This space intentionally left incomplete" *)
        (exist _ (fun _ => False)
          (conj (fun _ H => H)
                (fun Q HQ _ => conj (fun H => HQ _ H) (fun H => False_ind _ H))))
        (exist _ tt I)
  end.

(* The function space interpreter - where the magic happens *)
Definition interpret_function_code@{u v | u < v} 
  (c1 c2 : UniverseCode@{u}) : AlphaCarrier@{v} :=
  mkAlpha 
    (carrier (interpret_code@{u} c1) -> carrier (interpret_code@{u} c2))
    (exist _ (fun _ => False)
      (conj (fun _ H => H)
            (fun Q HQ _ => conj (fun H => HQ _ H) (fun H => False_ind _ H))))
    (match non_empty (interpret_code@{u} c2) with
     | exist _ b _ => exist _ (fun _ => b) I
     end).

(* A code that references function spaces *)
Definition higher_code@{u v | u < v} : AlphaCarrier@{v} :=
  interpret_function_code@{u v} code_unit code_unit.

(* Iteration of function space construction *)
Definition function_tower@{u v w | u < v, v < w} : AlphaCarrier@{w} :=
  interpret_function_code@{v w} 
    (code_function code_unit code_unit)  
    code_unit.

(* The self-aware universe can now reference its own function spaces! *)

(* The universe of universe codes - self-referential! *)
Definition code_universe@{u} : AlphaCarrier@{u} :=
  mkAlpha
    UniverseCode@{u}
    (exist _ (fun _ : UniverseCode@{u} => False)
      (conj (fun _ H => H)
            (fun Q HQ _ => conj (fun H => HQ _ H) (fun H => False_ind _ H))))
    (exist _ code_unit I).

Instance Alpha_code_universe : AlphaType := {
  Alphacarrier := UniverseCode;
  alpha_impossibility := exist _ (fun _ : UniverseCode => False)
    (conj 
      (fun _ H => H)
      (fun Q HQ c => conj (fun H => HQ c H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ code_unit I
}.
