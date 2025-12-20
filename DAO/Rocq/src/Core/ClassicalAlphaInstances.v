(** ClassicalAlphaInstances.v - A zoo of ClassicalAlphaType instances *)

Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.
Require Import Coq.Logic.Classical_Prop.
Require Import Stdlib.Init.Datatypes.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Vectors.Fin.
Require Import PeanoNat.
Import ListNotations.

Axiom classic : forall P : Prop, P \/ ~ P.

(* ============================================================ *)
(*                    Basic Type Instances                      *)
(* ============================================================ *)

(* Unit - the singleton classical universe *)
Instance ClassicalAlpha_unit : ClassicalAlphaType := {
  Alphacarrier := unit;
  alpha_impossibility := exist _ (fun _ : unit => False) 
    (conj 
      (fun (x : unit) (H : False) => H)
      (fun (Q : unit -> Prop) (HQ : forall x : unit, ~ Q x) (x : unit) => 
        conj
          (fun (H : Q x) => HQ x H : False)
          (fun (H : False) => False_ind (Q x) H)));
  alpha_not_empty := ex_intro _ tt I;
  alpha_constant_decision := classic
}.

(* Natural numbers - the classical discrete infinity *)
Instance ClassicalAlpha_nat : ClassicalAlphaType := {
  Alphacarrier := nat;
  alpha_impossibility := exist _ (fun _ : nat => False)
    (conj
      (fun (n : nat) (H : False) => H)
      (fun Q HQ n => conj (fun H => HQ n H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ 0 I;
  alpha_constant_decision := classic
}.

(* Booleans - the classical binary universe *)
Instance ClassicalAlpha_bool : ClassicalAlphaType := {
  Alphacarrier := bool;
  alpha_impossibility := exist _ (fun _ : bool => False)
    (conj
      (fun (b : bool) (H : False) => H)
      (fun Q HQ b => conj (fun H => HQ b H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ true I;
  alpha_constant_decision := classic
}.

(* Integers - positive and negative classical infinity *)
Require Import ZArith.
Instance ClassicalAlpha_Z : ClassicalAlphaType := {
  Alphacarrier := Z;
  alpha_impossibility := exist _ (fun _ : Z => False)
    (conj
      (fun (z : Z) (H : False) => H)
      (fun Q HQ z => conj (fun H => HQ z H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ Z0 I;
  alpha_constant_decision := classic
}.

(* ============================================================ *)
(*                    Composite Type Instances                  *)
(* ============================================================ *)

(* Option type - classical maybe monad *)
Instance ClassicalAlpha_option (A : Type) (witness : A) : ClassicalAlphaType := {
  Alphacarrier := option A;
  alpha_impossibility := exist _ (fun _ : option A => False)
    (conj
      (fun (o : option A) (H : False) => H)
      (fun Q HQ o => conj (fun H => HQ o H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (Some witness) I;
  alpha_constant_decision := classic
}.

(* Products - classical Cartesian universes *)
Instance ClassicalAlpha_product (A B : Type) (wa : A) (wb : B) : ClassicalAlphaType := {
  Alphacarrier := A * B;
  alpha_impossibility := exist _ (fun _ : A * B => False)
    (conj
      (fun (p : A * B) (H : False) => H)
      (fun Q HQ p => conj (fun H => HQ p H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (wa, wb) I;
  alpha_constant_decision := classic
}.

(* Sums - classical disjoint unions *)
Instance ClassicalAlpha_sum (A B : Type) (witness : A) : ClassicalAlphaType := {
  Alphacarrier := A + B;
  alpha_impossibility := exist _ (fun _ : A + B => False)
    (conj
      (fun (s : A + B) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (inl witness) I;
  alpha_constant_decision := classic
}.

(* Lists - classical sequences *)
Instance ClassicalAlpha_list (A : Type) : ClassicalAlphaType := {
  Alphacarrier := list A;
  alpha_impossibility := exist _ (fun _ : list A => False)
    (conj
      (fun (l : list A) (H : False) => H)
      (fun Q HQ l => conj (fun H => HQ l H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ nil I;
  alpha_constant_decision := classic
}.

(* ============================================================ *)
(*                    Function Space Instances                  *)
(* ============================================================ *)

(* Functions from finite domain - classical lookup tables *)
Instance ClassicalAlpha_fin_fun (n : nat) (B : Type) (default : B) : ClassicalAlphaType := {
  Alphacarrier := Fin.t n -> B;
  alpha_impossibility := exist _ (fun _ : Fin.t n -> B => False)
    (conj
      (fun (f : Fin.t n -> B) (H : False) => H)
      (fun Q HQ f => conj (fun H => HQ f H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (fun _ => default) I;
  alpha_constant_decision := classic
}.

(* Partial functions - classical partial maps *)
Instance ClassicalAlpha_partial (A B : Type) : ClassicalAlphaType := {
  Alphacarrier := A -> option B;
  alpha_impossibility := exist _ (fun _ : A -> option B => False)
    (conj
      (fun (f : A -> option B) (H : False) => H)
      (fun Q HQ f => conj (fun H => HQ f H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (fun _ => None) I;
  alpha_constant_decision := classic
}.

(* ============================================================ *)
(*                    Mathematical Structure Instances           *)
(* ============================================================ *)

(* Rational numbers *)
Require Import QArith.
Instance ClassicalAlpha_Q : ClassicalAlphaType := {
  Alphacarrier := Q;
  alpha_impossibility := exist _ (fun _ : Q => False)
    (conj
      (fun (q : Q) (H : False) => H)
      (fun P HP q => conj (fun H => HP q H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (0#1) I;
  alpha_constant_decision := classic
}.

(* Binary trees - classical hierarchical structures *)
Inductive BinaryTree (A : Type) : Type :=
  | Leaf : A -> BinaryTree A
  | Node : BinaryTree A -> BinaryTree A -> BinaryTree A.

Instance ClassicalAlpha_tree (A : Type) (witness : A) : ClassicalAlphaType := {
  Alphacarrier := BinaryTree A;
  alpha_impossibility := exist _ (fun _ : BinaryTree A => False)
    (conj
      (fun (t : BinaryTree A) (H : False) => H)
      (fun Q HQ t => conj (fun H => HQ t H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (Leaf A witness) I;
  alpha_constant_decision := classic
}.

(* ============================================================ *)
(*                    Set-theoretic Instances                   *)
(* ============================================================ *)

(* Finite sets as lists without duplicates *)
Require Import Coq.Lists.ListSet.
Instance ClassicalAlpha_set (A : Type) : ClassicalAlphaType := {
  Alphacarrier := set A;  (* This is list A in Coq's ListSet *)
  alpha_impossibility := exist _ (fun _ : set A => False)
    (conj
      (fun (s : set A) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (empty_set A) I;
  alpha_constant_decision := classic
}.

(* Finite maps - classical dictionaries *)
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Module Import M := FMapList.Make(Nat_as_OT).

Instance ClassicalAlpha_map (V : Type) : ClassicalAlphaType := {
  Alphacarrier := M.t V;
  alpha_impossibility := exist _ (fun _ : M.t V => False)
    (conj
      (fun (m : M.t V) (H : False) => H)
      (fun Q HQ m => conj (fun H => HQ m H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (M.empty V) I;
  alpha_constant_decision := classic
}.

(* ============================================================ *)
(*                    Dependent Type Instances                  *)
(* ============================================================ *)

(* Sigma types - classical dependent pairs *)
Instance ClassicalAlpha_sigma (A : Type) (B : A -> Type) 
  (wa : A) (wb : B wa) : ClassicalAlphaType := {
  Alphacarrier := {a : A & B a};
  alpha_impossibility := exist _ (fun _ : {a : A & B a} => False)
    (conj
      (fun (s : {a : A & B a}) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (existT _ wa wb) I;
  alpha_constant_decision := classic
}.

(* Vectors - length-indexed lists *)
Require Import Coq.Vectors.Vector.
Instance ClassicalAlpha_vector (A : Type) (n : nat) (default : A) : ClassicalAlphaType := {
  Alphacarrier := Vector.t A n;
  alpha_impossibility := exist _ (fun _ : Vector.t A n => False)
    (conj
      (fun (v : Vector.t A n) (H : False) => H)
      (fun Q HQ v => conj (fun H => HQ v H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (Vector.const default n) I;
  alpha_constant_decision := classic
}.

(* ============================================================ *)
(*                    Exotic Instances                          *)
(* ============================================================ *)

(* Coinductive streams - classical infinite sequences *)
CoInductive Stream (A : Type) : Type :=
  | Cons : A -> Stream A -> Stream A.

CoFixpoint repeat {A : Type} (a : A) : Stream A := 
  Cons A a (repeat a).

Instance ClassicalAlpha_stream (A : Type) (witness : A) : ClassicalAlphaType := {
  Alphacarrier := Stream A;
  alpha_impossibility := exist _ (fun _ : Stream A => False)
    (conj
      (fun (s : Stream A) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (repeat witness) I;
  alpha_constant_decision := classic
}.

(* Lazy lists - potentially infinite classical sequences *)
CoInductive LazyList (A : Type) : Type :=
  | LNil : LazyList A
  | LCons : A -> LazyList A -> LazyList A.

Instance ClassicalAlpha_lazy_list (A : Type) : ClassicalAlphaType := {
  Alphacarrier := LazyList A;
  alpha_impossibility := exist _ (fun _ : LazyList A => False)
    (conj
      (fun (l : LazyList A) (H : False) => H)
      (fun Q HQ l => conj (fun H => HQ l H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ (LNil A) I;
  alpha_constant_decision := classic
}.

(* String - classical text *)
Require Import Coq.Strings.String.
Instance ClassicalAlpha_string : ClassicalAlphaType := {
  Alphacarrier := string;
  alpha_impossibility := exist _ (fun _ : string => False)
    (conj
      (fun (s : string) (H : False) => H)
      (fun Q HQ s => conj (fun H => HQ s H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ EmptyString I;
  alpha_constant_decision := classic
}.

(* ASCII characters *)
Require Import Coq.Strings.Ascii.
Instance ClassicalAlpha_ascii : ClassicalAlphaType := {
  Alphacarrier := ascii;
  alpha_impossibility := exist _ (fun _ : ascii => False)
    (conj
      (fun (a : ascii) (H : False) => H)
      (fun Q HQ a => conj (fun H => HQ a H) (fun H => False_ind _ H)));
  alpha_not_empty := ex_intro _ zero I;
  alpha_constant_decision := classic
}.