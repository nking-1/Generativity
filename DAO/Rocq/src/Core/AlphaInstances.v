(* AlphaInstances.v - A zoo of AlphaType instances *)
Require Import DAO.Core.AlphaType.
Require Import Stdlib.Init.Datatypes.
Require Import Stdlib.Lists.List.
Require Import PeanoNat.
Require Import Stdlib.Vectors.Fin.

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

(* All Types can be an AlphaType *)
Instance Alpha_universal (T : Type) `{Inhabited T} : AlphaType := {
  Alphacarrier := T;
  alpha_impossibility := exist _ (fun _ : T => False)
    (conj
      (fun (x : T) (H : False) => H)
      (fun Q HQ x => conj (fun H => HQ x H) (fun H => False_ind _ H)));
  alpha_not_empty := exist _ inhabitant I
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

(* ============================================================ *)
(*                    Theorems About the Hierarchy               *)
(* ============================================================ *)

(* Each level of the tower is distinct *)
(* Lemma tower_levels_distinct@{u} : forall n m : nat,
  n <> m ->
  carrier (universe_tower@{u} n) <> carrier (universe_tower@{u} (S m)).
Proof.
  intros n m H_neq.
  (* The carriers have different universe levels, so they can't be equal *)
  simpl.
  (* This would require more detailed proof about universe levels *)
  admit.  (* The full proof would use universe level reasoning *)
Admitted. *)

(* The diagonal universe genuinely escapes *)
(* Theorem diagonal_escapes@{u} : 
  forall (enum : nat -> AlphaCarrier@{u}),
  ~ exists (n : nat), 
    carrier (enum n) = carrier (diagonal_universe enum).
Proof.
  intros enum [n H_eq].
  (* The diagonal has universe level u+1, enum n has level u *)
  (* They can't be equal due to universe inconsistency *)
  (* Full proof would require universe level arithmetic *)
  admit.
Admitted. *)

(* ============================================================ *)
(*                    The Infinite Chase                         *)
(* ============================================================ *)

(* Add a new section: Concrete Ouroboros Demonstration *)

(* Module ConcreteOuroboros.
  
  (* Let's run ouroboros on nat - starting with just omega_veil and one other predicate *)
  Definition nat_predicates_at_stage : nat -> (nat -> Prop) -> Prop :=
    fix stage n :=
      match n with
      | 0 => fun P => P = (fun _ => False) \/ P = (fun x => x = 0)
      | S n' => fun P => 
          stage n' P \/ 
          P = (fun x => exists Q, stage n' Q /\ Q x)
      end.
  
  (* Helper: the totality at each stage *)
  Definition totality_at_stage (n : nat) : nat -> Prop :=
    fun x => exists Q, nat_predicates_at_stage n Q /\ Q x.
  
  (* Show that stages are monotone (everything persists) *)
  Lemma stage_monotone :
    forall n P,
    nat_predicates_at_stage n P ->
    nat_predicates_at_stage (S n) P.
  Proof.
    intros n P H.
    simpl. left. exact H.
  Qed.
  
  (* Show growth: each stage adds something new *)
  Lemma nat_ouroboros_grows :
    forall n,
    nat_predicates_at_stage (S n) (totality_at_stage n) /\
    ~ nat_predicates_at_stage n (totality_at_stage n).
  Proof.
    intro n.
    split.
    - (* The totality appears at the next stage *)
      simpl. right. reflexivity.
    - (* The totality is not in the current stage - this would violate no_static_self_totality *)
      (* For demonstration, we'll show this for stage 0 *)
      destruct n.
      + (* Stage 0: only has False and (= 0) *)
        intro H.
        simpl in H.
        destruct H as [H | H].
        * (* totality_at_stage 0 = False - impossible since it has witnesses *)
          assert (exists x, totality_at_stage 0 x).
          { exists 0. unfold totality_at_stage. 
            exists (fun x => x = 0). split; [right; reflexivity | reflexivity]. }
          destruct H0 as [x Hx].
          rewrite H in Hx.
          exact Hx.
        * (* totality_at_stage 0 = (= 0) - also impossible *)
          (* This would mean: (exists Q at stage 0, Q x) iff (x = 0) *)
          (* But totality_at_stage 0 1 is false while 1 = 0 is false, so they differ *)
          assert (totality_at_stage 0 0).
          { unfold totality_at_stage.
            exists (fun x => x = 0). split; [right; reflexivity | reflexivity]. }
          rewrite H in H0.
          (* Now we'd need to show they're different predicates *)
          (* Let's admit this for now as it gets technical *)
          admit.
      + (* Inductive case - similar reasoning *)
        admit.
  Admitted.
  
  (* Concrete example: count predicates at each stage *)
    Example stage_0_has_two :
        nat_predicates_at_stage 0 (fun _ => False) /\
        nat_predicates_at_stage 0 (fun x => x = 0).
    Proof.
        split.
        - left. reflexivity.
        - right. reflexivity.
    Qed.

  Example stage_0_has_two_admitted :
    nat_predicates_at_stage 0 (fun _ => False) /\
    nat_predicates_at_stage 0 (fun x => x = 0) /\
    ~ nat_predicates_at_stage 0 (fun x => x = 1).
  Proof.
    split; [|split].
    - left. reflexivity.
    - right. reflexivity.
    - (* This requires functional extensionality or a more careful proof *)
      (* The functions (x = 1), False, and (x = 0) are all different *)
      (* but proving this in Coq without extensionality is technical *)
      admit.
  Admitted.
  
  (* The totality of stage 0 *)
  Example totality_0_holds_at_0 :
    totality_at_stage 0 0.
  Proof.
    unfold totality_at_stage.
    exists (fun x => x = 0).
    split.
    - right. reflexivity.
    - reflexivity.
  Qed.
  
  Example totality_0_not_at_1 :
    ~ totality_at_stage 0 1.
  Proof.
    unfold totality_at_stage.
    intros [Q [HQ H1]].
    simpl in HQ.
    destruct HQ as [HQ | HQ].
    - rewrite HQ in H1. exact H1.
    - rewrite HQ in H1. 
      simpl in H1. discriminate.
  Qed.
  
  (* Visualization: Stage 1 has stage 0 plus totality_0 *)
  Example stage_1_contains_totality_0 :
    nat_predicates_at_stage 1 (totality_at_stage 0).
  Proof.
    simpl. right. reflexivity.
  Qed.
  
  (* We can even compute specific values *)
  (* Definition compute_stages (max_stage : nat) : list (nat -> Prop) :=
    (* This would enumerate all predicates up to max_stage *)
    (* For now, just return a placeholder *)
    [(fun _ => False); (fun x => x = 0); totality_at_stage 0]. *)
  
  (* The process never stops *)
  Theorem ouroboros_infinite_on_nat :
    forall n, exists P,
    nat_predicates_at_stage (S n) P /\
    ~ nat_predicates_at_stage n P.
  Proof.
    intro n.
    exists (totality_at_stage n).
    apply nat_ouroboros_grows.
  Qed.
  
End ConcreteOuroboros.


Module ConcreteOuroboros_Tagged.

Inductive Tag : nat -> Type :=
| TFalse : Tag 0
| TZero  : Tag 0
| TOne   : Tag 0
| TKeep  : forall n, Tag n -> Tag (S n)
| TTotal : forall n, Tag (S n).

(* Mutual recursion: denote on t, totality on n *)
Fixpoint denote (n:nat) (t:Tag n) {struct t} : nat -> Prop :=
  match t with
  | TFalse      => fun _ => False
  | TZero       => fun x => x = 0
  | TOne        => fun x => x = 1
  | TKeep _ t'  => denote _ t'
  | TTotal n'   => totality n'
  end
with totality (n:nat) {struct n} : nat -> Prop :=
  fun x => exists (u : Tag n), denote _ u x.

(* Stage membership via tags (pointwise ↔), unchanged in spirit *)
Definition InStage (n:nat) (P:nat -> Prop) : Prop :=
  exists t:Tag n, forall x, P x <-> denote n t x.

(* Canonical totality predicate is just totality n now *)
Definition totality_at_stage (n:nat) : nat -> Prop := totality n.

(* Monotonicity via TKeep *)
Lemma stage_monotone :
  forall n P, InStage n P -> InStage (S n) P.
Proof.
  intros n P [t Heq]. exists (TKeep n t). intro x. simpl. apply Heq.
Qed.

(* Base separation: at level 0, no tag denotes the union {0,1} *)
Lemma sep0 : forall t0 : Tag 0, exists x, totality 0 x /\ ~ denote 0 t0 x.
Proof.
  intros t0. destruct t0.
  - (* TFalse *) exists 0. split; [now (exists TZero)| easy].
  - (* TZero  *) exists 1. split; [now (exists TOne)| now intros ->].
  - (* TOne   *) exists 0. split; [now (exists TZero)| now intros ->].
Qed.

(* Lift separation to any n: for any t:Tag n, there is an x in totality n not in t *)
Lemma sepS :
  forall n (t : Tag n), exists x, totality n x /\ ~ denote n t x.
Proof.
  induction n as [|n IH].
  - apply sep0.
  - intros t. (* t : Tag (S n) *)
    (* t is either TKeep n u or TTotal n; handle by cases. *)
    destruct t as [ (* impossible at S n *) | | | n' u | n'].
    all: try discriminate.
    + (* TKeep n u *)
      destruct (IH u) as [x [Hin Hnot]]. exists x. split; [exact Hin| simpl; exact Hnot].
    + (* TTotal n *)
      (* For TTotal n, pick x separating some u:Tag n from union;
         but union includes u, so contradiction; instead show directly:
         totality (S n) ≡ totality n, so use IH on some carried tag. *)
      (* A simple route: use u:=TZero at level 0, then carry it up with TKeep to level n. *)
      (* Build a tag at level n that certainly holds at some x, then use IH on that tag. *)
      destruct (IH (u:=TZero)) as [x [Hin Hnot]].
      { (* TZero lives at level 0; we need a Tag n. Carry it up n times. *)
        (* Define a helper to lift TZero: *)
        revert x Hin Hnot. (* we’ll rebuild below using a small helper lemma if you prefer *)
        admit. }
Admitted.

(* The key: totality isn’t representable at the same stage *)
Lemma totality_not_in_stage :
  forall n, ~ InStage n (totality n).
Proof.
  intros n [t Heq]. destruct (sepS n t) as [x [Hin Hnot]].
  specialize (Heq x). destruct Heq as [H1 H2]. apply Hnot. apply H2. exact Hin.
Qed.

(* The new thing at S n is exactly totality n, represented by TTotal n *)
Lemma in_next_totality :
  forall n, InStage (S n) (totality n).
Proof.
  intros n. exists (TTotal n). intro x. reflexivity.
Qed.

Theorem ouroboros_infinite_on_nat :
  forall n, exists P, InStage (S n) P /\ ~ InStage n P.
Proof.
  intro n. exists (totality n). split.
  - apply in_next_totality.
  - apply totality_not_in_stage.
Qed.

End ConcreteOuroboros_Tagged. *)


(* ============================================================ *)
(*                    Demonstration                              *)
(* ============================================================ *)
(* 
(* Example: Build a small tower *)
Definition level_0@{u} := universe_tower@{u} 0.
Definition level_1@{u} := universe_tower@{u} 1.  
Definition level_2@{u} := universe_tower@{u} 2.

(* Example: Create a diagonal over the first 3 levels *)
Definition my_enum@{u} (n : nat) : AlphaCarrier@{u} :=
  match n with
  | 0 => level_0
  | 1 => level_0  (* Repeat for simplicity *)
  | _ => level_0
  end.

Definition diagonal_over_levels@{u} := diagonal_universe my_enum.

(* Example: Universe of codes is self-aware *)
Definition self_aware_universe := code_universe.
(* It contains codes that can describe itself! *)

(* Example: Product of universe with itself *)
Definition universe_squared@{u} := product_universe level_0@{u} level_0@{u}.
*)