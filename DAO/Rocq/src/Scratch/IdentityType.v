(* The identity type is actually built in as 'eq', but let's define our own *)

Inductive Path {A : Type} : A -> A -> Type :=
  | refl : forall (x : A), Path x x.

(* 
  This says: Path is a type family indexed by two elements of A.
  The only constructor is refl, which gives a path from x to itself.
*)

(* We can prove symmetry: if there's a path from x to y, there's one from y to x *)
Definition sym {A : Type} {x y : A} (p : Path x y) : Path y x :=
  match p with
  | refl x => refl x
  end.

(* Transitivity: paths compose *)
Definition trans {A : Type} {x y z : A} (p : Path x y) (q : Path y z) : Path x z :=
  match q in Path y' z' return Path x y' -> Path x z' with
  | refl _ => fun p' => p'
  end p.

(* Transport: if x = y, we can move stuff from P(x) to P(y) *)
Definition transport {A : Type} {x y : A} (P : A -> Type) (p : Path x y) : P x -> P y :=
  match p with
  | refl _ => fun px => px
  end.

(* The J rule in its full glory *)
Definition J {A : Type} 
             (P : forall (x y : A), Path x y -> Type)
             (d : forall (x : A), P x x (refl x))
             {x y : A} 
             (p : Path x y) 
           : P x y p :=
  match p with
  | refl x => d x
  end.

(* 
  J says: to prove P holds for any path p : x = y,
  it suffices to prove P holds for refl.
  
  This is path induction - the fundamental elimination principle.
*)

(* Let's prove something: transport along refl is the identity *)
Definition transport_refl {A : Type} {x : A} (P : A -> Type) (px : P x) 
  : Path (transport P (refl x) px) px 
  := refl px.

(* Functions preserve paths (they're "functorial") *)
Definition ap {A B : Type} (f : A -> B) {x y : A} (p : Path x y) : Path (f x) (f y) :=
  match p with
  | refl x => refl (f x)
  end.

(* Functional extensionality: if two functions agree on all inputs, they're equal *)

(* First, let's state what we want to prove *)
Definition funext_statement := forall (A B : Type) (f g : A -> B),
  (forall x, Path (f x) (g x)) -> Path f g.

(* Let's try to prove it *)
(* Definition funext_attempt : funext_statement :=
  fun A B f g H =>  *)
    (* H : forall x, Path (f x) (g x) *)
    (* We need to produce: Path f g *)
    
    (* What can we do?
       - We can't pattern match on H, because it's a function, not a path
       - We can pick a specific x and get H x : Path (f x) (g x)
       - But a path between outputs doesn't give us a path between functions
       - We have no way to "bundle up" all the pointwise paths into one path
    *)
    
    (* We're stuck. There's no term we can write here. *)

(* If f = g, then f x = g x for any x. This is easy. *)
Definition happly {A B : Type} {f g : A -> B} (p : Path f g) (x : A) : Path (f x) (g x) :=
  match p in Path f' g' return Path (f' x) (g' x) with
  | refl h => refl (h x)
  end.

(* Left unit: composing with refl on the left does nothing *)
Definition trans_refl_l {A : Type} {x y : A} (p : Path x y) 
  : Path (trans (refl x) p) p :=
  match p with
  | refl x => refl (refl x)
  end.

(* Right unit: composing with refl on the right does nothing *)
Definition trans_refl_r {A : Type} {x y : A} (p : Path x y) 
  : Path (trans p (refl y)) p :=
  match p with
  | refl x => refl (refl x)
  end.

(* Left inverse: p composed with its inverse is refl *)
Definition trans_sym_l {A : Type} {x y : A} (p : Path x y)
  : Path (trans (sym p) p) (refl y) :=
  match p with
  | refl x => refl (refl x)
  end.

(* Right inverse: inverse composed with p is refl *)
Definition trans_sym_r {A : Type} {x y : A} (p : Path x y)
  : Path (trans p (sym p)) (refl x) :=
  match p with
  | refl x => refl (refl x)
  end.

(* Associativity of path composition *)
Definition trans_assoc {A : Type} {x y z w : A} 
  (p : Path x y) (q : Path y z) (r : Path z w)
  : Path (trans (trans p q) r) (trans p (trans q r)).
Proof.
  destruct p, q, r.
  exact (refl (refl x)).
Defined.


(* Sigma types - pairs where the second component's type depends on the first *)
Inductive Sigma {A : Type} (B : A -> Type) : Type :=
  | pair : forall (a : A), B a -> Sigma B.

Arguments pair {A B} a b.

(* Projections *)
Definition fst {A : Type} {B : A -> Type} (s : Sigma B) : A :=
  match s with
  | pair a _ => a
  end.

Definition snd {A : Type} {B : A -> Type} (s : Sigma B) : B (fst s) :=
  match s with
  | pair _ b => b
  end.

(* A function has a section if it has a right inverse *)
Definition has_section {A B : Type} (f : A -> B) : Type :=
  Sigma (fun g : B -> A => forall b, Path (f (g b)) b).

(* A function has a retraction if it has a left inverse *)
Definition has_retraction {A B : Type} (f : A -> B) : Type :=
  Sigma (fun g : B -> A => forall a, Path (g (f a)) a).

(* A quasi-equivalence has both *)
Definition is_qequiv {A B : Type} (f : A -> B) : Type :=
  has_section f * has_retraction f.

(* But the right definition of equivalence is more subtle.
   We want the section and retraction to be the *same* function,
   with coherent proofs. *)
Definition is_equiv {A B : Type} (f : A -> B) : Type :=
  Sigma (fun g : B -> A =>
  Sigma (fun eta : forall b, Path (f (g b)) b =>
  Sigma (fun eps : forall a, Path (g (f a)) a =>
    forall a, Path (ap f (eps a)) (eta (f a))))).

(* The equivalence type *)
Definition Equiv (A B : Type) : Type :=
  Sigma (fun f : A -> B => is_equiv f).

(* Univalence says: the canonical map from paths to equivalences is itself an equivalence *)

(* First, paths give equivalences *)
Definition path_to_equiv {A B : Type} (p : Path A B) : Equiv A B.
Proof.
  destruct p.
  exists (fun x => x).  (* identity function *)
  exists (fun x => x).  (* inverse is also identity *)
  exists (fun b => refl b).  (* section proof *)
  exists (fun a => refl a).  (* retraction proof *)
  intro a. exact (refl (refl a)).  (* coherence *)
Defined.

(* Univalence: this map is an equivalence *)
Axiom univalence : forall A B : Type, is_equiv (@path_to_equiv A B).


(* First, we need contractible types *)
Definition is_contr (A : Type) : Type :=
  Sigma (fun center : A => forall a : A, Path center a).

(* A type is a "mere proposition" if any two elements are equal *)
Definition is_prop (A : Type) : Type :=
  forall (x y : A), Path x y.

(* The key insight: singletons are contractible *)
Definition singleton (A : Type) (a : A) : Type :=
  Sigma (fun x : A => Path a x).

Definition singleton_is_contr {A : Type} (a : A) : is_contr (singleton A a).
Proof.
  exists (pair a (refl a)).
  intro s. destruct s as [x p].
  destruct p.
  exact (refl (pair x (refl x))).
Defined.

(* We need: transport in the universe is equivalence *)
Definition transport_is_equiv {A B : Type} (p : Path A B) : is_equiv (transport (fun X => X) p).
Proof.
  destruct p.
  (* transport along refl is identity, which is an equivalence *)
  exists (fun x => x).
  exists (fun b => refl b).
  exists (fun a => refl a).
  intro a. exact (refl (refl a)).
Defined.

(* From univalence, we get that equivalence gives us paths *)
Definition equiv_to_path (A B : Type) : Equiv A B -> Path A B.
Proof.
  intro e.
  (* univalence says path_to_equiv is an equivalence, so it has an inverse *)
  destruct (univalence A B) as [g [eta [eps _]]].
  exact (g e).
Defined.

Definition transport_equiv {A : Type} (P : A -> Type) {x y : A} (p : Path x y) 
  : Equiv (P x) (P y).
Proof.
  destruct p.
  (* When p is refl, transport is the identity function *)
  exists (fun x => x).
  exists (fun x => x).
  exists (fun b => refl b).
  exists (fun a => refl a).
  intro a. exact (refl (refl a)).
Defined.

(* Now postcomp_equiv is easier *)
Definition postcomp_equiv {A B C : Type} (e : Equiv B C) 
  : Equiv (A -> B) (A -> C).
Proof.
  pose (p := equiv_to_path B C e).
  (* Transport in the family (fun X => A -> X) *)
  exact (transport_equiv (fun X => A -> X) p).
Defined.

(* Unit type *)
Inductive Unit : Type := tt : Unit.

(* Unit is contractible *)
Definition unit_is_contr : is_contr Unit.
Proof.
  exists tt.
  intro u. destruct u. exact (refl tt).
Defined.

(* If a type is contractible, it's equivalent to Unit *)
Definition contr_equiv_unit {A : Type} (c : is_contr A) : Equiv A Unit.
Proof.
  exists (fun _ => tt).
  exists (fun _ => fst c).
  exists (fun b => match b return Path tt b with tt => refl tt end).
  exists (fun a => snd c a).
  intro a.
  destruct (snd c a).
  exact (refl (refl tt)).
Defined.

(* From univalence: contractible types are equal to Unit *)
Definition contr_path_unit {A : Type} (c : is_contr A) : Path A Unit.
Proof.
  exact (equiv_to_path A Unit (contr_equiv_unit c)).
Defined.

(* Weak function extensionality - admit this, it's technically involved *)
Axiom weak_funext : forall {A : Type} {B : A -> Type},
  (forall a, is_contr (B a)) -> is_contr (forall a, B a).

(* In a contractible type, all elements are equal *)
Definition contr_all_paths {A : Type} (c : is_contr A) (x y : A) : Path x y.
Proof.
  destruct c as [center p].
  exact (trans (sym (p x)) (p y)).
Defined.

(* Map from (∀x. Σ(y:B). Path (f x) y) to (A -> B) by taking fst *)
Definition section_to_fun {A B : Type} (f : A -> B) 
  (s : forall x, Sigma (fun y : B => Path (f x) y)) : A -> B :=
  fun x => fst (s x).

(* Key lemma: section_to_fun of the canonical f_section is f *)
Definition section_to_fun_f {A B : Type} (f : A -> B) 
  : Path (section_to_fun f (fun x => pair (f x) (refl (f x)))) f.
Proof.
  exact (refl f).
Defined.

(* First we need: paths in sigma types *)
Definition sigma_eq {A : Type} {B : A -> Type} {s t : Sigma B}
  (p : Path (fst s) (fst t)) 
  (q : Path (transport B p (snd s)) (snd t))
  : Path s t.
Proof.
  destruct s as [a b]. destruct t as [a' b'].
  simpl in p. destruct p.
  simpl in q. destruct q.
  exact (refl (pair x x0)).
Defined.

(* And the converse: equal sigmas have equal first components *)
Definition sigma_fst_eq {A : Type} {B : A -> Type} {s t : Sigma B}
  (p : Path s t) : Path (fst s) (fst t).
Proof.
  destruct p. exact (refl (fst x)).
Defined.

(* Singleton type at a point - reformulated *)
Definition singleton' {B : Type} (b : B) : Type :=
  Sigma (fun y : B => Path b y).

Definition singleton'_is_contr {B : Type} (b : B) : is_contr (singleton' b).
Proof.
  exists (pair b (refl b)).
  intro s. destruct s as [y p].
  destruct p.
  exact (refl (pair x (refl x))).
Defined.


Definition funext {A B : Type} (f g : A -> B) 
  : (forall x, Path (f x) (g x)) -> Path f g.
Proof.
  intro H.
  pose (P := fun x : A => Sigma (fun y : B => Path (f x) y)).
  assert (c : forall x, is_contr (P x)).
  { intro x. exact (singleton'_is_contr (f x)). }
  pose (total_contr := weak_funext c).
  pose (f_section := fun x : A => pair (f x) (refl (f x)) : P x).
  pose (g_section := fun x : A => pair (g x) (H x) : P x).
  pose (sections_eq := contr_all_paths total_contr f_section g_section).
  (* ap (section_to_fun f) gives us a path between the underlying functions *)
  exact (ap (section_to_fun f) sections_eq).
Defined.


(* Test: prove that (fun n => n + 0) = (fun n => n) *)
(* First we need natural numbers *)
Inductive Nat : Type :=
  | zero : Nat
  | succ : Nat -> Nat.

Fixpoint add (n m : Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)
  end.

(* Prove n + 0 = n *)
Fixpoint add_zero_r (n : Nat) : Path (add n zero) n :=
  match n with
  | zero => refl zero
  | succ n' => ap succ (add_zero_r n')
  end.

(* Now use funext! *)
Definition add_zero_r_funext : Path (fun n => add n zero) (fun n => n).
Proof.
  apply funext.
  exact add_zero_r.
Defined.