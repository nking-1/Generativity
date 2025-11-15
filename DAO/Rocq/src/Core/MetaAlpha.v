(** MetaAlpha.v: AlphaType at meta-level *)

Require Import DAO.Core.AlphaType.

Set Universe Polymorphism.

(* Define AlphaCarrier record at each universe level *)
Record AlphaCarrier@{u} : Type@{u+1} := mkAlpha {
  carrier : Type@{u};
  impossibility : {P : carrier -> Prop | 
    (forall x, ~ P x) /\ 
    (forall Q, (forall x, ~ Q x) -> forall x, Q x <-> P x)};
  non_empty : { x : carrier | True }
}.

Section MetaAlpha.
  
  Universe u v.
  Constraint u < v.
  
  (* The impossible predicate on AlphaCarriers *)
  Definition meta_omega_veil : AlphaCarrier@{u} -> Prop :=
    fun A => False.
  
  Lemma meta_omega_veil_has_no_witnesses :
    forall A : AlphaCarrier@{u}, ~ meta_omega_veil A.
  Proof.
    intros A H. exact H.
  Qed.
  
  Lemma meta_omega_veil_unique :
    forall Q : AlphaCarrier@{u} -> Prop,
    (forall A, ~ Q A) ->
    forall A, Q A <-> meta_omega_veil A.
  Proof.
    intros Q HQ A.
    unfold meta_omega_veil.
    split; intro H.
    - exfalso. exact (HQ A H).
    - exfalso. exact H.
  Qed.
  
  (* Need a witness AlphaCarrier at level u *)
  Definition nat_carrier : AlphaCarrier@{u} :=
    mkAlpha nat
      (exist _ (fun _ => False)
        (conj (fun _ H => H)
              (fun Q HQ n => conj (fun H => HQ n H) (fun H => False_ind _ H))))
      (exist _ 0 I).
  
  (* Now construct AlphaCarrier@{v} with carrier = AlphaCarrier@{u} *)
  Definition AlphaCarrier_is_alpha : AlphaCarrier@{v} :=
    mkAlpha 
      (AlphaCarrier@{u})
      (exist _ meta_omega_veil
        (conj meta_omega_veil_has_no_witnesses
              meta_omega_veil_unique))
      (exist _ nat_carrier I).
  
End MetaAlpha.