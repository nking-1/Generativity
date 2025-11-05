(* MinimalAlphaType.v: A non-empty type and what that implies *)

Class MinimalAlphaType := {
  Minalphacarrier : Type;
  min_not_empty : { x : Minalphacarrier | True }
}.

Section MinimalProperties.
  Context `{MinimalAlphaType}.
  
  (** Extract the witness *)
  Definition witness : Minalphacarrier := proj1_sig min_not_empty.
  
  (* ============================================================ *)
  (*          Properties That Need The Witness                    *)
  (* ============================================================ *)
  
  (** The impossible predicate FAILS on the actual witness *)
  Theorem impossible_fails_on_witness :
    ~ (witness <> witness).
  Proof.
    intro Hneq.
    exact (Hneq eq_refl).
  Qed.
  
  (** Different predicates give different results on witness *)
  Theorem predicates_distinguishable :
    exists (P Q : Minalphacarrier -> Prop),
      P witness /\ ~ Q witness.
  Proof.
    exists (fun _ => True), (fun _ => False).
    split.
    - exact I.
    - intro Hfalse. exact Hfalse.
  Qed.
  
  (** Can construct omega_veil that demonstrably fails *)
  Theorem omega_veil_construction :
    exists (impossible : Minalphacarrier -> Prop),
      ~ impossible witness /\
      (forall Q, (forall y, ~ Q y) -> forall y, Q y <-> impossible y).
  Proof.
    exists (fun x => x <> x).
    split.
    - intro Hneq. exact (Hneq eq_refl).
    - intros Q HQ y. split.
      + intro HQy. exfalso. exact (HQ y HQy).
      + intro Hneq. exfalso. exact (Hneq eq_refl).
  Qed.
  
  (* ============================================================ *)
  (*     Properties True Even Without Using The Witness           *)
  (*     (but we state them for completeness)                     *)
  (* ============================================================ *)
  
  (** An impossible predicate syntactically exists *)
  Theorem impossible_predicate_exists :
    exists P : Minalphacarrier -> Prop, forall x, ~ P x.
  Proof.
    exists (fun x => x <> x).
    intros x Hneq.
    exact (Hneq eq_refl).
  Qed.
  
  (** A universal predicate syntactically exists *)
  Theorem universal_predicate_exists :
    exists P : Minalphacarrier -> Prop, forall x, P x.
  Proof.
    exists (fun _ => True).
    intros x.
    exact I.
  Qed.
  
  (** Negation structure exists syntactically *)
  Theorem negation_exists :
    forall P : Minalphacarrier -> Prop,
    exists Q : Minalphacarrier -> Prop, 
      forall x, Q x <-> ~ P x.
  Proof.
    intro P.
    exists (fun x => ~ P x).
    intro x.
    split; intro Hneg; exact Hneg.
  Qed.
  
  (** All impossible predicates are pointwise equivalent *)
  Theorem all_impossible_predicates_pointwise_equal :
    forall P Q : Minalphacarrier -> Prop,
    (forall x, ~ P x) -> (forall x, ~ Q x) ->
    forall x, P x <-> Q x.
  Proof.
    intros P Q HP HQ x.
    split; intro H'.
    - exfalso. exact (HP x H').
    - exfalso. exact (HQ x H').
  Qed.
  
  (** From just non-emptiness, we can distinguish True and False *)
  Theorem non_emptiness_gives_logic :
    (* We have a witness *)
    (exists w : Minalphacarrier, True) /\
    (* Impossible predicate fails on it *)
    (exists impossible : Minalphacarrier -> Prop, ~ impossible witness) /\
    (* Universal predicate holds on it *)
    (exists top : Minalphacarrier -> Prop, top witness) /\
    (* They're distinguished *)
    (exists P Q : Minalphacarrier -> Prop, P witness /\ ~ Q witness).
  Proof.
    destruct min_not_empty as [w _].
    split.
    - exists w. exact I.
    - split.
      + exists (fun x => x <> x). intro Hneq. exact (Hneq eq_refl).
      + split.
        * exists (fun _ => True). exact I.
        * exists (fun _ => True), (fun _ => False). split.
          -- exact I.
          -- intro Hfalse. exact Hfalse.
  Qed.
  
End MinimalProperties.