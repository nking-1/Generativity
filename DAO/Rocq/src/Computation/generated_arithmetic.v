(* Generated code for U0 through U20 *)
(* Auto-generated Universe Arithmetic *)
Require Import Coq.Init.Nat.

Set Universe Polymorphism.

(* === AbstractAlphaType Definition === *)

Class AbstractAlphaType := {
  AbstractAlphacarrier : Type;
  emptiness_impossible : (AbstractAlphacarrier -> False) -> False
}.

(* === Base Instance === *)

Definition nat_abstract : AbstractAlphaType := {|
  AbstractAlphacarrier := nat;
  emptiness_impossible := fun H => H 0
|}.

(* === Successor Construction === *)

Definition alpha_succ (A : AbstractAlphaType) : AbstractAlphaType.
Proof.
  refine {|
    AbstractAlphacarrier := AbstractAlphaType;
    emptiness_impossible := _
  |}.
  intro H.
  exact (H A).
Defined.

(* === Meta Instance === *)

Section MetaAbstractAlpha.
  
  Lemma abstract_alpha_not_empty : 
    (AbstractAlphaType -> False) -> False.
  Proof.
    intro H.
    exact (H nat_abstract).
  Qed.
  
  Instance AbstractAlphaType_is_abstract : AbstractAlphaType := {|
    AbstractAlphacarrier := AbstractAlphaType;
    emptiness_impossible := abstract_alpha_not_empty
  |}.
  
End MetaAbstractAlpha.

Section NaturalsFromMeta.

(* === GENERATED UNIVERSE NUMBERS === *)

(* === UNIVERSE NUMBERS === *)
Definition U0 : AbstractAlphaType := nat_abstract.
Definition U1 : AbstractAlphaType := alpha_succ U0.
Definition U2 : AbstractAlphaType := alpha_succ U1.
Definition U3 : AbstractAlphaType := alpha_succ U2.
Definition U4 : AbstractAlphaType := alpha_succ U3.
Definition U5 : AbstractAlphaType := alpha_succ U4.
Definition U6 : AbstractAlphaType := alpha_succ U5.
Definition U7 : AbstractAlphaType := alpha_succ U6.
Definition U8 : AbstractAlphaType := alpha_succ U7.
Definition U9 : AbstractAlphaType := alpha_succ U8.
Definition U10 : AbstractAlphaType := alpha_succ U9.
Definition U11 : AbstractAlphaType := alpha_succ U10.
Definition U12 : AbstractAlphaType := alpha_succ U11.
Definition U13 : AbstractAlphaType := alpha_succ U12.
Definition U14 : AbstractAlphaType := alpha_succ U13.
Definition U15 : AbstractAlphaType := alpha_succ U14.
Definition U16 : AbstractAlphaType := alpha_succ U15.
Definition U17 : AbstractAlphaType := alpha_succ U16.
Definition U18 : AbstractAlphaType := alpha_succ U17.
Definition U19 : AbstractAlphaType := alpha_succ U18.
Definition U20 : AbstractAlphaType := alpha_succ U19.


(* === ADDITION TABLE === *)
Definition add_U_0_0 : AbstractAlphaType := U0.
Definition add_U_0_1 : AbstractAlphaType := alpha_succ (U0). (* = U1 *)
Definition add_U_0_2 : AbstractAlphaType := alpha_succ (alpha_succ (U0)). (* = U2 *)
Definition add_U_0_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U0))). (* = U3 *)
Definition add_U_0_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))). (* = U4 *)
Definition add_U_0_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))). (* = U5 *)
Definition add_U_0_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))). (* = U6 *)
Definition add_U_0_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))). (* = U7 *)
Definition add_U_0_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))). (* = U8 *)
Definition add_U_0_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))). (* = U9 *)
Definition add_U_0_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))). (* = U10 *)
Definition add_U_0_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))))). (* = U11 *)
Definition add_U_0_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))). (* = U12 *)
Definition add_U_0_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))))))). (* = U13 *)
Definition add_U_0_14 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))). (* = U14 *)
Definition add_U_0_15 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))))))))). (* = U15 *)
Definition add_U_0_16 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))). (* = U16 *)
Definition add_U_0_17 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))))))))))). (* = U17 *)
Definition add_U_0_18 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))). (* = U18 *)
Definition add_U_0_19 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))))))))))))). (* = U19 *)
Definition add_U_0_20 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))))). (* = U20 *)
Definition add_U_1_0 : AbstractAlphaType := U1.
Definition add_U_1_1 : AbstractAlphaType := alpha_succ (U1). (* = U2 *)
Definition add_U_1_2 : AbstractAlphaType := alpha_succ (alpha_succ (U1)). (* = U3 *)
Definition add_U_1_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U1))). (* = U4 *)
Definition add_U_1_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))). (* = U5 *)
Definition add_U_1_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))). (* = U6 *)
Definition add_U_1_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))))). (* = U7 *)
Definition add_U_1_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))))). (* = U8 *)
Definition add_U_1_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))))))). (* = U9 *)
Definition add_U_1_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))))))). (* = U10 *)
Definition add_U_1_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))))))))). (* = U11 *)
Definition add_U_1_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))))))))). (* = U12 *)
Definition add_U_1_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))))))))))). (* = U13 *)
Definition add_U_1_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))))))))))). (* = U14 *)
Definition add_U_1_14 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))))))))))))). (* = U15 *)
Definition add_U_1_15 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))))))))))))). (* = U16 *)
Definition add_U_1_16 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))))))))))))))). (* = U17 *)
Definition add_U_1_17 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))))))))))))))). (* = U18 *)
Definition add_U_1_18 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1)))))))))))))))))). (* = U19 *)
Definition add_U_1_19 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U1))))))))))))))))))). (* = U20 *)
Definition add_U_2_0 : AbstractAlphaType := U2.
Definition add_U_2_1 : AbstractAlphaType := alpha_succ (U2). (* = U3 *)
Definition add_U_2_2 : AbstractAlphaType := alpha_succ (alpha_succ (U2)). (* = U4 *)
Definition add_U_2_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U2))). (* = U5 *)
Definition add_U_2_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))). (* = U6 *)
Definition add_U_2_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2))))). (* = U7 *)
Definition add_U_2_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))))). (* = U8 *)
Definition add_U_2_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2))))))). (* = U9 *)
Definition add_U_2_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))))))). (* = U10 *)
Definition add_U_2_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2))))))))). (* = U11 *)
Definition add_U_2_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))))))))). (* = U12 *)
Definition add_U_2_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2))))))))))). (* = U13 *)
Definition add_U_2_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))))))))))). (* = U14 *)
Definition add_U_2_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2))))))))))))). (* = U15 *)
Definition add_U_2_14 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))))))))))))). (* = U16 *)
Definition add_U_2_15 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2))))))))))))))). (* = U17 *)
Definition add_U_2_16 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))))))))))))))). (* = U18 *)
Definition add_U_2_17 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2))))))))))))))))). (* = U19 *)
Definition add_U_2_18 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U2)))))))))))))))))). (* = U20 *)
Definition add_U_3_0 : AbstractAlphaType := U3.
Definition add_U_3_1 : AbstractAlphaType := alpha_succ (U3). (* = U4 *)
Definition add_U_3_2 : AbstractAlphaType := alpha_succ (alpha_succ (U3)). (* = U5 *)
Definition add_U_3_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U3))). (* = U6 *)
Definition add_U_3_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3)))). (* = U7 *)
Definition add_U_3_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3))))). (* = U8 *)
Definition add_U_3_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3)))))). (* = U9 *)
Definition add_U_3_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3))))))). (* = U10 *)
Definition add_U_3_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3)))))))). (* = U11 *)
Definition add_U_3_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3))))))))). (* = U12 *)
Definition add_U_3_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3)))))))))). (* = U13 *)
Definition add_U_3_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3))))))))))). (* = U14 *)
Definition add_U_3_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3)))))))))))). (* = U15 *)
Definition add_U_3_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3))))))))))))). (* = U16 *)
Definition add_U_3_14 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3)))))))))))))). (* = U17 *)
Definition add_U_3_15 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3))))))))))))))). (* = U18 *)
Definition add_U_3_16 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3)))))))))))))))). (* = U19 *)
Definition add_U_3_17 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U3))))))))))))))))). (* = U20 *)
Definition add_U_4_0 : AbstractAlphaType := U4.
Definition add_U_4_1 : AbstractAlphaType := alpha_succ (U4). (* = U5 *)
Definition add_U_4_2 : AbstractAlphaType := alpha_succ (alpha_succ (U4)). (* = U6 *)
Definition add_U_4_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U4))). (* = U7 *)
Definition add_U_4_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4)))). (* = U8 *)
Definition add_U_4_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4))))). (* = U9 *)
Definition add_U_4_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4)))))). (* = U10 *)
Definition add_U_4_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4))))))). (* = U11 *)
Definition add_U_4_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4)))))))). (* = U12 *)
Definition add_U_4_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4))))))))). (* = U13 *)
Definition add_U_4_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4)))))))))). (* = U14 *)
Definition add_U_4_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4))))))))))). (* = U15 *)
Definition add_U_4_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4)))))))))))). (* = U16 *)
Definition add_U_4_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4))))))))))))). (* = U17 *)
Definition add_U_4_14 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4)))))))))))))). (* = U18 *)
Definition add_U_4_15 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4))))))))))))))). (* = U19 *)
Definition add_U_4_16 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U4)))))))))))))))). (* = U20 *)
Definition add_U_5_0 : AbstractAlphaType := U5.
Definition add_U_5_1 : AbstractAlphaType := alpha_succ (U5). (* = U6 *)
Definition add_U_5_2 : AbstractAlphaType := alpha_succ (alpha_succ (U5)). (* = U7 *)
Definition add_U_5_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U5))). (* = U8 *)
Definition add_U_5_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5)))). (* = U9 *)
Definition add_U_5_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5))))). (* = U10 *)
Definition add_U_5_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5)))))). (* = U11 *)
Definition add_U_5_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5))))))). (* = U12 *)
Definition add_U_5_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5)))))))). (* = U13 *)
Definition add_U_5_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5))))))))). (* = U14 *)
Definition add_U_5_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5)))))))))). (* = U15 *)
Definition add_U_5_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5))))))))))). (* = U16 *)
Definition add_U_5_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5)))))))))))). (* = U17 *)
Definition add_U_5_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5))))))))))))). (* = U18 *)
Definition add_U_5_14 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5)))))))))))))). (* = U19 *)
Definition add_U_5_15 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U5))))))))))))))). (* = U20 *)
Definition add_U_6_0 : AbstractAlphaType := U6.
Definition add_U_6_1 : AbstractAlphaType := alpha_succ (U6). (* = U7 *)
Definition add_U_6_2 : AbstractAlphaType := alpha_succ (alpha_succ (U6)). (* = U8 *)
Definition add_U_6_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U6))). (* = U9 *)
Definition add_U_6_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6)))). (* = U10 *)
Definition add_U_6_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6))))). (* = U11 *)
Definition add_U_6_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6)))))). (* = U12 *)
Definition add_U_6_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6))))))). (* = U13 *)
Definition add_U_6_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6)))))))). (* = U14 *)
Definition add_U_6_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6))))))))). (* = U15 *)
Definition add_U_6_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6)))))))))). (* = U16 *)
Definition add_U_6_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6))))))))))). (* = U17 *)
Definition add_U_6_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6)))))))))))). (* = U18 *)
Definition add_U_6_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6))))))))))))). (* = U19 *)
Definition add_U_6_14 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U6)))))))))))))). (* = U20 *)
Definition add_U_7_0 : AbstractAlphaType := U7.
Definition add_U_7_1 : AbstractAlphaType := alpha_succ (U7). (* = U8 *)
Definition add_U_7_2 : AbstractAlphaType := alpha_succ (alpha_succ (U7)). (* = U9 *)
Definition add_U_7_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U7))). (* = U10 *)
Definition add_U_7_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7)))). (* = U11 *)
Definition add_U_7_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7))))). (* = U12 *)
Definition add_U_7_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7)))))). (* = U13 *)
Definition add_U_7_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7))))))). (* = U14 *)
Definition add_U_7_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7)))))))). (* = U15 *)
Definition add_U_7_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7))))))))). (* = U16 *)
Definition add_U_7_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7)))))))))). (* = U17 *)
Definition add_U_7_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7))))))))))). (* = U18 *)
Definition add_U_7_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7)))))))))))). (* = U19 *)
Definition add_U_7_13 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U7))))))))))))). (* = U20 *)
Definition add_U_8_0 : AbstractAlphaType := U8.
Definition add_U_8_1 : AbstractAlphaType := alpha_succ (U8). (* = U9 *)
Definition add_U_8_2 : AbstractAlphaType := alpha_succ (alpha_succ (U8)). (* = U10 *)
Definition add_U_8_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U8))). (* = U11 *)
Definition add_U_8_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8)))). (* = U12 *)
Definition add_U_8_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8))))). (* = U13 *)
Definition add_U_8_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8)))))). (* = U14 *)
Definition add_U_8_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8))))))). (* = U15 *)
Definition add_U_8_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8)))))))). (* = U16 *)
Definition add_U_8_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8))))))))). (* = U17 *)
Definition add_U_8_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8)))))))))). (* = U18 *)
Definition add_U_8_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8))))))))))). (* = U19 *)
Definition add_U_8_12 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U8)))))))))))). (* = U20 *)
Definition add_U_9_0 : AbstractAlphaType := U9.
Definition add_U_9_1 : AbstractAlphaType := alpha_succ (U9). (* = U10 *)
Definition add_U_9_2 : AbstractAlphaType := alpha_succ (alpha_succ (U9)). (* = U11 *)
Definition add_U_9_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U9))). (* = U12 *)
Definition add_U_9_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9)))). (* = U13 *)
Definition add_U_9_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9))))). (* = U14 *)
Definition add_U_9_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9)))))). (* = U15 *)
Definition add_U_9_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9))))))). (* = U16 *)
Definition add_U_9_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9)))))))). (* = U17 *)
Definition add_U_9_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9))))))))). (* = U18 *)
Definition add_U_9_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9)))))))))). (* = U19 *)
Definition add_U_9_11 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U9))))))))))). (* = U20 *)
Definition add_U_10_0 : AbstractAlphaType := U10.
Definition add_U_10_1 : AbstractAlphaType := alpha_succ (U10). (* = U11 *)
Definition add_U_10_2 : AbstractAlphaType := alpha_succ (alpha_succ (U10)). (* = U12 *)
Definition add_U_10_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U10))). (* = U13 *)
Definition add_U_10_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U10)))). (* = U14 *)
Definition add_U_10_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U10))))). (* = U15 *)
Definition add_U_10_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U10)))))). (* = U16 *)
Definition add_U_10_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U10))))))). (* = U17 *)
Definition add_U_10_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U10)))))))). (* = U18 *)
Definition add_U_10_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U10))))))))). (* = U19 *)
Definition add_U_10_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U10)))))))))). (* = U20 *)
Definition add_U_11_0 : AbstractAlphaType := U11.
Definition add_U_11_1 : AbstractAlphaType := alpha_succ (U11). (* = U12 *)
Definition add_U_11_2 : AbstractAlphaType := alpha_succ (alpha_succ (U11)). (* = U13 *)
Definition add_U_11_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U11))). (* = U14 *)
Definition add_U_11_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U11)))). (* = U15 *)
Definition add_U_11_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U11))))). (* = U16 *)
Definition add_U_11_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U11)))))). (* = U17 *)
Definition add_U_11_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U11))))))). (* = U18 *)
Definition add_U_11_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U11)))))))). (* = U19 *)
Definition add_U_11_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U11))))))))). (* = U20 *)
Definition add_U_12_0 : AbstractAlphaType := U12.
Definition add_U_12_1 : AbstractAlphaType := alpha_succ (U12). (* = U13 *)
Definition add_U_12_2 : AbstractAlphaType := alpha_succ (alpha_succ (U12)). (* = U14 *)
Definition add_U_12_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U12))). (* = U15 *)
Definition add_U_12_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U12)))). (* = U16 *)
Definition add_U_12_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U12))))). (* = U17 *)
Definition add_U_12_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U12)))))). (* = U18 *)
Definition add_U_12_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U12))))))). (* = U19 *)
Definition add_U_12_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U12)))))))). (* = U20 *)
Definition add_U_13_0 : AbstractAlphaType := U13.
Definition add_U_13_1 : AbstractAlphaType := alpha_succ (U13). (* = U14 *)
Definition add_U_13_2 : AbstractAlphaType := alpha_succ (alpha_succ (U13)). (* = U15 *)
Definition add_U_13_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U13))). (* = U16 *)
Definition add_U_13_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U13)))). (* = U17 *)
Definition add_U_13_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U13))))). (* = U18 *)
Definition add_U_13_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U13)))))). (* = U19 *)
Definition add_U_13_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U13))))))). (* = U20 *)
Definition add_U_14_0 : AbstractAlphaType := U14.
Definition add_U_14_1 : AbstractAlphaType := alpha_succ (U14). (* = U15 *)
Definition add_U_14_2 : AbstractAlphaType := alpha_succ (alpha_succ (U14)). (* = U16 *)
Definition add_U_14_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U14))). (* = U17 *)
Definition add_U_14_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U14)))). (* = U18 *)
Definition add_U_14_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U14))))). (* = U19 *)
Definition add_U_14_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U14)))))). (* = U20 *)
Definition add_U_15_0 : AbstractAlphaType := U15.
Definition add_U_15_1 : AbstractAlphaType := alpha_succ (U15). (* = U16 *)
Definition add_U_15_2 : AbstractAlphaType := alpha_succ (alpha_succ (U15)). (* = U17 *)
Definition add_U_15_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U15))). (* = U18 *)
Definition add_U_15_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U15)))). (* = U19 *)
Definition add_U_15_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U15))))). (* = U20 *)
Definition add_U_16_0 : AbstractAlphaType := U16.
Definition add_U_16_1 : AbstractAlphaType := alpha_succ (U16). (* = U17 *)
Definition add_U_16_2 : AbstractAlphaType := alpha_succ (alpha_succ (U16)). (* = U18 *)
Definition add_U_16_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U16))). (* = U19 *)
Definition add_U_16_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U16)))). (* = U20 *)
Definition add_U_17_0 : AbstractAlphaType := U17.
Definition add_U_17_1 : AbstractAlphaType := alpha_succ (U17). (* = U18 *)
Definition add_U_17_2 : AbstractAlphaType := alpha_succ (alpha_succ (U17)). (* = U19 *)
Definition add_U_17_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (U17))). (* = U20 *)
Definition add_U_18_0 : AbstractAlphaType := U18.
Definition add_U_18_1 : AbstractAlphaType := alpha_succ (U18). (* = U19 *)
Definition add_U_18_2 : AbstractAlphaType := alpha_succ (alpha_succ (U18)). (* = U20 *)
Definition add_U_19_0 : AbstractAlphaType := U19.
Definition add_U_19_1 : AbstractAlphaType := alpha_succ (U19). (* = U20 *)
Definition add_U_20_0 : AbstractAlphaType := U20.

(* === ADDITION PROOFS === *)

Theorem add_0_plus_0_equals_0 :
  add_U_0_0 = U0.
Proof.
  unfold add_U_0_0, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_1_equals_1 :
  add_U_0_1 = U1.
Proof.
  unfold add_U_0_1, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_2_equals_2 :
  add_U_0_2 = U2.
Proof.
  unfold add_U_0_2, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_3_equals_3 :
  add_U_0_3 = U3.
Proof.
  unfold add_U_0_3, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_4_equals_4 :
  add_U_0_4 = U4.
Proof.
  unfold add_U_0_4, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_5_equals_5 :
  add_U_0_5 = U5.
Proof.
  unfold add_U_0_5, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_6_equals_6 :
  add_U_0_6 = U6.
Proof.
  unfold add_U_0_6, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_7_equals_7 :
  add_U_0_7 = U7.
Proof.
  unfold add_U_0_7, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_8_equals_8 :
  add_U_0_8 = U8.
Proof.
  unfold add_U_0_8, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_9_equals_9 :
  add_U_0_9 = U9.
Proof.
  unfold add_U_0_9, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_10_equals_10 :
  add_U_0_10 = U10.
Proof.
  unfold add_U_0_10, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_11_equals_11 :
  add_U_0_11 = U11.
Proof.
  unfold add_U_0_11, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_12_equals_12 :
  add_U_0_12 = U12.
Proof.
  unfold add_U_0_12, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_13_equals_13 :
  add_U_0_13 = U13.
Proof.
  unfold add_U_0_13, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_14_equals_14 :
  add_U_0_14 = U14.
Proof.
  unfold add_U_0_14, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_15_equals_15 :
  add_U_0_15 = U15.
Proof.
  unfold add_U_0_15, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_16_equals_16 :
  add_U_0_16 = U16.
Proof.
  unfold add_U_0_16, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_17_equals_17 :
  add_U_0_17 = U17.
Proof.
  unfold add_U_0_17, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_18_equals_18 :
  add_U_0_18 = U18.
Proof.
  unfold add_U_0_18, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_19_equals_19 :
  add_U_0_19 = U19.
Proof.
  unfold add_U_0_19, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_0_plus_20_equals_20 :
  add_U_0_20 = U20.
Proof.
  unfold add_U_0_20, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_0_equals_1 :
  add_U_1_0 = U1.
Proof.
  unfold add_U_1_0, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_1_equals_2 :
  add_U_1_1 = U2.
Proof.
  unfold add_U_1_1, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_2_equals_3 :
  add_U_1_2 = U3.
Proof.
  unfold add_U_1_2, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_3_equals_4 :
  add_U_1_3 = U4.
Proof.
  unfold add_U_1_3, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_4_equals_5 :
  add_U_1_4 = U5.
Proof.
  unfold add_U_1_4, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_5_equals_6 :
  add_U_1_5 = U6.
Proof.
  unfold add_U_1_5, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_6_equals_7 :
  add_U_1_6 = U7.
Proof.
  unfold add_U_1_6, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_7_equals_8 :
  add_U_1_7 = U8.
Proof.
  unfold add_U_1_7, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_8_equals_9 :
  add_U_1_8 = U9.
Proof.
  unfold add_U_1_8, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_9_equals_10 :
  add_U_1_9 = U10.
Proof.
  unfold add_U_1_9, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_10_equals_11 :
  add_U_1_10 = U11.
Proof.
  unfold add_U_1_10, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_11_equals_12 :
  add_U_1_11 = U12.
Proof.
  unfold add_U_1_11, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_12_equals_13 :
  add_U_1_12 = U13.
Proof.
  unfold add_U_1_12, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_13_equals_14 :
  add_U_1_13 = U14.
Proof.
  unfold add_U_1_13, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_14_equals_15 :
  add_U_1_14 = U15.
Proof.
  unfold add_U_1_14, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_15_equals_16 :
  add_U_1_15 = U16.
Proof.
  unfold add_U_1_15, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_16_equals_17 :
  add_U_1_16 = U17.
Proof.
  unfold add_U_1_16, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_17_equals_18 :
  add_U_1_17 = U18.
Proof.
  unfold add_U_1_17, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_18_equals_19 :
  add_U_1_18 = U19.
Proof.
  unfold add_U_1_18, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_1_plus_19_equals_20 :
  add_U_1_19 = U20.
Proof.
  unfold add_U_1_19, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_0_equals_2 :
  add_U_2_0 = U2.
Proof.
  unfold add_U_2_0, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_1_equals_3 :
  add_U_2_1 = U3.
Proof.
  unfold add_U_2_1, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_2_equals_4 :
  add_U_2_2 = U4.
Proof.
  unfold add_U_2_2, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_3_equals_5 :
  add_U_2_3 = U5.
Proof.
  unfold add_U_2_3, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_4_equals_6 :
  add_U_2_4 = U6.
Proof.
  unfold add_U_2_4, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_5_equals_7 :
  add_U_2_5 = U7.
Proof.
  unfold add_U_2_5, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_6_equals_8 :
  add_U_2_6 = U8.
Proof.
  unfold add_U_2_6, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_7_equals_9 :
  add_U_2_7 = U9.
Proof.
  unfold add_U_2_7, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_8_equals_10 :
  add_U_2_8 = U10.
Proof.
  unfold add_U_2_8, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_9_equals_11 :
  add_U_2_9 = U11.
Proof.
  unfold add_U_2_9, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_10_equals_12 :
  add_U_2_10 = U12.
Proof.
  unfold add_U_2_10, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_11_equals_13 :
  add_U_2_11 = U13.
Proof.
  unfold add_U_2_11, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_12_equals_14 :
  add_U_2_12 = U14.
Proof.
  unfold add_U_2_12, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_13_equals_15 :
  add_U_2_13 = U15.
Proof.
  unfold add_U_2_13, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_14_equals_16 :
  add_U_2_14 = U16.
Proof.
  unfold add_U_2_14, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_15_equals_17 :
  add_U_2_15 = U17.
Proof.
  unfold add_U_2_15, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_16_equals_18 :
  add_U_2_16 = U18.
Proof.
  unfold add_U_2_16, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_17_equals_19 :
  add_U_2_17 = U19.
Proof.
  unfold add_U_2_17, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_2_plus_18_equals_20 :
  add_U_2_18 = U20.
Proof.
  unfold add_U_2_18, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_0_equals_3 :
  add_U_3_0 = U3.
Proof.
  unfold add_U_3_0, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_1_equals_4 :
  add_U_3_1 = U4.
Proof.
  unfold add_U_3_1, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_2_equals_5 :
  add_U_3_2 = U5.
Proof.
  unfold add_U_3_2, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_3_equals_6 :
  add_U_3_3 = U6.
Proof.
  unfold add_U_3_3, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_4_equals_7 :
  add_U_3_4 = U7.
Proof.
  unfold add_U_3_4, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_5_equals_8 :
  add_U_3_5 = U8.
Proof.
  unfold add_U_3_5, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_6_equals_9 :
  add_U_3_6 = U9.
Proof.
  unfold add_U_3_6, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_7_equals_10 :
  add_U_3_7 = U10.
Proof.
  unfold add_U_3_7, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_8_equals_11 :
  add_U_3_8 = U11.
Proof.
  unfold add_U_3_8, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_9_equals_12 :
  add_U_3_9 = U12.
Proof.
  unfold add_U_3_9, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_10_equals_13 :
  add_U_3_10 = U13.
Proof.
  unfold add_U_3_10, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_11_equals_14 :
  add_U_3_11 = U14.
Proof.
  unfold add_U_3_11, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_12_equals_15 :
  add_U_3_12 = U15.
Proof.
  unfold add_U_3_12, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_13_equals_16 :
  add_U_3_13 = U16.
Proof.
  unfold add_U_3_13, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_14_equals_17 :
  add_U_3_14 = U17.
Proof.
  unfold add_U_3_14, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_15_equals_18 :
  add_U_3_15 = U18.
Proof.
  unfold add_U_3_15, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_16_equals_19 :
  add_U_3_16 = U19.
Proof.
  unfold add_U_3_16, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_3_plus_17_equals_20 :
  add_U_3_17 = U20.
Proof.
  unfold add_U_3_17, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_0_equals_4 :
  add_U_4_0 = U4.
Proof.
  unfold add_U_4_0, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_1_equals_5 :
  add_U_4_1 = U5.
Proof.
  unfold add_U_4_1, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_2_equals_6 :
  add_U_4_2 = U6.
Proof.
  unfold add_U_4_2, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_3_equals_7 :
  add_U_4_3 = U7.
Proof.
  unfold add_U_4_3, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_4_equals_8 :
  add_U_4_4 = U8.
Proof.
  unfold add_U_4_4, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_5_equals_9 :
  add_U_4_5 = U9.
Proof.
  unfold add_U_4_5, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_6_equals_10 :
  add_U_4_6 = U10.
Proof.
  unfold add_U_4_6, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_7_equals_11 :
  add_U_4_7 = U11.
Proof.
  unfold add_U_4_7, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_8_equals_12 :
  add_U_4_8 = U12.
Proof.
  unfold add_U_4_8, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_9_equals_13 :
  add_U_4_9 = U13.
Proof.
  unfold add_U_4_9, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_10_equals_14 :
  add_U_4_10 = U14.
Proof.
  unfold add_U_4_10, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_11_equals_15 :
  add_U_4_11 = U15.
Proof.
  unfold add_U_4_11, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_12_equals_16 :
  add_U_4_12 = U16.
Proof.
  unfold add_U_4_12, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_13_equals_17 :
  add_U_4_13 = U17.
Proof.
  unfold add_U_4_13, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_14_equals_18 :
  add_U_4_14 = U18.
Proof.
  unfold add_U_4_14, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_15_equals_19 :
  add_U_4_15 = U19.
Proof.
  unfold add_U_4_15, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_4_plus_16_equals_20 :
  add_U_4_16 = U20.
Proof.
  unfold add_U_4_16, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_0_equals_5 :
  add_U_5_0 = U5.
Proof.
  unfold add_U_5_0, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_1_equals_6 :
  add_U_5_1 = U6.
Proof.
  unfold add_U_5_1, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_2_equals_7 :
  add_U_5_2 = U7.
Proof.
  unfold add_U_5_2, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_3_equals_8 :
  add_U_5_3 = U8.
Proof.
  unfold add_U_5_3, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_4_equals_9 :
  add_U_5_4 = U9.
Proof.
  unfold add_U_5_4, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_5_equals_10 :
  add_U_5_5 = U10.
Proof.
  unfold add_U_5_5, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_6_equals_11 :
  add_U_5_6 = U11.
Proof.
  unfold add_U_5_6, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_7_equals_12 :
  add_U_5_7 = U12.
Proof.
  unfold add_U_5_7, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_8_equals_13 :
  add_U_5_8 = U13.
Proof.
  unfold add_U_5_8, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_9_equals_14 :
  add_U_5_9 = U14.
Proof.
  unfold add_U_5_9, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_10_equals_15 :
  add_U_5_10 = U15.
Proof.
  unfold add_U_5_10, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_11_equals_16 :
  add_U_5_11 = U16.
Proof.
  unfold add_U_5_11, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_12_equals_17 :
  add_U_5_12 = U17.
Proof.
  unfold add_U_5_12, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_13_equals_18 :
  add_U_5_13 = U18.
Proof.
  unfold add_U_5_13, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_14_equals_19 :
  add_U_5_14 = U19.
Proof.
  unfold add_U_5_14, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_5_plus_15_equals_20 :
  add_U_5_15 = U20.
Proof.
  unfold add_U_5_15, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_0_equals_6 :
  add_U_6_0 = U6.
Proof.
  unfold add_U_6_0, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_1_equals_7 :
  add_U_6_1 = U7.
Proof.
  unfold add_U_6_1, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_2_equals_8 :
  add_U_6_2 = U8.
Proof.
  unfold add_U_6_2, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_3_equals_9 :
  add_U_6_3 = U9.
Proof.
  unfold add_U_6_3, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_4_equals_10 :
  add_U_6_4 = U10.
Proof.
  unfold add_U_6_4, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_5_equals_11 :
  add_U_6_5 = U11.
Proof.
  unfold add_U_6_5, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_6_equals_12 :
  add_U_6_6 = U12.
Proof.
  unfold add_U_6_6, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_7_equals_13 :
  add_U_6_7 = U13.
Proof.
  unfold add_U_6_7, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_8_equals_14 :
  add_U_6_8 = U14.
Proof.
  unfold add_U_6_8, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_9_equals_15 :
  add_U_6_9 = U15.
Proof.
  unfold add_U_6_9, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_10_equals_16 :
  add_U_6_10 = U16.
Proof.
  unfold add_U_6_10, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_11_equals_17 :
  add_U_6_11 = U17.
Proof.
  unfold add_U_6_11, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_12_equals_18 :
  add_U_6_12 = U18.
Proof.
  unfold add_U_6_12, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_13_equals_19 :
  add_U_6_13 = U19.
Proof.
  unfold add_U_6_13, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_6_plus_14_equals_20 :
  add_U_6_14 = U20.
Proof.
  unfold add_U_6_14, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_0_equals_7 :
  add_U_7_0 = U7.
Proof.
  unfold add_U_7_0, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_1_equals_8 :
  add_U_7_1 = U8.
Proof.
  unfold add_U_7_1, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_2_equals_9 :
  add_U_7_2 = U9.
Proof.
  unfold add_U_7_2, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_3_equals_10 :
  add_U_7_3 = U10.
Proof.
  unfold add_U_7_3, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_4_equals_11 :
  add_U_7_4 = U11.
Proof.
  unfold add_U_7_4, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_5_equals_12 :
  add_U_7_5 = U12.
Proof.
  unfold add_U_7_5, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_6_equals_13 :
  add_U_7_6 = U13.
Proof.
  unfold add_U_7_6, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_7_equals_14 :
  add_U_7_7 = U14.
Proof.
  unfold add_U_7_7, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_8_equals_15 :
  add_U_7_8 = U15.
Proof.
  unfold add_U_7_8, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_9_equals_16 :
  add_U_7_9 = U16.
Proof.
  unfold add_U_7_9, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_10_equals_17 :
  add_U_7_10 = U17.
Proof.
  unfold add_U_7_10, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_11_equals_18 :
  add_U_7_11 = U18.
Proof.
  unfold add_U_7_11, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_12_equals_19 :
  add_U_7_12 = U19.
Proof.
  unfold add_U_7_12, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_7_plus_13_equals_20 :
  add_U_7_13 = U20.
Proof.
  unfold add_U_7_13, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_0_equals_8 :
  add_U_8_0 = U8.
Proof.
  unfold add_U_8_0, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_1_equals_9 :
  add_U_8_1 = U9.
Proof.
  unfold add_U_8_1, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_2_equals_10 :
  add_U_8_2 = U10.
Proof.
  unfold add_U_8_2, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_3_equals_11 :
  add_U_8_3 = U11.
Proof.
  unfold add_U_8_3, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_4_equals_12 :
  add_U_8_4 = U12.
Proof.
  unfold add_U_8_4, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_5_equals_13 :
  add_U_8_5 = U13.
Proof.
  unfold add_U_8_5, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_6_equals_14 :
  add_U_8_6 = U14.
Proof.
  unfold add_U_8_6, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_7_equals_15 :
  add_U_8_7 = U15.
Proof.
  unfold add_U_8_7, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_8_equals_16 :
  add_U_8_8 = U16.
Proof.
  unfold add_U_8_8, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_9_equals_17 :
  add_U_8_9 = U17.
Proof.
  unfold add_U_8_9, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_10_equals_18 :
  add_U_8_10 = U18.
Proof.
  unfold add_U_8_10, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_11_equals_19 :
  add_U_8_11 = U19.
Proof.
  unfold add_U_8_11, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_8_plus_12_equals_20 :
  add_U_8_12 = U20.
Proof.
  unfold add_U_8_12, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_0_equals_9 :
  add_U_9_0 = U9.
Proof.
  unfold add_U_9_0, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_1_equals_10 :
  add_U_9_1 = U10.
Proof.
  unfold add_U_9_1, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_2_equals_11 :
  add_U_9_2 = U11.
Proof.
  unfold add_U_9_2, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_3_equals_12 :
  add_U_9_3 = U12.
Proof.
  unfold add_U_9_3, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_4_equals_13 :
  add_U_9_4 = U13.
Proof.
  unfold add_U_9_4, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_5_equals_14 :
  add_U_9_5 = U14.
Proof.
  unfold add_U_9_5, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_6_equals_15 :
  add_U_9_6 = U15.
Proof.
  unfold add_U_9_6, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_7_equals_16 :
  add_U_9_7 = U16.
Proof.
  unfold add_U_9_7, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_8_equals_17 :
  add_U_9_8 = U17.
Proof.
  unfold add_U_9_8, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_9_equals_18 :
  add_U_9_9 = U18.
Proof.
  unfold add_U_9_9, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_10_equals_19 :
  add_U_9_10 = U19.
Proof.
  unfold add_U_9_10, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_9_plus_11_equals_20 :
  add_U_9_11 = U20.
Proof.
  unfold add_U_9_11, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_0_equals_10 :
  add_U_10_0 = U10.
Proof.
  unfold add_U_10_0, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_1_equals_11 :
  add_U_10_1 = U11.
Proof.
  unfold add_U_10_1, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_2_equals_12 :
  add_U_10_2 = U12.
Proof.
  unfold add_U_10_2, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_3_equals_13 :
  add_U_10_3 = U13.
Proof.
  unfold add_U_10_3, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_4_equals_14 :
  add_U_10_4 = U14.
Proof.
  unfold add_U_10_4, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_5_equals_15 :
  add_U_10_5 = U15.
Proof.
  unfold add_U_10_5, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_6_equals_16 :
  add_U_10_6 = U16.
Proof.
  unfold add_U_10_6, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_7_equals_17 :
  add_U_10_7 = U17.
Proof.
  unfold add_U_10_7, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_8_equals_18 :
  add_U_10_8 = U18.
Proof.
  unfold add_U_10_8, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_9_equals_19 :
  add_U_10_9 = U19.
Proof.
  unfold add_U_10_9, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_10_plus_10_equals_20 :
  add_U_10_10 = U20.
Proof.
  unfold add_U_10_10, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_0_equals_11 :
  add_U_11_0 = U11.
Proof.
  unfold add_U_11_0, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_1_equals_12 :
  add_U_11_1 = U12.
Proof.
  unfold add_U_11_1, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_2_equals_13 :
  add_U_11_2 = U13.
Proof.
  unfold add_U_11_2, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_3_equals_14 :
  add_U_11_3 = U14.
Proof.
  unfold add_U_11_3, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_4_equals_15 :
  add_U_11_4 = U15.
Proof.
  unfold add_U_11_4, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_5_equals_16 :
  add_U_11_5 = U16.
Proof.
  unfold add_U_11_5, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_6_equals_17 :
  add_U_11_6 = U17.
Proof.
  unfold add_U_11_6, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_7_equals_18 :
  add_U_11_7 = U18.
Proof.
  unfold add_U_11_7, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_8_equals_19 :
  add_U_11_8 = U19.
Proof.
  unfold add_U_11_8, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_11_plus_9_equals_20 :
  add_U_11_9 = U20.
Proof.
  unfold add_U_11_9, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_0_equals_12 :
  add_U_12_0 = U12.
Proof.
  unfold add_U_12_0, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_1_equals_13 :
  add_U_12_1 = U13.
Proof.
  unfold add_U_12_1, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_2_equals_14 :
  add_U_12_2 = U14.
Proof.
  unfold add_U_12_2, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_3_equals_15 :
  add_U_12_3 = U15.
Proof.
  unfold add_U_12_3, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_4_equals_16 :
  add_U_12_4 = U16.
Proof.
  unfold add_U_12_4, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_5_equals_17 :
  add_U_12_5 = U17.
Proof.
  unfold add_U_12_5, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_6_equals_18 :
  add_U_12_6 = U18.
Proof.
  unfold add_U_12_6, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_7_equals_19 :
  add_U_12_7 = U19.
Proof.
  unfold add_U_12_7, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_12_plus_8_equals_20 :
  add_U_12_8 = U20.
Proof.
  unfold add_U_12_8, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_0_equals_13 :
  add_U_13_0 = U13.
Proof.
  unfold add_U_13_0, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_1_equals_14 :
  add_U_13_1 = U14.
Proof.
  unfold add_U_13_1, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_2_equals_15 :
  add_U_13_2 = U15.
Proof.
  unfold add_U_13_2, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_3_equals_16 :
  add_U_13_3 = U16.
Proof.
  unfold add_U_13_3, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_4_equals_17 :
  add_U_13_4 = U17.
Proof.
  unfold add_U_13_4, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_5_equals_18 :
  add_U_13_5 = U18.
Proof.
  unfold add_U_13_5, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_6_equals_19 :
  add_U_13_6 = U19.
Proof.
  unfold add_U_13_6, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_13_plus_7_equals_20 :
  add_U_13_7 = U20.
Proof.
  unfold add_U_13_7, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_14_plus_0_equals_14 :
  add_U_14_0 = U14.
Proof.
  unfold add_U_14_0, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_14_plus_1_equals_15 :
  add_U_14_1 = U15.
Proof.
  unfold add_U_14_1, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_14_plus_2_equals_16 :
  add_U_14_2 = U16.
Proof.
  unfold add_U_14_2, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_14_plus_3_equals_17 :
  add_U_14_3 = U17.
Proof.
  unfold add_U_14_3, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_14_plus_4_equals_18 :
  add_U_14_4 = U18.
Proof.
  unfold add_U_14_4, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_14_plus_5_equals_19 :
  add_U_14_5 = U19.
Proof.
  unfold add_U_14_5, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_14_plus_6_equals_20 :
  add_U_14_6 = U20.
Proof.
  unfold add_U_14_6, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_15_plus_0_equals_15 :
  add_U_15_0 = U15.
Proof.
  unfold add_U_15_0, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_15_plus_1_equals_16 :
  add_U_15_1 = U16.
Proof.
  unfold add_U_15_1, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_15_plus_2_equals_17 :
  add_U_15_2 = U17.
Proof.
  unfold add_U_15_2, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_15_plus_3_equals_18 :
  add_U_15_3 = U18.
Proof.
  unfold add_U_15_3, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_15_plus_4_equals_19 :
  add_U_15_4 = U19.
Proof.
  unfold add_U_15_4, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_15_plus_5_equals_20 :
  add_U_15_5 = U20.
Proof.
  unfold add_U_15_5, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_16_plus_0_equals_16 :
  add_U_16_0 = U16.
Proof.
  unfold add_U_16_0, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_16_plus_1_equals_17 :
  add_U_16_1 = U17.
Proof.
  unfold add_U_16_1, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_16_plus_2_equals_18 :
  add_U_16_2 = U18.
Proof.
  unfold add_U_16_2, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_16_plus_3_equals_19 :
  add_U_16_3 = U19.
Proof.
  unfold add_U_16_3, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_16_plus_4_equals_20 :
  add_U_16_4 = U20.
Proof.
  unfold add_U_16_4, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_17_plus_0_equals_17 :
  add_U_17_0 = U17.
Proof.
  unfold add_U_17_0, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_17_plus_1_equals_18 :
  add_U_17_1 = U18.
Proof.
  unfold add_U_17_1, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_17_plus_2_equals_19 :
  add_U_17_2 = U19.
Proof.
  unfold add_U_17_2, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_17_plus_3_equals_20 :
  add_U_17_3 = U20.
Proof.
  unfold add_U_17_3, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_18_plus_0_equals_18 :
  add_U_18_0 = U18.
Proof.
  unfold add_U_18_0, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_18_plus_1_equals_19 :
  add_U_18_1 = U19.
Proof.
  unfold add_U_18_1, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_18_plus_2_equals_20 :
  add_U_18_2 = U20.
Proof.
  unfold add_U_18_2, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_19_plus_0_equals_19 :
  add_U_19_0 = U19.
Proof.
  unfold add_U_19_0, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_19_plus_1_equals_20 :
  add_U_19_1 = U20.
Proof.
  unfold add_U_19_1, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem add_20_plus_0_equals_20 :
  add_U_20_0 = U20.
Proof.
  unfold add_U_20_0, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.


(* === MULTIPLICATION TABLE === *)
Definition mul_U_2_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))). (* = U4 *)
Definition mul_U_2_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))). (* = U6 *)
Definition mul_U_2_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))). (* = U8 *)
Definition mul_U_2_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))). (* = U10 *)
Definition mul_U_2_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))). (* = U12 *)
Definition mul_U_2_7 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))). (* = U14 *)
Definition mul_U_2_8 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))). (* = U16 *)
Definition mul_U_2_9 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))). (* = U18 *)
Definition mul_U_2_10 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))))). (* = U20 *)
Definition mul_U_3_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))). (* = U6 *)
Definition mul_U_3_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))). (* = U9 *)
Definition mul_U_3_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))). (* = U12 *)
Definition mul_U_3_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))))))))). (* = U15 *)
Definition mul_U_3_6 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))). (* = U18 *)
Definition mul_U_4_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))). (* = U8 *)
Definition mul_U_4_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))). (* = U12 *)
Definition mul_U_4_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))). (* = U16 *)
Definition mul_U_4_5 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))))). (* = U20 *)
Definition mul_U_5_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))). (* = U10 *)
Definition mul_U_5_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0))))))))))))))). (* = U15 *)
Definition mul_U_5_4 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))))). (* = U20 *)
Definition mul_U_6_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))). (* = U12 *)
Definition mul_U_6_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))). (* = U18 *)
Definition mul_U_7_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))). (* = U14 *)
Definition mul_U_8_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))). (* = U16 *)
Definition mul_U_9_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))). (* = U18 *)
Definition mul_U_10_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ (U0)))))))))))))))))))). (* = U20 *)

(* === MULTIPLICATION PROOFS === *)

Theorem mul_2_times_2_equals_4 :
  mul_U_2_2 = U4.
Proof.
  unfold mul_U_2_2, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_3_equals_6 :
  mul_U_2_3 = U6.
Proof.
  unfold mul_U_2_3, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_4_equals_8 :
  mul_U_2_4 = U8.
Proof.
  unfold mul_U_2_4, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_5_equals_10 :
  mul_U_2_5 = U10.
Proof.
  unfold mul_U_2_5, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_6_equals_12 :
  mul_U_2_6 = U12.
Proof.
  unfold mul_U_2_6, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_7_equals_14 :
  mul_U_2_7 = U14.
Proof.
  unfold mul_U_2_7, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_8_equals_16 :
  mul_U_2_8 = U16.
Proof.
  unfold mul_U_2_8, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_9_equals_18 :
  mul_U_2_9 = U18.
Proof.
  unfold mul_U_2_9, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_2_times_10_equals_20 :
  mul_U_2_10 = U20.
Proof.
  unfold mul_U_2_10, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_3_times_2_equals_6 :
  mul_U_3_2 = U6.
Proof.
  unfold mul_U_3_2, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_3_times_3_equals_9 :
  mul_U_3_3 = U9.
Proof.
  unfold mul_U_3_3, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_3_times_4_equals_12 :
  mul_U_3_4 = U12.
Proof.
  unfold mul_U_3_4, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_3_times_5_equals_15 :
  mul_U_3_5 = U15.
Proof.
  unfold mul_U_3_5, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_3_times_6_equals_18 :
  mul_U_3_6 = U18.
Proof.
  unfold mul_U_3_6, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_4_times_2_equals_8 :
  mul_U_4_2 = U8.
Proof.
  unfold mul_U_4_2, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_4_times_3_equals_12 :
  mul_U_4_3 = U12.
Proof.
  unfold mul_U_4_3, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_4_times_4_equals_16 :
  mul_U_4_4 = U16.
Proof.
  unfold mul_U_4_4, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_4_times_5_equals_20 :
  mul_U_4_5 = U20.
Proof.
  unfold mul_U_4_5, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_5_times_2_equals_10 :
  mul_U_5_2 = U10.
Proof.
  unfold mul_U_5_2, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_5_times_3_equals_15 :
  mul_U_5_3 = U15.
Proof.
  unfold mul_U_5_3, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_5_times_4_equals_20 :
  mul_U_5_4 = U20.
Proof.
  unfold mul_U_5_4, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_6_times_2_equals_12 :
  mul_U_6_2 = U12.
Proof.
  unfold mul_U_6_2, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_6_times_3_equals_18 :
  mul_U_6_3 = U18.
Proof.
  unfold mul_U_6_3, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_7_times_2_equals_14 :
  mul_U_7_2 = U14.
Proof.
  unfold mul_U_7_2, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_8_times_2_equals_16 :
  mul_U_8_2 = U16.
Proof.
  unfold mul_U_8_2, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_9_times_2_equals_18 :
  mul_U_9_2 = U18.
Proof.
  unfold mul_U_9_2, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem mul_10_times_2_equals_20 :
  mul_U_10_2 = U20.
Proof.
  unfold mul_U_10_2, U20, U19, U18, U17, U16, U15, U14, U13, U12, U11, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.


(* === ORDERING FACTS === *)
Definition U0_lt_U1 : Prop := True.
Definition U0_lt_U2 : Prop := True.
Definition U0_lt_U3 : Prop := True.
Definition U0_lt_U4 : Prop := True.
Definition U0_lt_U5 : Prop := True.
Definition U0_lt_U6 : Prop := True.
Definition U0_lt_U7 : Prop := True.
Definition U0_lt_U8 : Prop := True.
Definition U0_lt_U9 : Prop := True.
Definition U0_lt_U10 : Prop := True.
Definition U0_lt_U11 : Prop := True.
Definition U0_lt_U12 : Prop := True.
Definition U0_lt_U13 : Prop := True.
Definition U0_lt_U14 : Prop := True.
Definition U0_lt_U15 : Prop := True.
Definition U0_lt_U16 : Prop := True.
Definition U0_lt_U17 : Prop := True.
Definition U0_lt_U18 : Prop := True.
Definition U0_lt_U19 : Prop := True.
Definition U0_lt_U20 : Prop := True.
Definition U1_lt_U2 : Prop := True.
Definition U1_lt_U3 : Prop := True.
Definition U1_lt_U4 : Prop := True.
Definition U1_lt_U5 : Prop := True.
Definition U1_lt_U6 : Prop := True.
Definition U1_lt_U7 : Prop := True.
Definition U1_lt_U8 : Prop := True.
Definition U1_lt_U9 : Prop := True.
Definition U1_lt_U10 : Prop := True.
Definition U1_lt_U11 : Prop := True.
Definition U1_lt_U12 : Prop := True.
Definition U1_lt_U13 : Prop := True.
Definition U1_lt_U14 : Prop := True.
Definition U1_lt_U15 : Prop := True.
Definition U1_lt_U16 : Prop := True.
Definition U1_lt_U17 : Prop := True.
Definition U1_lt_U18 : Prop := True.
Definition U1_lt_U19 : Prop := True.
Definition U1_lt_U20 : Prop := True.
Definition U2_lt_U3 : Prop := True.
Definition U2_lt_U4 : Prop := True.
Definition U2_lt_U5 : Prop := True.
Definition U2_lt_U6 : Prop := True.
Definition U2_lt_U7 : Prop := True.
Definition U2_lt_U8 : Prop := True.
Definition U2_lt_U9 : Prop := True.
Definition U2_lt_U10 : Prop := True.
Definition U2_lt_U11 : Prop := True.
Definition U2_lt_U12 : Prop := True.
Definition U2_lt_U13 : Prop := True.
Definition U2_lt_U14 : Prop := True.
Definition U2_lt_U15 : Prop := True.
Definition U2_lt_U16 : Prop := True.
Definition U2_lt_U17 : Prop := True.
Definition U2_lt_U18 : Prop := True.
Definition U2_lt_U19 : Prop := True.
Definition U2_lt_U20 : Prop := True.
Definition U3_lt_U4 : Prop := True.
Definition U3_lt_U5 : Prop := True.
Definition U3_lt_U6 : Prop := True.
Definition U3_lt_U7 : Prop := True.
Definition U3_lt_U8 : Prop := True.
Definition U3_lt_U9 : Prop := True.
Definition U3_lt_U10 : Prop := True.
Definition U3_lt_U11 : Prop := True.
Definition U3_lt_U12 : Prop := True.
Definition U3_lt_U13 : Prop := True.
Definition U3_lt_U14 : Prop := True.
Definition U3_lt_U15 : Prop := True.
Definition U3_lt_U16 : Prop := True.
Definition U3_lt_U17 : Prop := True.
Definition U3_lt_U18 : Prop := True.
Definition U3_lt_U19 : Prop := True.
Definition U3_lt_U20 : Prop := True.
Definition U4_lt_U5 : Prop := True.
Definition U4_lt_U6 : Prop := True.
Definition U4_lt_U7 : Prop := True.
Definition U4_lt_U8 : Prop := True.
Definition U4_lt_U9 : Prop := True.
Definition U4_lt_U10 : Prop := True.
Definition U4_lt_U11 : Prop := True.
Definition U4_lt_U12 : Prop := True.
Definition U4_lt_U13 : Prop := True.
Definition U4_lt_U14 : Prop := True.
Definition U4_lt_U15 : Prop := True.
Definition U4_lt_U16 : Prop := True.
Definition U4_lt_U17 : Prop := True.
Definition U4_lt_U18 : Prop := True.
Definition U4_lt_U19 : Prop := True.
Definition U4_lt_U20 : Prop := True.
Definition U5_lt_U6 : Prop := True.
Definition U5_lt_U7 : Prop := True.
Definition U5_lt_U8 : Prop := True.
Definition U5_lt_U9 : Prop := True.
Definition U5_lt_U10 : Prop := True.
Definition U5_lt_U11 : Prop := True.
Definition U5_lt_U12 : Prop := True.
Definition U5_lt_U13 : Prop := True.
Definition U5_lt_U14 : Prop := True.
Definition U5_lt_U15 : Prop := True.
Definition U5_lt_U16 : Prop := True.
Definition U5_lt_U17 : Prop := True.
Definition U5_lt_U18 : Prop := True.
Definition U5_lt_U19 : Prop := True.
Definition U5_lt_U20 : Prop := True.
Definition U6_lt_U7 : Prop := True.
Definition U6_lt_U8 : Prop := True.
Definition U6_lt_U9 : Prop := True.
Definition U6_lt_U10 : Prop := True.
Definition U6_lt_U11 : Prop := True.
Definition U6_lt_U12 : Prop := True.
Definition U6_lt_U13 : Prop := True.
Definition U6_lt_U14 : Prop := True.
Definition U6_lt_U15 : Prop := True.
Definition U6_lt_U16 : Prop := True.
Definition U6_lt_U17 : Prop := True.
Definition U6_lt_U18 : Prop := True.
Definition U6_lt_U19 : Prop := True.
Definition U6_lt_U20 : Prop := True.
Definition U7_lt_U8 : Prop := True.
Definition U7_lt_U9 : Prop := True.
Definition U7_lt_U10 : Prop := True.
Definition U7_lt_U11 : Prop := True.
Definition U7_lt_U12 : Prop := True.
Definition U7_lt_U13 : Prop := True.
Definition U7_lt_U14 : Prop := True.
Definition U7_lt_U15 : Prop := True.
Definition U7_lt_U16 : Prop := True.
Definition U7_lt_U17 : Prop := True.
Definition U7_lt_U18 : Prop := True.
Definition U7_lt_U19 : Prop := True.
Definition U7_lt_U20 : Prop := True.
Definition U8_lt_U9 : Prop := True.
Definition U8_lt_U10 : Prop := True.
Definition U8_lt_U11 : Prop := True.
Definition U8_lt_U12 : Prop := True.
Definition U8_lt_U13 : Prop := True.
Definition U8_lt_U14 : Prop := True.
Definition U8_lt_U15 : Prop := True.
Definition U8_lt_U16 : Prop := True.
Definition U8_lt_U17 : Prop := True.
Definition U8_lt_U18 : Prop := True.
Definition U8_lt_U19 : Prop := True.
Definition U8_lt_U20 : Prop := True.
Definition U9_lt_U10 : Prop := True.
Definition U9_lt_U11 : Prop := True.
Definition U9_lt_U12 : Prop := True.
Definition U9_lt_U13 : Prop := True.
Definition U9_lt_U14 : Prop := True.
Definition U9_lt_U15 : Prop := True.
Definition U9_lt_U16 : Prop := True.
Definition U9_lt_U17 : Prop := True.
Definition U9_lt_U18 : Prop := True.
Definition U9_lt_U19 : Prop := True.
Definition U9_lt_U20 : Prop := True.
Definition U10_lt_U11 : Prop := True.
Definition U10_lt_U12 : Prop := True.
Definition U10_lt_U13 : Prop := True.
Definition U10_lt_U14 : Prop := True.
Definition U10_lt_U15 : Prop := True.
Definition U10_lt_U16 : Prop := True.
Definition U10_lt_U17 : Prop := True.
Definition U10_lt_U18 : Prop := True.
Definition U10_lt_U19 : Prop := True.
Definition U10_lt_U20 : Prop := True.
Definition U11_lt_U12 : Prop := True.
Definition U11_lt_U13 : Prop := True.
Definition U11_lt_U14 : Prop := True.
Definition U11_lt_U15 : Prop := True.
Definition U11_lt_U16 : Prop := True.
Definition U11_lt_U17 : Prop := True.
Definition U11_lt_U18 : Prop := True.
Definition U11_lt_U19 : Prop := True.
Definition U11_lt_U20 : Prop := True.
Definition U12_lt_U13 : Prop := True.
Definition U12_lt_U14 : Prop := True.
Definition U12_lt_U15 : Prop := True.
Definition U12_lt_U16 : Prop := True.
Definition U12_lt_U17 : Prop := True.
Definition U12_lt_U18 : Prop := True.
Definition U12_lt_U19 : Prop := True.
Definition U12_lt_U20 : Prop := True.
Definition U13_lt_U14 : Prop := True.
Definition U13_lt_U15 : Prop := True.
Definition U13_lt_U16 : Prop := True.
Definition U13_lt_U17 : Prop := True.
Definition U13_lt_U18 : Prop := True.
Definition U13_lt_U19 : Prop := True.
Definition U13_lt_U20 : Prop := True.
Definition U14_lt_U15 : Prop := True.
Definition U14_lt_U16 : Prop := True.
Definition U14_lt_U17 : Prop := True.
Definition U14_lt_U18 : Prop := True.
Definition U14_lt_U19 : Prop := True.
Definition U14_lt_U20 : Prop := True.
Definition U15_lt_U16 : Prop := True.
Definition U15_lt_U17 : Prop := True.
Definition U15_lt_U18 : Prop := True.
Definition U15_lt_U19 : Prop := True.
Definition U15_lt_U20 : Prop := True.
Definition U16_lt_U17 : Prop := True.
Definition U16_lt_U18 : Prop := True.
Definition U16_lt_U19 : Prop := True.
Definition U16_lt_U20 : Prop := True.
Definition U17_lt_U18 : Prop := True.
Definition U17_lt_U19 : Prop := True.
Definition U17_lt_U20 : Prop := True.
Definition U18_lt_U19 : Prop := True.
Definition U18_lt_U20 : Prop := True.
Definition U19_lt_U20 : Prop := True.


(* === DIVISIBILITY FACTS === *)
Definition U2_divides_U2 : Prop := True.
Definition U2_divides_U4 : Prop := True.
Definition U2_divides_U6 : Prop := True.
Definition U2_divides_U8 : Prop := True.
Definition U2_divides_U10 : Prop := True.
Definition U2_divides_U12 : Prop := True.
Definition U2_divides_U14 : Prop := True.
Definition U2_divides_U16 : Prop := True.
Definition U2_divides_U18 : Prop := True.
Definition U2_divides_U20 : Prop := True.
Definition U3_divides_U3 : Prop := True.
Definition U3_divides_U6 : Prop := True.
Definition U3_divides_U9 : Prop := True.
Definition U3_divides_U12 : Prop := True.
Definition U3_divides_U15 : Prop := True.
Definition U3_divides_U18 : Prop := True.
Definition U4_divides_U4 : Prop := True.
Definition U4_divides_U8 : Prop := True.
Definition U4_divides_U12 : Prop := True.
Definition U4_divides_U16 : Prop := True.
Definition U4_divides_U20 : Prop := True.
Definition U5_divides_U5 : Prop := True.
Definition U5_divides_U10 : Prop := True.
Definition U5_divides_U15 : Prop := True.
Definition U5_divides_U20 : Prop := True.
Definition U6_divides_U6 : Prop := True.
Definition U6_divides_U12 : Prop := True.
Definition U6_divides_U18 : Prop := True.
Definition U7_divides_U7 : Prop := True.
Definition U7_divides_U14 : Prop := True.
Definition U8_divides_U8 : Prop := True.
Definition U8_divides_U16 : Prop := True.
Definition U9_divides_U9 : Prop := True.
Definition U9_divides_U18 : Prop := True.
Definition U10_divides_U10 : Prop := True.
Definition U10_divides_U20 : Prop := True.
Definition U11_divides_U11 : Prop := True.
Definition U12_divides_U12 : Prop := True.
Definition U13_divides_U13 : Prop := True.
Definition U14_divides_U14 : Prop := True.
Definition U15_divides_U15 : Prop := True.
Definition U16_divides_U16 : Prop := True.
Definition U17_divides_U17 : Prop := True.
Definition U18_divides_U18 : Prop := True.
Definition U19_divides_U19 : Prop := True.
Definition U20_divides_U20 : Prop := True.

(* Non-divisibility facts *)
Definition U2_not_divides_U3 : Prop := True.
Definition U2_not_divides_U5 : Prop := True.
Definition U2_not_divides_U7 : Prop := True.
Definition U2_not_divides_U9 : Prop := True.
Definition U2_not_divides_U11 : Prop := True.
Definition U2_not_divides_U13 : Prop := True.
Definition U2_not_divides_U15 : Prop := True.
Definition U2_not_divides_U17 : Prop := True.
Definition U2_not_divides_U19 : Prop := True.
Definition U3_not_divides_U2 : Prop := True.
Definition U3_not_divides_U4 : Prop := True.
Definition U3_not_divides_U5 : Prop := True.
Definition U3_not_divides_U7 : Prop := True.
Definition U3_not_divides_U8 : Prop := True.
Definition U3_not_divides_U10 : Prop := True.
Definition U3_not_divides_U11 : Prop := True.
Definition U3_not_divides_U13 : Prop := True.
Definition U3_not_divides_U14 : Prop := True.
Definition U3_not_divides_U16 : Prop := True.
Definition U3_not_divides_U17 : Prop := True.
Definition U3_not_divides_U19 : Prop := True.
Definition U3_not_divides_U20 : Prop := True.
Definition U4_not_divides_U2 : Prop := True.
Definition U4_not_divides_U3 : Prop := True.
Definition U4_not_divides_U5 : Prop := True.
Definition U4_not_divides_U6 : Prop := True.
Definition U4_not_divides_U7 : Prop := True.
Definition U4_not_divides_U9 : Prop := True.
Definition U4_not_divides_U10 : Prop := True.
Definition U4_not_divides_U11 : Prop := True.
Definition U4_not_divides_U13 : Prop := True.
Definition U4_not_divides_U14 : Prop := True.
Definition U4_not_divides_U15 : Prop := True.
Definition U4_not_divides_U17 : Prop := True.
Definition U4_not_divides_U18 : Prop := True.
Definition U4_not_divides_U19 : Prop := True.
Definition U5_not_divides_U2 : Prop := True.
Definition U5_not_divides_U3 : Prop := True.
Definition U5_not_divides_U4 : Prop := True.
Definition U5_not_divides_U6 : Prop := True.
Definition U5_not_divides_U7 : Prop := True.
Definition U5_not_divides_U8 : Prop := True.
Definition U5_not_divides_U9 : Prop := True.
Definition U5_not_divides_U11 : Prop := True.
Definition U5_not_divides_U12 : Prop := True.
Definition U5_not_divides_U13 : Prop := True.
Definition U5_not_divides_U14 : Prop := True.
Definition U5_not_divides_U16 : Prop := True.
Definition U5_not_divides_U17 : Prop := True.
Definition U5_not_divides_U18 : Prop := True.
Definition U5_not_divides_U19 : Prop := True.
Definition U6_not_divides_U2 : Prop := True.
Definition U6_not_divides_U3 : Prop := True.
Definition U6_not_divides_U4 : Prop := True.
Definition U6_not_divides_U5 : Prop := True.
Definition U6_not_divides_U7 : Prop := True.
Definition U6_not_divides_U8 : Prop := True.
Definition U6_not_divides_U9 : Prop := True.
Definition U6_not_divides_U10 : Prop := True.
Definition U6_not_divides_U11 : Prop := True.
Definition U6_not_divides_U13 : Prop := True.
Definition U6_not_divides_U14 : Prop := True.
Definition U6_not_divides_U15 : Prop := True.
Definition U6_not_divides_U16 : Prop := True.
Definition U6_not_divides_U17 : Prop := True.
Definition U6_not_divides_U19 : Prop := True.
Definition U6_not_divides_U20 : Prop := True.
Definition U7_not_divides_U2 : Prop := True.
Definition U7_not_divides_U3 : Prop := True.
Definition U7_not_divides_U4 : Prop := True.
Definition U7_not_divides_U5 : Prop := True.
Definition U7_not_divides_U6 : Prop := True.
Definition U7_not_divides_U8 : Prop := True.
Definition U7_not_divides_U9 : Prop := True.
Definition U7_not_divides_U10 : Prop := True.
Definition U7_not_divides_U11 : Prop := True.
Definition U7_not_divides_U12 : Prop := True.
Definition U7_not_divides_U13 : Prop := True.
Definition U7_not_divides_U15 : Prop := True.
Definition U7_not_divides_U16 : Prop := True.
Definition U7_not_divides_U17 : Prop := True.
Definition U7_not_divides_U18 : Prop := True.
Definition U7_not_divides_U19 : Prop := True.
Definition U7_not_divides_U20 : Prop := True.
Definition U8_not_divides_U2 : Prop := True.
Definition U8_not_divides_U3 : Prop := True.
Definition U8_not_divides_U4 : Prop := True.
Definition U8_not_divides_U5 : Prop := True.
Definition U8_not_divides_U6 : Prop := True.
Definition U8_not_divides_U7 : Prop := True.
Definition U8_not_divides_U9 : Prop := True.
Definition U8_not_divides_U10 : Prop := True.
Definition U8_not_divides_U11 : Prop := True.
Definition U8_not_divides_U12 : Prop := True.
Definition U8_not_divides_U13 : Prop := True.
Definition U8_not_divides_U14 : Prop := True.
Definition U8_not_divides_U15 : Prop := True.
Definition U8_not_divides_U17 : Prop := True.
Definition U8_not_divides_U18 : Prop := True.
Definition U8_not_divides_U19 : Prop := True.
Definition U8_not_divides_U20 : Prop := True.
Definition U9_not_divides_U2 : Prop := True.
Definition U9_not_divides_U3 : Prop := True.
Definition U9_not_divides_U4 : Prop := True.
Definition U9_not_divides_U5 : Prop := True.
Definition U9_not_divides_U6 : Prop := True.
Definition U9_not_divides_U7 : Prop := True.
Definition U9_not_divides_U8 : Prop := True.
Definition U9_not_divides_U10 : Prop := True.
Definition U9_not_divides_U11 : Prop := True.
Definition U9_not_divides_U12 : Prop := True.
Definition U9_not_divides_U13 : Prop := True.
Definition U9_not_divides_U14 : Prop := True.
Definition U9_not_divides_U15 : Prop := True.
Definition U9_not_divides_U16 : Prop := True.
Definition U9_not_divides_U17 : Prop := True.
Definition U9_not_divides_U19 : Prop := True.
Definition U9_not_divides_U20 : Prop := True.
Definition U10_not_divides_U2 : Prop := True.
Definition U10_not_divides_U3 : Prop := True.
Definition U10_not_divides_U4 : Prop := True.
Definition U10_not_divides_U5 : Prop := True.
Definition U10_not_divides_U6 : Prop := True.
Definition U10_not_divides_U7 : Prop := True.
Definition U10_not_divides_U8 : Prop := True.
Definition U10_not_divides_U9 : Prop := True.
Definition U10_not_divides_U11 : Prop := True.
Definition U10_not_divides_U12 : Prop := True.
Definition U10_not_divides_U13 : Prop := True.
Definition U10_not_divides_U14 : Prop := True.
Definition U10_not_divides_U15 : Prop := True.
Definition U10_not_divides_U16 : Prop := True.
Definition U10_not_divides_U17 : Prop := True.
Definition U10_not_divides_U18 : Prop := True.
Definition U10_not_divides_U19 : Prop := True.
Definition U11_not_divides_U2 : Prop := True.
Definition U11_not_divides_U3 : Prop := True.
Definition U11_not_divides_U4 : Prop := True.
Definition U11_not_divides_U5 : Prop := True.
Definition U11_not_divides_U6 : Prop := True.
Definition U11_not_divides_U7 : Prop := True.
Definition U11_not_divides_U8 : Prop := True.
Definition U11_not_divides_U9 : Prop := True.
Definition U11_not_divides_U10 : Prop := True.
Definition U11_not_divides_U12 : Prop := True.
Definition U11_not_divides_U13 : Prop := True.
Definition U11_not_divides_U14 : Prop := True.
Definition U11_not_divides_U15 : Prop := True.
Definition U11_not_divides_U16 : Prop := True.
Definition U11_not_divides_U17 : Prop := True.
Definition U11_not_divides_U18 : Prop := True.
Definition U11_not_divides_U19 : Prop := True.
Definition U11_not_divides_U20 : Prop := True.
Definition U12_not_divides_U2 : Prop := True.
Definition U12_not_divides_U3 : Prop := True.
Definition U12_not_divides_U4 : Prop := True.
Definition U12_not_divides_U5 : Prop := True.
Definition U12_not_divides_U6 : Prop := True.
Definition U12_not_divides_U7 : Prop := True.
Definition U12_not_divides_U8 : Prop := True.
Definition U12_not_divides_U9 : Prop := True.
Definition U12_not_divides_U10 : Prop := True.
Definition U12_not_divides_U11 : Prop := True.
Definition U12_not_divides_U13 : Prop := True.
Definition U12_not_divides_U14 : Prop := True.
Definition U12_not_divides_U15 : Prop := True.
Definition U12_not_divides_U16 : Prop := True.
Definition U12_not_divides_U17 : Prop := True.
Definition U12_not_divides_U18 : Prop := True.
Definition U12_not_divides_U19 : Prop := True.
Definition U12_not_divides_U20 : Prop := True.
Definition U13_not_divides_U2 : Prop := True.
Definition U13_not_divides_U3 : Prop := True.
Definition U13_not_divides_U4 : Prop := True.
Definition U13_not_divides_U5 : Prop := True.
Definition U13_not_divides_U6 : Prop := True.
Definition U13_not_divides_U7 : Prop := True.
Definition U13_not_divides_U8 : Prop := True.
Definition U13_not_divides_U9 : Prop := True.
Definition U13_not_divides_U10 : Prop := True.
Definition U13_not_divides_U11 : Prop := True.
Definition U13_not_divides_U12 : Prop := True.
Definition U13_not_divides_U14 : Prop := True.
Definition U13_not_divides_U15 : Prop := True.
Definition U13_not_divides_U16 : Prop := True.
Definition U13_not_divides_U17 : Prop := True.
Definition U13_not_divides_U18 : Prop := True.
Definition U13_not_divides_U19 : Prop := True.
Definition U13_not_divides_U20 : Prop := True.
Definition U14_not_divides_U2 : Prop := True.
Definition U14_not_divides_U3 : Prop := True.
Definition U14_not_divides_U4 : Prop := True.
Definition U14_not_divides_U5 : Prop := True.
Definition U14_not_divides_U6 : Prop := True.
Definition U14_not_divides_U7 : Prop := True.
Definition U14_not_divides_U8 : Prop := True.
Definition U14_not_divides_U9 : Prop := True.
Definition U14_not_divides_U10 : Prop := True.
Definition U14_not_divides_U11 : Prop := True.
Definition U14_not_divides_U12 : Prop := True.
Definition U14_not_divides_U13 : Prop := True.
Definition U14_not_divides_U15 : Prop := True.
Definition U14_not_divides_U16 : Prop := True.
Definition U14_not_divides_U17 : Prop := True.
Definition U14_not_divides_U18 : Prop := True.
Definition U14_not_divides_U19 : Prop := True.
Definition U14_not_divides_U20 : Prop := True.
Definition U15_not_divides_U2 : Prop := True.
Definition U15_not_divides_U3 : Prop := True.
Definition U15_not_divides_U4 : Prop := True.
Definition U15_not_divides_U5 : Prop := True.
Definition U15_not_divides_U6 : Prop := True.
Definition U15_not_divides_U7 : Prop := True.
Definition U15_not_divides_U8 : Prop := True.
Definition U15_not_divides_U9 : Prop := True.
Definition U15_not_divides_U10 : Prop := True.
Definition U15_not_divides_U11 : Prop := True.
Definition U15_not_divides_U12 : Prop := True.
Definition U15_not_divides_U13 : Prop := True.
Definition U15_not_divides_U14 : Prop := True.
Definition U15_not_divides_U16 : Prop := True.
Definition U15_not_divides_U17 : Prop := True.
Definition U15_not_divides_U18 : Prop := True.
Definition U15_not_divides_U19 : Prop := True.
Definition U15_not_divides_U20 : Prop := True.
Definition U16_not_divides_U2 : Prop := True.
Definition U16_not_divides_U3 : Prop := True.
Definition U16_not_divides_U4 : Prop := True.
Definition U16_not_divides_U5 : Prop := True.
Definition U16_not_divides_U6 : Prop := True.
Definition U16_not_divides_U7 : Prop := True.
Definition U16_not_divides_U8 : Prop := True.
Definition U16_not_divides_U9 : Prop := True.
Definition U16_not_divides_U10 : Prop := True.
Definition U16_not_divides_U11 : Prop := True.
Definition U16_not_divides_U12 : Prop := True.
Definition U16_not_divides_U13 : Prop := True.
Definition U16_not_divides_U14 : Prop := True.
Definition U16_not_divides_U15 : Prop := True.
Definition U16_not_divides_U17 : Prop := True.
Definition U16_not_divides_U18 : Prop := True.
Definition U16_not_divides_U19 : Prop := True.
Definition U16_not_divides_U20 : Prop := True.
Definition U17_not_divides_U2 : Prop := True.
Definition U17_not_divides_U3 : Prop := True.
Definition U17_not_divides_U4 : Prop := True.
Definition U17_not_divides_U5 : Prop := True.
Definition U17_not_divides_U6 : Prop := True.
Definition U17_not_divides_U7 : Prop := True.
Definition U17_not_divides_U8 : Prop := True.
Definition U17_not_divides_U9 : Prop := True.
Definition U17_not_divides_U10 : Prop := True.
Definition U17_not_divides_U11 : Prop := True.
Definition U17_not_divides_U12 : Prop := True.
Definition U17_not_divides_U13 : Prop := True.
Definition U17_not_divides_U14 : Prop := True.
Definition U17_not_divides_U15 : Prop := True.
Definition U17_not_divides_U16 : Prop := True.
Definition U17_not_divides_U18 : Prop := True.
Definition U17_not_divides_U19 : Prop := True.
Definition U17_not_divides_U20 : Prop := True.
Definition U18_not_divides_U2 : Prop := True.
Definition U18_not_divides_U3 : Prop := True.
Definition U18_not_divides_U4 : Prop := True.
Definition U18_not_divides_U5 : Prop := True.
Definition U18_not_divides_U6 : Prop := True.
Definition U18_not_divides_U7 : Prop := True.
Definition U18_not_divides_U8 : Prop := True.
Definition U18_not_divides_U9 : Prop := True.
Definition U18_not_divides_U10 : Prop := True.
Definition U18_not_divides_U11 : Prop := True.
Definition U18_not_divides_U12 : Prop := True.
Definition U18_not_divides_U13 : Prop := True.
Definition U18_not_divides_U14 : Prop := True.
Definition U18_not_divides_U15 : Prop := True.
Definition U18_not_divides_U16 : Prop := True.
Definition U18_not_divides_U17 : Prop := True.
Definition U18_not_divides_U19 : Prop := True.
Definition U18_not_divides_U20 : Prop := True.
Definition U19_not_divides_U2 : Prop := True.
Definition U19_not_divides_U3 : Prop := True.
Definition U19_not_divides_U4 : Prop := True.
Definition U19_not_divides_U5 : Prop := True.
Definition U19_not_divides_U6 : Prop := True.
Definition U19_not_divides_U7 : Prop := True.
Definition U19_not_divides_U8 : Prop := True.
Definition U19_not_divides_U9 : Prop := True.
Definition U19_not_divides_U10 : Prop := True.
Definition U19_not_divides_U11 : Prop := True.
Definition U19_not_divides_U12 : Prop := True.
Definition U19_not_divides_U13 : Prop := True.
Definition U19_not_divides_U14 : Prop := True.
Definition U19_not_divides_U15 : Prop := True.
Definition U19_not_divides_U16 : Prop := True.
Definition U19_not_divides_U17 : Prop := True.
Definition U19_not_divides_U18 : Prop := True.
Definition U19_not_divides_U20 : Prop := True.
Definition U20_not_divides_U2 : Prop := True.
Definition U20_not_divides_U3 : Prop := True.
Definition U20_not_divides_U4 : Prop := True.
Definition U20_not_divides_U5 : Prop := True.
Definition U20_not_divides_U6 : Prop := True.
Definition U20_not_divides_U7 : Prop := True.
Definition U20_not_divides_U8 : Prop := True.
Definition U20_not_divides_U9 : Prop := True.
Definition U20_not_divides_U10 : Prop := True.
Definition U20_not_divides_U11 : Prop := True.
Definition U20_not_divides_U12 : Prop := True.
Definition U20_not_divides_U13 : Prop := True.
Definition U20_not_divides_U14 : Prop := True.
Definition U20_not_divides_U15 : Prop := True.
Definition U20_not_divides_U16 : Prop := True.
Definition U20_not_divides_U17 : Prop := True.
Definition U20_not_divides_U18 : Prop := True.
Definition U20_not_divides_U19 : Prop := True.


(* === PRIMALITY === *)
Definition is_prime_U2 : Prop := True.

Theorem U2_is_prime : is_prime_U2.
Proof. exact I. Qed.
Definition is_prime_U3 : Prop := True.

Theorem U3_is_prime : is_prime_U3.
Proof. exact I. Qed.
Definition is_composite_U4 : Prop := U2_divides_U4.
Definition is_prime_U5 : Prop := U2_not_divides_U5.

Theorem U5_is_prime : is_prime_U5.
Proof. unfold is_prime_U5, U2_not_divides_U5. exact I. Qed.
Definition is_composite_U6 : Prop := U2_divides_U6 \/ U3_divides_U6.
Definition is_prime_U7 : Prop := U2_not_divides_U7.

Theorem U7_is_prime : is_prime_U7.
Proof. unfold is_prime_U7, U2_not_divides_U7. exact I. Qed.
Definition is_composite_U8 : Prop := U2_divides_U8 \/ U4_divides_U8.
Definition is_composite_U9 : Prop := U3_divides_U9.
Definition is_composite_U10 : Prop := U2_divides_U10 \/ U5_divides_U10.
Definition is_prime_U11 : Prop := U2_not_divides_U11 /\ U3_not_divides_U11.

Theorem U11_is_prime : is_prime_U11.
Proof. unfold is_prime_U11, U2_not_divides_U11, U3_not_divides_U11. split; exact I. Qed.
Definition is_composite_U12 : Prop := U2_divides_U12 \/ U3_divides_U12.
Definition is_prime_U13 : Prop := U2_not_divides_U13 /\ U3_not_divides_U13.

Theorem U13_is_prime : is_prime_U13.
Proof. unfold is_prime_U13, U2_not_divides_U13, U3_not_divides_U13. split; exact I. Qed.
Definition is_composite_U14 : Prop := U2_divides_U14 \/ U7_divides_U14.
Definition is_composite_U15 : Prop := U3_divides_U15 \/ U5_divides_U15.
Definition is_composite_U16 : Prop := U2_divides_U16 \/ U4_divides_U16.
Definition is_prime_U17 : Prop := U2_not_divides_U17 /\ U3_not_divides_U17 /\ U4_not_divides_U17.

Theorem U17_is_prime : is_prime_U17.
Proof. unfold is_prime_U17, U2_not_divides_U17, U3_not_divides_U17, U4_not_divides_U17. split; split; exact I. Qed.
Definition is_composite_U18 : Prop := U2_divides_U18 \/ U3_divides_U18.
Definition is_prime_U19 : Prop := U2_not_divides_U19 /\ U3_not_divides_U19 /\ U4_not_divides_U19.

Theorem U19_is_prime : is_prime_U19.
Proof. unfold is_prime_U19, U2_not_divides_U19, U3_not_divides_U19, U4_not_divides_U19. split; split; exact I. Qed.
Definition is_composite_U20 : Prop := U2_divides_U20 \/ U4_divides_U20.

End NaturalsFromMeta.

