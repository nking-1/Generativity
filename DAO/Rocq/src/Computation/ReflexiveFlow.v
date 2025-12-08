(* ============================================================ *)
(* Bounded Mortal Systems: First Principles *)
(* ============================================================ *)

Require Import Lia.
Require Import Arith.

(* ============================================================ *)
(* States *)
(* ============================================================ *)

Record State := {
  structure : nat;
  capacity : nat
}.

Definition alive (s : State) : Prop := structure s > 0.

Definition dead (s : State) : Prop := structure s = 0.

Definition bounded (s : State) : Prop := structure s < capacity s.

Definition valid_state (s : State) : Prop := alive s -> bounded s.

(* ============================================================ *)
(* Transitions *)
(* ============================================================ *)

Definition can_transition (s1 s2 : State) : Prop :=
  (* If alive, must be bounded *)
  (alive s1 -> bounded s1) /\
  (* If both alive, must change *)
  (alive s1 /\ alive s2 -> structure s1 <> structure s2) /\
  (* Death is permanent *)
  (dead s1 -> dead s2).

(* ============================================================ *)
(* Timelines *)
(* ============================================================ *)

Definition Timeline := nat -> State.

Definition valid_timeline (T : Timeline) : Prop :=
  forall t, can_transition (T t) (T (t + 1)).

(* ============================================================ *)
(* Information Flow *)
(* ============================================================ *)

Definition DS (s1 s2 : State) : nat :=
  if Nat.ltb (structure s2) (structure s1) then
    structure s1 - structure s2
  else
    structure s2 - structure s1.

Definition I_val (s1 s2 : State) : nat :=
  (structure s1) * (DS s1 s2).

(* I_val along a timeline at time t *)
Definition I_at (T : Timeline) (t : nat) : nat :=
  I_val (T t) (T (t + 1)).


(* ============================================================ *)
(* Basic State Lemmas *)
(* ============================================================ *)

Lemma alive_or_dead : forall s : State, alive s \/ dead s.
Proof.
  intro s.
  unfold alive, dead.
  lia.
Qed.

Lemma not_alive_is_dead : forall s : State, ~alive s <-> dead s.
Proof.
  intro s.
  unfold alive, dead.
  lia.
Qed.

Lemma not_dead_is_alive : forall s : State, ~dead s <-> alive s.
Proof.
  intro s.
  unfold alive, dead.
  lia.
Qed.

(* ============================================================ *)
(* Transition Lemmas *)
(* ============================================================ *)

Lemma dead_stays_dead : forall s1 s2 : State,
  can_transition s1 s2 -> dead s1 -> dead s2.
Proof.
  intros s1 s2 Htrans Hdead.
  unfold can_transition in Htrans.
  destruct Htrans as [_ [_ Hperm]].
  apply Hperm.
  exact Hdead.
Qed.

Lemma alive_transition_changes : forall s1 s2 : State,
  can_transition s1 s2 -> alive s1 -> alive s2 -> structure s1 <> structure s2.
Proof.
  intros s1 s2 Htrans Ha1 Ha2.
  unfold can_transition in Htrans.
  destruct Htrans as [_ [Hchange _]].
  apply Hchange.
  split; assumption.
Qed.

Lemma alive_is_bounded : forall s1 s2 : State,
  can_transition s1 s2 -> alive s1 -> bounded s1.
Proof.
  intros s1 s2 Htrans Ha1.
  unfold can_transition in Htrans.
  destruct Htrans as [Hbounded _].
  apply Hbounded.
  exact Ha1.
Qed.


(* ============================================================ *)
(* DS Lemmas *)
(* ============================================================ *)

Lemma DS_symmetric : forall s1 s2 : State,
  DS s1 s2 = DS s2 s1.
Proof.
  intros s1 s2.
  unfold DS.
  destruct (Nat.ltb (structure s2) (structure s1)) eqn:H1;
  destruct (Nat.ltb (structure s1) (structure s2)) eqn:H2;
  try lia.
  - apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
  - apply Nat.ltb_ge in H1. apply Nat.ltb_ge in H2. lia.
Qed.

Lemma DS_zero_iff_equal : forall s1 s2 : State,
  DS s1 s2 = 0 <-> structure s1 = structure s2.
Proof.
  intros s1 s2.
  unfold DS.
  destruct (Nat.ltb (structure s2) (structure s1)) eqn:H.
  - apply Nat.ltb_lt in H. lia.
  - apply Nat.ltb_ge in H. lia.
Qed.

Lemma DS_pos_iff_different : forall s1 s2 : State,
  DS s1 s2 > 0 <-> structure s1 <> structure s2.
Proof.
  intros s1 s2.
  unfold DS.
  destruct (Nat.ltb (structure s2) (structure s1)) eqn:H.
  - apply Nat.ltb_lt in H. lia.
  - apply Nat.ltb_ge in H. lia.
Qed.

(* ============================================================ *)
(* I_val Lemmas *)
(* ============================================================ *)

Lemma I_val_zero_if_dead : forall s1 s2 : State,
  dead s1 -> I_val s1 s2 = 0.
Proof.
  intros s1 s2 Hdead.
  unfold I_val, dead in *.
  rewrite Hdead.
  lia.
Qed.

Lemma I_val_pos_iff : forall s1 s2 : State,
  I_val s1 s2 > 0 <-> alive s1 /\ structure s1 <> structure s2.
Proof.
  intros s1 s2.
  unfold I_val, alive.
  split.
  - intro H.
    assert (structure s1 > 0 /\ DS s1 s2 > 0).
    { destruct (structure s1); destruct (DS s1 s2); lia. }
    destruct H0.
    split.
    + exact H0.
    + apply DS_pos_iff_different. exact H1.
  - intros [Halive Hdiff].
    apply DS_pos_iff_different in Hdiff.
    apply Nat.mul_pos_pos; assumption.
Qed.

(* ============================================================ *)
(* Timeline Lemmas *)
(* ============================================================ *)

Lemma timeline_alive_changes : forall T : Timeline,
  valid_timeline T ->
  forall t, alive (T t) -> alive (T (t + 1)) -> structure (T t) <> structure (T (t + 1)).
Proof.
  intros T Hvalid t Ha1 Ha2.
  unfold valid_timeline in Hvalid.
  specialize (Hvalid t).
  apply alive_transition_changes; assumption.
Qed.

Lemma timeline_alive_bounded : forall T : Timeline,
  valid_timeline T ->
  forall t, alive (T t) -> bounded (T t).
Proof.
  intros T Hvalid t Ha.
  unfold valid_timeline in Hvalid.
  specialize (Hvalid t).
  apply alive_is_bounded with (s2 := T (t + 1)); assumption.
Qed.

Lemma timeline_dead_stays_dead : forall T : Timeline,
  valid_timeline T ->
  forall t, dead (T t) -> dead (T (t + 1)).
Proof.
  intros T Hvalid t Hdead.
  unfold valid_timeline in Hvalid.
  specialize (Hvalid t).
  apply (dead_stays_dead (T t) (T (t + 1))); assumption.
Qed.


Lemma dead_forever : forall T : Timeline,
  valid_timeline T ->
  forall t1 t2, t1 <= t2 -> dead (T t1) -> dead (T t2).
Proof.
  intros T Hvalid t1 t2 Hle Hdead.
  induction Hle.
  - (* t1 = t2 *)
    exact Hdead.
  - (* t1 <= m -> t1 <= S m *)
    replace (S m) with (m + 1) by lia.
    apply (timeline_dead_stays_dead T Hvalid m).
    exact IHHle.
Qed.


Lemma alive_before : forall T : Timeline,
  valid_timeline T ->
  forall t1 t2, t1 <= t2 -> alive (T t2) -> alive (T t1).
Proof.
  intros T Hvalid t1 t2 Hle Halive.
  destruct (alive_or_dead (T t1)) as [Ha | Hd].
  - exact Ha.
  - (* If dead at t1, then dead at t2 — contradiction *)
    exfalso.
    apply (dead_forever T Hvalid t1 t2 Hle) in Hd.
    unfold alive, dead in *.
    lia.
Qed.