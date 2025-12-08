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


Lemma I_at_pos_while_alive : forall T : Timeline,
  valid_timeline T ->
  forall t, alive (T t) -> alive (T (t + 1)) -> I_at T t > 0.
Proof.
  intros T Hvalid t Ha1 Ha2.
  unfold I_at.
  apply I_val_pos_iff.
  split.
  - exact Ha1.
  - apply (timeline_alive_changes T Hvalid t Ha1 Ha2).
Qed.


Definition max_capacity (T : Timeline) (t : nat) : nat :=
  Nat.max (capacity (T t)) (capacity (T (t + 1))).

Lemma I_at_bounded : forall T : Timeline,
  valid_timeline T ->
  forall t, alive (T t) -> alive (T (t + 1)) ->
  I_at T t < max_capacity T t * max_capacity T t.
Proof.
  intros T Hvalid t Ha1 Ha2.
  unfold I_at, I_val, max_capacity.
  pose proof (timeline_alive_bounded T Hvalid t Ha1) as Hb1.
  pose proof (timeline_alive_bounded T Hvalid (t + 1) Ha2) as Hb2.
  unfold bounded, alive in *.
  unfold DS.
  destruct (Nat.ltb (structure (T (t + 1))) (structure (T t))) eqn:H.
  - apply Nat.ltb_lt in H.
    assert (structure (T t) <= Nat.max (capacity (T t)) (capacity (T (t + 1)))) by lia.
    assert (structure (T t) - structure (T (t + 1)) < structure (T t)) by lia.
    nia.
  - apply Nat.ltb_ge in H.
    assert (structure (T t) <= Nat.max (capacity (T t)) (capacity (T (t + 1)))) by lia.
    assert (structure (T (t + 1)) <= Nat.max (capacity (T t)) (capacity (T (t + 1)))) by lia.
    assert (structure (T (t + 1)) - structure (T t) < structure (T (t + 1))) by lia.
    nia.
Qed.


(* Helper: structure is always at least 1 when alive *)
Lemma alive_ge_1 : forall s : State, alive s -> structure s >= 1.
Proof.
  intros s Ha.
  unfold alive in Ha.
  lia.
Qed.

(* If capacity is constant and system is alive, structure is trapped in [1, cap-1] *)
Lemma structure_in_range : forall T : Timeline,
  valid_timeline T ->
  forall t, alive (T t) ->
  1 <= structure (T t) <= capacity (T t) - 1.
Proof.
  intros T Hvalid t Ha.
  split.
  - apply alive_ge_1. exact Ha.
  - pose proof (timeline_alive_bounded T Hvalid t Ha) as Hb.
    unfold bounded in Hb.
    lia.
Qed.


(* Change is at least 1 when alive *)
Lemma DS_at_least_1 : forall T : Timeline,
  valid_timeline T ->
  forall t, alive (T t) -> alive (T (t + 1)) ->
  DS (T t) (T (t + 1)) >= 1.
Proof.
  intros T Hvalid t Ha1 Ha2.
  apply DS_pos_iff_different.
  apply (timeline_alive_changes T Hvalid t Ha1 Ha2).
Qed.

(* Increasing means structure goes up *)
Definition increasing_at (T : Timeline) (t : nat) : Prop :=
  structure (T t) < structure (T (t + 1)).

(* Decreasing means structure goes down *)
Definition decreasing_at (T : Timeline) (t : nat) : Prop :=
  structure (T t) > structure (T (t + 1)).

(* While alive, must be increasing or decreasing *)
Lemma alive_inc_or_dec : forall T : Timeline,
  valid_timeline T ->
  forall t, alive (T t) -> alive (T (t + 1)) ->
  increasing_at T t \/ decreasing_at T t.
Proof.
  intros T Hvalid t Ha1 Ha2.
  unfold increasing_at, decreasing_at.
  pose proof (timeline_alive_changes T Hvalid t Ha1 Ha2) as Hneq.
  lia.
Qed.


(* If you increase n times starting from t, structure grows by at least n *)
Lemma n_increases_adds_n : forall T : Timeline,
  valid_timeline T ->
  forall t n,
  (forall i, i < n -> alive (T (t + i)) /\ alive (T (t + i + 1))) ->
  (forall i, i < n -> increasing_at T (t + i)) ->
  structure (T (t + n)) >= structure (T t) + n.
Proof.
  intros T Hvalid t n.
  induction n.
  - intros _ _. replace (t + 0) with t by lia. lia.
  - intros Halive Hinc.
    assert (structure (T (t + n)) >= structure (T t) + n) as IH.
    {
      apply IHn.
      - intros i Hi. apply Halive. lia.
      - intros i Hi. apply Hinc. lia.
    }
    specialize (Hinc n).
    assert (increasing_at T (t + n)) as Hinc_n.
    { apply Hinc. lia. }
    unfold increasing_at in Hinc_n.
    replace (t + S n) with (t + n + 1) by lia.
    lia.
Qed.


Lemma increases_bounded : forall T : Timeline,
  valid_timeline T ->
  forall t n,
  alive (T t) ->
  (forall i, i < n -> alive (T (t + i)) /\ alive (T (t + i + 1))) ->
  (forall i, i < n -> increasing_at T (t + i)) ->
  n < capacity (T (t + n)).
Proof.
  intros T Hvalid t n Ha Halive Hinc.
  pose proof (n_increases_adds_n T Hvalid t n Halive Hinc) as Hgrow.
  pose proof (alive_ge_1 (T t) Ha) as Hge1.
  destruct n.
  - replace (t + 0) with t by lia.
    pose proof (timeline_alive_bounded T Hvalid t Ha). unfold bounded in *. lia.
  - assert (alive (T (t + S n))) as Ha_end.
    {
      specialize (Halive n).
      replace (t + n + 1) with (t + S n) in Halive by lia.
      assert (n < S n) by lia.
      apply Halive in H.
      destruct H as [_ H].
      exact H.
    }
    pose proof (timeline_alive_bounded T Hvalid (t + S n) Ha_end) as Hb.
    unfold bounded in Hb.
    lia.
Qed.


(* Symmetric: n decreases subtracts at least n *)
Lemma n_decreases_subtracts_n : forall T : Timeline,
  valid_timeline T ->
  forall t n,
  (forall i, i < n -> alive (T (t + i)) /\ alive (T (t + i + 1))) ->
  (forall i, i < n -> decreasing_at T (t + i)) ->
  structure (T t) >= structure (T (t + n)) + n.
Proof.
  intros T Hvalid t n.
  induction n.
  - intros _ _. replace (t + 0) with t by lia. lia.
  - intros Halive Hdec.
    assert (structure (T t) >= structure (T (t + n)) + n) as IH.
    {
      apply IHn.
      - intros i Hi. apply Halive. lia.
      - intros i Hi. apply Hdec. lia.
    }
    specialize (Hdec n).
    assert (decreasing_at T (t + n)) as Hdec_n.
    { apply Hdec. lia. }
    unfold decreasing_at in Hdec_n.
    replace (t + S n) with (t + n + 1) by lia.
    lia.
Qed.

(* Consecutive decreases are bounded by initial structure *)
Lemma decreases_bounded : forall T : Timeline,
  valid_timeline T ->
  forall t n,
  alive (T t) ->
  (forall i, i < n -> alive (T (t + i)) /\ alive (T (t + i + 1))) ->
  (forall i, i < n -> decreasing_at T (t + i)) ->
  n < structure (T t).
Proof.
  intros T Hvalid t n Ha Halive Hdec.
  pose proof (n_decreases_subtracts_n T Hvalid t n Halive Hdec) as Hshrink.
  pose proof (alive_ge_1 (T t) Ha) as Hge1.
  destruct n.
  - unfold alive in Ha. lia.
  - assert (alive (T (t + S n))) as Ha_end.
    {
      specialize (Halive n).
      replace (t + n + 1) with (t + S n) in Halive by lia.
      assert (n < S n) by lia.
      apply Halive in H.
      destruct H as [_ H].
      exact H.
    }
    pose proof (alive_ge_1 (T (t + S n)) Ha_end) as Hge1_end.
    lia.
Qed.


(* ============================================================ *)
(* Global Capacity Bound *)
(* ============================================================ *)

Definition bounded_capacity (T : Timeline) (cap : nat) : Prop :=
  forall t, capacity (T t) <= cap.

(* With bounded capacity, structure is always below cap *)
Lemma structure_below_cap : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t, alive (T t) -> structure (T t) < cap.
Proof.
  intros T Hvalid cap Hcap t Ha.
  pose proof (timeline_alive_bounded T Hvalid t Ha) as Hb.
  unfold bounded in Hb.
  unfold bounded_capacity in Hcap.
  specialize (Hcap t).
  lia.
Qed.

(* A living sequence of length n means alive at all points from t to t+n *)
Definition living_sequence (T : Timeline) (t n : nat) : Prop :=
  forall i, i <= n -> alive (T (t + i)).

Theorem cant_increase_forever : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t n,
  alive (T t) ->
  n >= cap ->
  living_sequence T t n ->
  ~(forall i, i < n -> increasing_at T (t + i)).
Proof.
  intros T Hvalid cap Hcap t n Ha Hn_big Hliving Hall_inc.
  assert (forall i, i < n -> alive (T (t + i)) /\ alive (T (t + i + 1))) as Halive_pairs.
  { intros i Hi. unfold living_sequence in Hliving. split.
    - apply Hliving. lia.
    - replace (t + i + 1) with (t + (i + 1)) by lia. apply Hliving. lia. }
  pose proof (n_increases_adds_n T Hvalid t n Halive_pairs Hall_inc) as Hgrow.
  pose proof (alive_ge_1 (T t) Ha) as Hge1.
  assert (alive (T (t + n))) as Ha_end.
  { unfold living_sequence in Hliving. apply Hliving. lia. }
  pose proof (structure_below_cap T Hvalid cap Hcap (t + n) Ha_end) as Hbelow.
  lia.
Qed.

(* Symmetric: can't decrease forever *)
Theorem cant_decrease_forever : forall T : Timeline,
  valid_timeline T ->
  forall t n,
  alive (T t) ->
  n >= structure (T t) ->
  living_sequence T t n ->
  ~(forall i, i < n -> decreasing_at T (t + i)).
Proof.
  intros T Hvalid t n Ha Hn_big Hliving Hall_dec.
  assert (forall i, i < n -> alive (T (t + i)) /\ alive (T (t + i + 1))) as Halive_pairs.
  { intros i Hi. unfold living_sequence in Hliving. split.
    - apply Hliving. lia.
    - replace (t + i + 1) with (t + (i + 1)) by lia. apply Hliving. lia. }
  pose proof (n_decreases_subtracts_n T Hvalid t n Halive_pairs Hall_dec) as Hshrink.
  assert (alive (T (t + n))) as Ha_end.
  { unfold living_sequence in Hliving. apply Hliving. lia. }
  pose proof (alive_ge_1 (T (t + n)) Ha_end) as Hge1_end.
  lia.
Qed.


(* Can't stay monotonic forever *)
Theorem cant_stay_monotonic : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t n,
  alive (T t) ->
  living_sequence T t n ->
  n >= cap + structure (T t) ->
  ~(forall i, i < n -> increasing_at T (t + i)) /\
  ~(forall i, i < n -> decreasing_at T (t + i)).
Proof.
  intros T Hvalid cap Hcap t n Ha Hliving Hn_big.
  split.
  - intro Hall_inc.
    apply (cant_increase_forever T Hvalid cap Hcap t n Ha); try assumption. lia.
  - intro Hall_dec.
    apply (cant_decrease_forever T Hvalid t n Ha); try assumption. lia.
Qed.

(* Key tradeoff: I_val scales multiplicatively with structure *)
Lemma I_val_scales_with_structure : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t, alive (T t) -> alive (T (t + 1)) ->
  I_at T t < structure (T t) * cap.
Proof.
  intros T Hvalid cap Hcap t Ha1 Ha2.
  unfold I_at, I_val.
  pose proof (timeline_alive_bounded T Hvalid t Ha1) as Hb1.
  pose proof (timeline_alive_bounded T Hvalid (t + 1) Ha2) as Hb2.
  unfold bounded, bounded_capacity in *.
  pose proof (Hcap t) as Hcap_t.
  pose proof (Hcap (t + 1)) as Hcap_t1.
  unfold alive in Ha1, Ha2.
  unfold DS.
  destruct (Nat.ltb (structure (T (t + 1))) (structure (T t))) eqn:H.
  - apply Nat.ltb_lt in H. nia.
  - apply Nat.ltb_ge in H.
    assert (structure (T (t + 1)) - structure (T t) < structure (T (t + 1))) by lia.
    nia.
Qed.


(* Cumulative I_val over an interval *)
Fixpoint cumulative_I (T : Timeline) (start len : nat) : nat :=
  match len with
  | 0 => 0
  | S n => I_at T start + cumulative_I T (start + 1) n
  end.

(* Cumulative structure over an interval *)
Fixpoint cumulative_S (T : Timeline) (start len : nat) : nat :=
  match len with
  | 0 => 0
  | S n => structure (T start) + cumulative_S T (start + 1) n
  end.

(* Cumulative I_val is bounded by cap times cumulative structure *)
Lemma cumulative_I_bounded : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall start len,
  (forall i, i < len -> alive (T (start + i)) /\ alive (T (start + i + 1))) ->
  cumulative_I T start len <= cap * cumulative_S T start len.
Proof.
  intros T Hvalid cap Hcap start len.
  generalize dependent start.
  induction len.
  - (* Base case: len = 0 *)
    intros start Halive. simpl. lia.
  - (* Inductive case: len = S n *)
    intros start Halive. simpl.
    assert (alive (T start) /\ alive (T (start + 1))) as [Ha0 Ha1].
    { specialize (Halive 0). 
      replace (start + 0) with start in Halive by lia.
      replace (start + 0 + 1) with (start + 1) in Halive by lia.
      apply Halive. lia. }
    assert (I_at T start < structure (T start) * cap) as HI_bound.
    { apply (I_val_scales_with_structure T Hvalid cap Hcap start Ha0 Ha1). }
    assert (cumulative_I T (start + 1) len <= cap * cumulative_S T (start + 1) len) as IH.
    { apply IHlen. intros i Hi. 
      replace (start + 1 + i) with (start + (S i)) by lia.
      replace (start + 1 + i + 1) with (start + (S i) + 1) by lia.
      apply Halive. lia. }
    nia.
Qed.


Lemma cumulative_S_bounded : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall start len,
  (forall i, i < len -> alive (T (start + i))) ->
  cumulative_S T start len <= len * cap.
Proof.
  intros T Hvalid cap Hcap start len.
  generalize dependent start.
  induction len.
  - intros start Halive. simpl. lia.
  - intros start Halive. simpl.
    assert (alive (T start)) as Ha.
    { specialize (Halive 0). replace (start + 0) with start in Halive by lia. apply Halive. lia. }
    pose proof (structure_below_cap T Hvalid cap Hcap start Ha) as Hs_bound.
    assert (cumulative_S T (start + 1) len <= len * cap) as IH.
    { apply IHlen. intros i Hi.
      replace (start + 1 + i) with (start + S i) by lia.
      apply Halive. lia. }
    lia.
Qed.


Lemma cumulative_I_quadratic_bound : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall start len,
  (forall i, i < len -> alive (T (start + i)) /\ alive (T (start + i + 1))) ->
  cumulative_I T start len <= len * cap * cap.
Proof.
  intros T Hvalid cap Hcap start len Halive.
  assert (cumulative_I T start len <= cap * cumulative_S T start len) as H1.
  { apply cumulative_I_bounded; assumption. }
  assert (cumulative_S T start len <= len * cap) as H2.
  { apply cumulative_S_bounded; try assumption.
    intros i Hi. specialize (Halive i Hi). destruct Halive. assumption. }
  nia.
Qed.


(* ============================================================ *)
(* Self-Reflective Systems *)
(* ============================================================ *)

(* Minimum structure needed to represent a state *)
Definition reflection_cost (s : State) : nat := structure s.

(* A state s2 "reflects" s1 if s2 has enough structure to encode s1 *)
Definition reflects (s1 s2 : State) : Prop :=
  structure s2 >= reflection_cost s1.

(* A self-reflective transition: the next state must reflect the current state *)
Definition self_reflective_transition (s1 s2 : State) : Prop :=
  can_transition s1 s2 /\
  reflects s1 s2.

(* A self-reflective timeline: every transition is self-reflective *)
Definition self_reflective_timeline (T : Timeline) : Prop :=
  forall t, self_reflective_transition (T t) (T (t + 1)).

(* Self-reflective timelines are valid timelines *)
Lemma self_reflective_is_valid : forall T : Timeline,
  self_reflective_timeline T ->
  valid_timeline T.
Proof.
  intros T Hsr.
  unfold self_reflective_timeline, self_reflective_transition in Hsr.
  unfold valid_timeline.
  intro t.
  specialize (Hsr t).
  destruct Hsr as [Htrans _].
  exact Htrans.
Qed.

(* Key theorem: self-reflective living transitions must increase structure *)
Lemma self_reflection_forces_growth : forall s1 s2 : State,
  self_reflective_transition s1 s2 ->
  alive s1 -> alive s2 ->
  structure s2 > structure s1.
Proof.
  intros s1 s2 Hsr Ha1 Ha2.
  unfold self_reflective_transition in Hsr.
  destruct Hsr as [Htrans Hrefl].
  unfold reflects, reflection_cost in Hrefl.
  (* Hrefl: structure s2 >= structure s1 *)
  (* From can_transition + both alive: structure s1 <> structure s2 *)
  pose proof (alive_transition_changes s1 s2 Htrans Ha1 Ha2) as Hneq.
  lia.
Qed.

(* Corollary: self-reflective systems can't decrease while alive *)
Lemma self_reflection_no_decrease : forall T : Timeline,
  self_reflective_timeline T ->
  forall t, alive (T t) -> alive (T (t + 1)) ->
  increasing_at T t.
Proof.
  intros T Hsr t Ha1 Ha2.
  unfold increasing_at.
  unfold self_reflective_timeline in Hsr.
  specialize (Hsr t).
  apply (self_reflection_forces_growth (T t) (T (t + 1)) Hsr Ha1 Ha2).
Qed.

(* Self-reflective systems cannot live beyond cap steps *)
Theorem self_reflection_finite_life : forall T : Timeline,
  self_reflective_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t,
  alive (T t) ->
  ~(forall i, i <= cap -> alive (T (t + i))).
Proof.
  intros T Hsr cap Hcap t Ha Halive.
  (* All steps are increasing *)
  assert (forall i, i < cap -> increasing_at T (t + i)) as Hinc.
  { intros i Hi.
    apply self_reflection_no_decrease.
    - exact Hsr.
    - apply Halive. lia.
    - replace (t + i + 1) with (t + (i + 1)) by lia. apply Halive. lia. }
  (* Build living_sequence *)
  assert (living_sequence T t cap) as Hliving.
  { unfold living_sequence. intros i Hi. apply Halive. lia. }
  (* But we proved can't increase forever *)
  pose proof (self_reflective_is_valid T Hsr) as Hvalid.
  apply (cant_increase_forever T Hvalid cap Hcap t cap Ha); try lia.
  - exact Hliving.
  - exact Hinc.
Qed.


(* ============================================================ *)
(* Recursive Self-Reflection and Infinite Regress *)
(* ============================================================ *)

(* Reflection has overhead: encoding yourself requires at least your size + 1 *)
Definition reflection_cost_overhead (s : State) : nat := structure s + 1.

Definition reflects_with_overhead (s1 s2 : State) : Prop :=
  structure s2 >= reflection_cost_overhead s1.

(* n levels of recursive reflection along a timeline *)
Fixpoint n_levels_reflection (T : Timeline) (start : nat) (n : nat) : Prop :=
  match n with
  | 0 => True
  | S m => reflects_with_overhead (T start) (T (start + 1)) /\ 
           n_levels_reflection T (start + 1) m
  end.

(* Each level of reflection forces growth by at least 1 *)
Lemma reflection_level_grows : forall T : Timeline,
  forall start,
  reflects_with_overhead (T start) (T (start + 1)) ->
  structure (T (start + 1)) >= structure (T start) + 1.
Proof.
  intros T start Hrefl.
  unfold reflects_with_overhead, reflection_cost_overhead in Hrefl.
  lia.
Qed.

(* n levels of reflection means structure grows by at least n *)
Lemma n_reflections_adds_n : forall T : Timeline,
  forall start n,
  n_levels_reflection T start n ->
  structure (T (start + n)) >= structure (T start) + n.
Proof.
  intros T start n.
  generalize dependent start.
  induction n.
  - intros start _. replace (start + 0) with start by lia. lia.
  - intros start Hlevels.
    simpl in Hlevels.
    destruct Hlevels as [Hrefl Hrest].
    pose proof (reflection_level_grows T start Hrefl) as Hgrow1.
    specialize (IHn (start + 1) Hrest).
    replace (start + S n) with (start + 1 + n) by lia.
    lia.
Qed.

(* The depth of recursive reflection is bounded *)
Theorem reflection_depth_bounded : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall start n,
  alive (T start) ->
  alive (T (start + n)) ->
  n_levels_reflection T start n ->
  n < cap.
Proof.
  intros T Hvalid cap Hcap start n Ha_start Ha_end Hlevels.
  pose proof (n_reflections_adds_n T start n Hlevels) as Hgrow.
  pose proof (structure_below_cap T Hvalid cap Hcap (start + n) Ha_end) as Hbound.
  pose proof (alive_ge_1 (T start) Ha_start) as Hge1.
  lia.
Qed.

(* Corollary: infinite regress is impossible *)
Theorem no_reflection_infinite_regress : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall start,
  alive (T start) ->
  ~(forall n, alive (T (start + n)) /\ n_levels_reflection T start n).
Proof.
  intros T Hvalid cap Hcap start Ha Hinf.
  (* Take n = cap, derive contradiction *)
  specialize (Hinf cap).
  destruct Hinf as [Ha_cap Hlevels].
  pose proof (reflection_depth_bounded T Hvalid cap Hcap start cap Ha Ha_cap Hlevels) as Hbound.
  lia.
Qed.


(* This says: to reflect n levels deep while staying alive, you need structure(start) + n < cap.
Equivalently: maximum reflection depth = cap - structure(start) - 1.
The gap between your current structure and the capacity ceiling is exactly your budget
for self-reflection. Every level of introspection costs one unit from that budget. *)
Theorem reflection_level_requires_capacity : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall start n,
  alive (T start) ->
  n_levels_reflection T start n ->
  (forall i, i <= n -> alive (T (start + i))) ->
  structure (T start) + n < cap.
Proof.
  intros T Hvalid cap Hcap start n Ha Hlevels Halive.
  pose proof (n_reflections_adds_n T start n Hlevels) as Hgrow.
  assert (alive (T (start + n))) as Ha_n.
  { apply Halive. lia. }
  pose proof (structure_below_cap T Hvalid cap Hcap (start + n) Ha_n) as Hbound.
  lia.
Qed.


(* Exploring theorems related to original I_max arguments in the paper *)
Theorem I_val_confined : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t, alive (T t) -> alive (T (t + 1)) ->
  1 <= I_at T t /\ I_at T t < cap * cap.
Proof.
  intros T Hvalid cap Hcap t Ha1 Ha2.
  split.
  - (* Lower bound: I_at T t >= 1 *)
    unfold I_at, I_val.
    pose proof (alive_ge_1 (T t) Ha1) as Hs_pos.
    pose proof (DS_at_least_1 T Hvalid t Ha1 Ha2) as Hds_pos.
    nia.
  - (* Upper bound: I_at T t < cap * cap *)
    pose proof (I_at_bounded T Hvalid t Ha1 Ha2) as Hbnd.
    unfold max_capacity in Hbnd.
    unfold bounded_capacity in Hcap.
    pose proof (Hcap t) as Hcap_t.
    pose proof (Hcap (t + 1)) as Hcap_t1.
    assert (Nat.max (capacity (T t)) (capacity (T (t + 1))) <= cap) by lia.
    nia.
Qed.


Theorem high_S_limits_DS : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t, alive (T t) -> alive (T (t + 1)) ->
  increasing_at T t ->
  DS (T t) (T (t + 1)) <= cap - structure (T t) - 1.
Proof.
  intros T Hvalid cap Hcap t Ha1 Ha2 Hinc.
  unfold increasing_at in Hinc.
  unfold DS.
  destruct (Nat.ltb (structure (T (t + 1))) (structure (T t))) eqn:Hlt.
  - (* Contradiction: increasing but structure decreased *)
    apply Nat.ltb_lt in Hlt. lia.
  - (* DS = structure(t+1) - structure(t) *)
    apply Nat.ltb_ge in Hlt.
    (* structure(t+1) < capacity(t+1) <= cap *)
    pose proof (timeline_alive_bounded T Hvalid (t + 1) Ha2) as Hb.
    unfold bounded in Hb.
    unfold bounded_capacity in Hcap.
    pose proof (Hcap (t + 1)) as Hcap_t1.
    lia.
Qed.


Definition approaching_death (T : Timeline) (t : nat) : Prop :=
  alive (T t) /\ dead (T (t + 1)).

Theorem final_I_val : forall T : Timeline,
  valid_timeline T ->
  forall t, approaching_death T t ->
  I_at T t = structure (T t) * structure (T t).
Proof.
  intros T Hvalid t Happroach.
  unfold approaching_death in Happroach.
  destruct Happroach as [Ha Hd].
  unfold I_at, I_val, DS.
  unfold dead in Hd.
  rewrite Hd.
  (* structure (T (t+1)) = 0, so ltb 0 (structure (T t)) = true since alive *)
  unfold alive in Ha.
  destruct (Nat.ltb 0 (structure (T t))) eqn:Hlt.
  - (* 0 < structure (T t), so DS = structure(t) - 0 = structure(t) *)
    simpl. lia.
  - (* Contradiction: alive means structure > 0 *)
    apply Nat.ltb_ge in Hlt. lia.
Qed.


(* After a drop, I_val is constrained by the lowered structure *)
Theorem post_drop_I_val_constrained : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t,
  alive (T t) -> alive (T (t + 1)) -> alive (T (t + 2)) ->
  decreasing_at T t ->
  I_at T (t + 1) < (structure (T t) - 1) * cap.
Proof.
  intros T Hvalid cap Hcap t Ha1 Ha2 Ha3 Hdec.
  unfold decreasing_at in Hdec.
  replace (t + 2) with (t + 1 + 1) in Ha3 by lia.
  pose proof (I_val_scales_with_structure T Hvalid cap Hcap (t + 1) Ha2 Ha3) as Hbound.
  assert (structure (T (t + 1)) < structure (T t)) by lia.
  assert (structure (T (t + 1)) <= structure (T t) - 1) by lia.
  nia.
Qed.


(* In 2*cap steps, cannot be all increasing *)
Theorem must_decrease_within_2cap : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t,
  alive (T t) ->
  (forall i, i <= 2 * cap -> alive (T (t + i))) ->
  ~(forall i, i < 2 * cap -> increasing_at T (t + i)).
Proof.
  intros T Hvalid cap Hcap t Ha Halive Hinc.
  assert (living_sequence T t cap) as Hliving.
  { unfold living_sequence. intros i Hi. apply Halive. lia. }
  assert (forall i, i < cap -> increasing_at T (t + i)) as Hinc_cap.
  { intros i Hi. apply Hinc. lia. }
  apply (cant_increase_forever T Hvalid cap Hcap t cap Ha); try lia.
  - exact Hliving.
  - exact Hinc_cap.
Qed.

(* In 2*cap steps, cannot be all decreasing *)
Theorem must_increase_within_2cap : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t,
  alive (T t) ->
  (forall i, i <= 2 * cap -> alive (T (t + i))) ->
  ~(forall i, i < 2 * cap -> decreasing_at T (t + i)).
Proof.
  intros T Hvalid cap Hcap t Ha Halive Hdec.
  assert (living_sequence T t (structure (T t))) as Hliving.
  { unfold living_sequence. intros i Hi. apply Halive. 
    pose proof (structure_below_cap T Hvalid cap Hcap t Ha). lia. }
  assert (forall i, i < structure (T t) -> decreasing_at T (t + i)) as Hdec_s.
  { intros i Hi. apply Hdec.
    pose proof (structure_below_cap T Hvalid cap Hcap t Ha). lia. }
  apply (cant_decrease_forever T Hvalid t (structure (T t)) Ha); try lia.
  - exact Hliving.
  - exact Hdec_s.
Qed.

(* Combined: in any 2*cap steps, there must be both increase and decrease *)
Theorem oscillation_within_2cap : forall T : Timeline,
  valid_timeline T ->
  forall cap, bounded_capacity T cap ->
  forall t,
  alive (T t) ->
  (forall i, i <= 2 * cap -> alive (T (t + i))) ->
  ~(forall i, i < 2 * cap -> increasing_at T (t + i)) /\
  ~(forall i, i < 2 * cap -> decreasing_at T (t + i)).
Proof.
  intros T Hvalid cap Hcap t Ha Halive.
  split.
  - apply must_decrease_within_2cap; assumption.
  - apply must_increase_within_2cap; assumption.
Qed.