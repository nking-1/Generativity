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