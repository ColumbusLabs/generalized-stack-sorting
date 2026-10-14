import GeneralizedCanonicalRecords

/-! Exact deletion of a canonical nonrecord, with the surviving labels shifted
down by one above the deleted value. All event chronology is preserved. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- Rank compression after deleting `v`. Its value at `v` is irrelevant because
that label is erased. On surviving labels this is ordinary standardization. -/
def deleteRank (v a : Nat) : Nat := if v < a then a-1 else a

def deleteWord (v : Nat) (word : List Nat) : List Nat :=
  (word.filter (fun a => a != v)).map (deleteRank v)

def deleteEvent (v : Nat) : EndpointEvent → Option EndpointEvent
  | .push a => if a = v then none else some (.push (deleteRank v a))
  | .pop a => if a = v then none else some (.pop (deleteRank v a))

def deleteEvents (v : Nat) (events : List EndpointEvent) : List EndpointEvent :=
  events.filterMap (deleteEvent v)

theorem deleteRank_mono (v : Nat) {a b : Nat} (h : a ≤ b) : deleteRank v a ≤ deleteRank v b := by
  unfold deleteRank
  split <;> split <;> omega

theorem deleteRank_succ {v a : Nat} (h : a ≠ v) : deleteRank v (a+1) = deleteRank v a + 1 := by
  unfold deleteRank
  split <;> split <;> omega

/-- Strict order is preserved and reflected on surviving labels. The second
argument may also be the first-unread input boundary. -/
theorem deleteRank_lt_iff {v a b : Nat} (h : a ≠ v) :
    deleteRank v a < deleteRank v b ↔ a < b := by
  unfold deleteRank
  split <;> split <;> omega

theorem deleteRank_injective_surviving {v a b : Nat} (ha : a ≠ v) (hb : b ≠ v)
    (h : deleteRank v a = deleteRank v b) : a = b := by
  have h1 := deleteRank_lt_iff (b := b) ha
  have h2 := deleteRank_lt_iff (b := a) hb
  omega

theorem deleteWord_cons (v a : Nat) (word : List Nat) :
    deleteWord v (a :: word) = if a = v then deleteWord v word
      else deleteRank v a :: deleteWord v word := by
  by_cases h : a = v <;> simp [deleteWord, h]

/-- Deleting one label and compressing an increasing half-open input interval
produces exactly the corresponding compressed half-open interval. -/
theorem deleteWord_range' (v start count : Nat) :
    deleteWord v (List.range' start count) =
      List.range' (deleteRank v start) (deleteRank v (start+count) - deleteRank v start) := by
  induction count generalizing start with
  | zero => simp [deleteWord]
  | succ count ih =>
    rw [List.range'_succ, deleteWord_cons]
    by_cases hv : start = v
    · subst start
      have he : deleteRank v (v+1) = deleteRank v v := by simp [deleteRank]
      simpa [he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (v+1)
    · have hs := deleteRank_succ hv
      have hle := deleteRank_mono v (Nat.le_add_right (start+1) count)
      have hend : (start+1)+count = start+(count+1) := by omega
      rw [hend, hs] at hle
      have hcount : deleteRank v (start+(count+1)) - deleteRank v start =
          (deleteRank v (start+(count+1)) - deleteRank v (start+1)) + 1 := by omega
      rw [ite_eq_right hv, ih, hend, hcount, List.range'_succ, hs]

theorem deleteWord_range {n v : Nat} (hv : v < n) :
    deleteWord v (List.range n) = List.range (n-1) := by
  simpa [List.range_eq_range', deleteRank, hv] using deleteWord_range' v 0 n

theorem deleteWord_eq_erase_map {v : Nat} {word : List Nat} (hn : word.Nodup) :
    deleteWord v word = (word.erase v).map (deleteRank v) := by
  rw [hn.erase_eq_filter v]
  rfl

theorem deleteWord_permutation {n v : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hv : v < n) :
    (deleteWord v output).Perm (List.range (n-1)) := by
  have h := (hp.filter (fun a => a != v)).map (deleteRank v)
  change (deleteWord v output).Perm (deleteWord v (List.range n)) at h
  simpa [deleteWord_range hv] using h

theorem deleteEvents_append (v : Nat) (xs ys : List EndpointEvent) :
    deleteEvents v (xs ++ ys) = deleteEvents v xs ++ deleteEvents v ys := by
  simp [deleteEvents]

theorem deleteEvents_pushes (v : Nat) (input : List Nat) :
    deleteEvents v (input.map EndpointEvent.push) = (deleteWord v input).map EndpointEvent.push := by
  induction input with
  | nil => rfl
  | cons a input ih =>
    by_cases h : a = v <;> simp [deleteEvents, deleteEvent, deleteWord, h] at ih ⊢ <;> exact ih

/-- Exact schedule erasure, valid even for general output words whenever the
deleted value is not a record in the specified canonical suffix state. -/
theorem canonicalEvents_delete_nonrecord {next v : Nat} {output : List Nat}
    (hv : v ∉ canonicalRecords next output) :
    canonicalEvents (deleteRank v next) (deleteWord v output) =
      deleteEvents v (canonicalEvents next output) := by
  induction output generalizing next with
  | nil => simp [deleteWord, canonicalEvents, deleteEvents]
  | cons a output ih =>
    by_cases ha : a < next
    · have ht : v ∉ canonicalRecords next output := by simpa [canonicalRecords, ha] using hv
      have hit := ih ht
      by_cases he : a = v
      · subst a
        simpa [canonicalEvents, ha, deleteWord_cons, deleteEvents, deleteEvent] using hit
      · have ha' : deleteRank v a < deleteRank v next := (deleteRank_lt_iff he).mpr ha
        simpa [canonicalEvents, ha, ha', deleteWord_cons, he, deleteEvents, deleteEvent] using
          congrArg (EndpointEvent.pop (deleteRank v a) :: ·) hit
    · have hh : v ≠ a ∧ v ∉ canonicalRecords (a+1) output := by
        simpa [canonicalRecords, ha] using hv
      have he : a ≠ v := Ne.symm hh.1
      have hit := ih hh.2
      have ha' : ¬ deleteRank v a < deleteRank v next := by
        simpa only [deleteRank_lt_iff he] using ha
      have hs := deleteRank_succ he
      have hb : next + (a+1-next) = a+1 := by omega
      have hrange : deleteWord v (List.range' next (a+1-next)) =
          List.range' (deleteRank v next) (deleteRank v a+1-deleteRank v next) := by
        rw [deleteWord_range', hb, hs]
      simp only [deleteWord_cons, ite_eq_right he, canonicalEvents, ite_eq_right ha, ite_eq_right ha',
        deleteEvents_append, deleteEvents_pushes, hrange]
      have hpop (events : List EndpointEvent) :
          deleteEvents v (.pop a :: events) = .pop (deleteRank v a) :: deleteEvents v events := by
        simp [deleteEvents, deleteEvent, he]
      rw [hpop, ← hs, hit]

/-- The surviving record labels are exactly the old records under the same rank
compression; no new record is introduced by nonrecord deletion. -/
theorem canonicalRecords_delete_nonrecord {next v : Nat} {output : List Nat}
    (hv : v ∉ canonicalRecords next output) :
    canonicalRecords (deleteRank v next) (deleteWord v output) =
      (canonicalRecords next output).map (deleteRank v) := by
  induction output generalizing next with
  | nil => simp [deleteWord, canonicalRecords]
  | cons a output ih =>
    by_cases ha : a < next
    · have ht : v ∉ canonicalRecords next output := by simpa [canonicalRecords, ha] using hv
      by_cases he : a = v
      · subst a
        simpa [deleteWord_cons, canonicalRecords, ha] using ih ht
      · have ha' := (deleteRank_lt_iff he).mpr ha
        simpa [deleteWord_cons, he, canonicalRecords, ha, ha'] using ih ht
    · have hh : v ≠ a ∧ v ∉ canonicalRecords (a+1) output := by
        simpa [canonicalRecords, ha] using hv
      have he : a ≠ v := Ne.symm hh.1
      have ha' : ¬ deleteRank v a < deleteRank v next := by
        simpa only [deleteRank_lt_iff he] using ha
      simpa [deleteWord_cons, he, canonicalRecords, ha, ha', ← deleteRank_succ he] using
        congrArg (deleteRank v a :: ·) (ih hh.2)

theorem deleteRank_mem_map_iff {v a : Nat} {records : List Nat}
    (ha : a ≠ v) (hv : v ∉ records) :
    deleteRank v a ∈ records.map (deleteRank v) ↔ a ∈ records := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    have hne : b ≠ v := fun heq => hv (heq ▸ hb)
    have heq := deleteRank_injective_surviving hne ha he
    simpa [heq] using hb
  · intro h
    exact List.mem_map.mpr ⟨a, h, rfl⟩

theorem deleteWord_filter_nonrecords (v : Nat) (input records : List Nat)
    (hv : v ∉ records) :
    deleteWord v (input.filter (fun a => !records.contains a)) =
      (deleteWord v input).filter (fun a => !(records.map (deleteRank v)).contains a) := by
  unfold deleteWord
  rw [List.filter_map, List.filter_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro a _
  by_cases he : a = v
  · subst a; simp
  · have hm := deleteRank_mem_map_iff he hv
    have hc : records.contains a = (records.map (deleteRank v)).contains (deleteRank v a) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [List.contains_iff_mem] using hm.symm
    rw [hc, Bool.and_comm]
    rfl

/-- Exact identity of the standardized nonrecord token lists, in increasing
input order. This is the subsystem used by the criticality bridge. -/
theorem nonrecordTokens_delete_nonrecord {n v : Nat} {output : List Nat}
    (hm : v < n) (hv : v ∉ canonicalRecords 0 output) :
    nonrecordTokens (n-1) (deleteWord v output) = deleteWord v (nonrecordTokens n output) := by
  have hr : canonicalRecords 0 (deleteWord v output) =
      (canonicalRecords 0 output).map (deleteRank v) := by
    simpa [deleteRank] using canonicalRecords_delete_nonrecord hv
  unfold nonrecordTokens
  rw [hr, deleteWord_filter_nonrecords v (List.range n) (canonicalRecords 0 output) hv,
    deleteWord_range hm]

/-- Ordinary one-value deletion and standardization of a permutation nonrecord
has precisely the old schedule with that value's two events erased and every
surviving event label shifted. The chronological equalities are conclusions. -/
theorem permutation_nonrecord_deletion {n v : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hm : v ∈ List.range n)
    (hv : v ∉ canonicalRecords 0 output) :
    (deleteWord v output).Perm (List.range (n-1)) ∧
      deleteWord v output = (output.erase v).map (deleteRank v) ∧
      canonicalEvents 0 (deleteWord v output) = deleteEvents v (canonicalEvents 0 output) ∧
      canonicalRecords 0 (deleteWord v output) = (canonicalRecords 0 output).map (deleteRank v) ∧
      nonrecordTokens (n-1) (deleteWord v output) = deleteWord v (nonrecordTokens n output) := by
  have hn : output.Nodup := hp.nodup_iff.mpr List.nodup_range
  exact ⟨deleteWord_permutation hp (List.mem_range.mp hm), deleteWord_eq_erase_map hn,
    by simpa [deleteRank] using canonicalEvents_delete_nonrecord hv,
    by simpa [deleteRank] using canonicalRecords_delete_nonrecord hv,
    nonrecordTokens_delete_nonrecord (List.mem_range.mp hm) hv⟩

#print axioms deleteRank_lt_iff
#print axioms deleteRank_injective_surviving
#print axioms deleteWord_range'
#print axioms canonicalEvents_delete_nonrecord
#print axioms canonicalRecords_delete_nonrecord
#print axioms nonrecordTokens_delete_nonrecord
#print axioms permutation_nonrecord_deletion
end StackSorting.Generalized
