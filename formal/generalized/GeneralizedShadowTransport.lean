import GeneralizedCodeRecognition

/-! Exact local R/U/D annotation transport. The executable update below is the
label-carrying version of the reviewed Python `update(sh,index)`: output ranks
count the selected token, D emits epsilon, and only a U output promotes U cells.
The invariant states ordinary local label facts, not a deletion-code equivalence.
This module does not prove initialization from an original code, the selection
of exactly one deletion, set merging, pruning, or a serialized DFA. -/
namespace StackSorting.Generalized
namespace LazyCode
namespace Shadow
open List

inductive Cell where
  | R (value : Nat)
  | U (value : Nat)
  | D (value : Nat)
  deriving DecidableEq, Repr

def readValue : Cell → Option Nat
  | .R v => some v
  | _ => none

def unreadValue : Cell → Option Nat
  | .U v => some v
  | _ => none

def reads (cells : List Cell) : List Nat := cells.filterMap readValue

def unreads (cells : List Cell) : List Nat := cells.filterMap unreadValue

def promoteCell : Cell → Cell
  | .U v => .R v
  | c => c

def promote (cells : List Cell) : List Cell := cells.map promoteCell

/-- D is ignored; retained read cells precede retained unread cells. -/
def NotUR : Cell → Cell → Prop
  | .U _, .R _ => False
  | _, _ => True

def Ordered (cells : List Cell) : Prop := cells.Pairwise NotUR

/-- Every current shortened held label is R; every unread retained label in the
original available pool is the next contiguous input interval and is U. -/
def Invariant (next : Nat) (held : List Nat) (cells : List Cell) : Prop :=
  Ordered cells ∧ reads cells = held ∧ HeldInvariant next held ∧
    ∃ count, unreads cells = List.range' next count

/-- A valid selected index is represented by its actual prefix/selected/suffix
split. The label field is bookkeeping only; transitions inspect only R/U/D. -/
def update (pre : List Cell) (selected : Cell) (post : List Cell) : Option Letter × List Cell :=
  match selected with
  | .D _ => (none, pre ++ post)
  | .R _ => (some (.H ((reads pre).length+1)), pre ++ post)
  | .U _ => (some (.N ((unreads pre).length+1)), promote pre ++ post)

@[simp] theorem reads_append (xs ys : List Cell) : reads (xs ++ ys) = reads xs ++ reads ys := by
  simp [reads]
@[simp] theorem unreads_append (xs ys : List Cell) : unreads (xs ++ ys) = unreads xs ++ unreads ys := by
  simp [unreads]
@[simp] theorem reads_cons_R (a : Nat) (xs : List Cell) : reads (.R a :: xs) = a :: reads xs := rfl
@[simp] theorem reads_cons_U (a : Nat) (xs : List Cell) : reads (.U a :: xs) = reads xs := rfl
@[simp] theorem reads_cons_D (a : Nat) (xs : List Cell) : reads (.D a :: xs) = reads xs := rfl
@[simp] theorem unreads_cons_R (a : Nat) (xs : List Cell) : unreads (.R a :: xs) = unreads xs := rfl
@[simp] theorem unreads_cons_U (a : Nat) (xs : List Cell) : unreads (.U a :: xs) = a :: unreads xs := rfl
@[simp] theorem unreads_cons_D (a : Nat) (xs : List Cell) : unreads (.D a :: xs) = unreads xs := rfl

/-- Ignoring the deleted cells is essential: they count in neither rank. -/
theorem reads_eq_nil_of_no_R {cells : List Cell}
    (h : ∀ v, Cell.R v ∉ cells) : reads cells = [] := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    have ht : ∀ v, Cell.R v ∉ cs := fun v hv => h v (by simp [hv])
    cases c with
    | R v => exact False.elim (h v (by simp))
    | U v => simpa using ih ht
    | D v => simpa using ih ht

theorem ordered_remove {pre post : List Cell} {c : Cell}
    (h : Ordered (pre ++ c :: post)) : Ordered (pre ++ post) := by
  exact h.sublist ((List.Sublist.cons c (List.Sublist.refl post)).append_left pre)

theorem ordered_prefix {pre post : List Cell} {c : Cell}
    (h : Ordered (pre ++ c :: post)) : Ordered pre :=
  (List.pairwise_append.mp h).1

theorem no_read_after_unread {pre post : List Cell} {a : Nat}
    (h : Ordered (pre ++ .U a :: post)) : reads post = [] := by
  have ht := (List.pairwise_cons.mp (List.pairwise_append.mp h).2.1).1
  apply reads_eq_nil_of_no_R
  intro v hv
  exact ht (.R v) hv

/-- On ordered annotations promotion preserves sorted label order: old R first,
then the U labels that have just been read. -/
theorem reads_promote {cells : List Cell} (h : Ordered cells) :
    reads (promote cells) = reads cells ++ unreads cells := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    have hh := List.pairwise_cons.mp h
    have ht := ih hh.2
    cases c with
    | R v =>
      change v :: reads (promote cs) = (v :: reads cs) ++ unreads cs
      rw [ht]; rfl
    | D v => exact ht
    | U v =>
      have hn : reads cs = [] := reads_eq_nil_of_no_R (fun w hw => hh.1 (.R w) hw)
      change v :: reads (promote cs) = reads cs ++ v :: unreads cs
      rw [ht, hn]; rfl

@[simp] theorem unreads_promote (cells : List Cell) : unreads (promote cells) = [] := by
  induction cells with
  | nil => rfl
  | cons c cs ih => cases c <;> simpa [promote, promoteCell, unreads, unreadValue] using ih

/-- Exact interval split, including the selected output at offset pre.length. -/
theorem range_split {next count a : Nat} {pre post : List Nat}
    (h : pre ++ a :: post = List.range' next count) :
    a = next + pre.length ∧ pre = List.range' next pre.length ∧
      post = List.range' (a+1) post.length := by
  induction pre generalizing next count with
  | nil =>
    cases count with
    | zero => simp at h
    | succ count =>
      simp only [List.nil_append, List.range'_succ] at h
      obtain ⟨ha, hp⟩ := List.cons.inj h
      subst a
      have hl : post.length = count := by simpa using congrArg List.length hp
      simpa [hl] using hp
  | cons b pre ih =>
    cases count with
    | zero => simp at h
    | succ count =>
      simp only [List.cons_append, List.range'_succ] at h
      obtain ⟨hb, ht⟩ := List.cons.inj h
      subst b
      obtain ⟨ha, hp, hpost⟩ := ih ht
      refine ⟨by simp only [List.length_cons]; omega, ?_, hpost⟩
      simpa [List.range'_succ] using congrArg (next :: ·) hp

/-- Promoting a prefix cannot introduce a U-before-R inversion. -/
theorem ordered_promote_prefix (pre : List Cell) {post : List Cell}
    (h : Ordered post) : Ordered (promote pre ++ post) := by
  induction pre with
  | nil => exact h
  | cons c cs ih =>
    change Ordered (promoteCell c :: (promote cs ++ post))
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro b hb
    cases c <;> cases b <;> trivial

/-- Removing D leaves the shortened frontier, held labels, and unread interval
unchanged. In particular, deleting an original record does not read its batch. -/
theorem invariant_deleted {next a : Nat} {held : List Nat} {pre post : List Cell}
    (h : Invariant next held (pre ++ .D a :: post)) :
    Invariant next held (pre ++ post) := by
  obtain ⟨ho, hr, hi, count, hu⟩ := h
  exact ⟨ordered_remove ho, by simpa using hr, hi, count, by simpa using hu⟩

/-- R uses the one-based rank among R cells, excluding every U and D. -/
theorem invariant_read {next a : Nat} {held : List Nat} {pre post : List Cell}
    (h : Invariant next held (pre ++ .R a :: post)) :
    held = reads pre ++ a :: reads post ∧ a < next ∧
      Invariant next (reads pre ++ reads post) (pre ++ post) := by
  obtain ⟨ho, hr, hi, count, hu⟩ := h
  have he : held = reads pre ++ a :: reads post := by simpa using hr.symm
  rw [he] at hi
  have ha : a < next := hi.2 a (by simp)
  exact ⟨he, ha, ordered_remove ho, by simp, hi.remove, count, by simpa using hu⟩

/-- U emits exactly a positive N batch through its actual shortened label.
The newly held list and frontier are those of the literal lazy decoder. -/
theorem invariant_unread {next a : Nat} {held : List Nat} {pre post : List Cell}
    (h : Invariant next held (pre ++ .U a :: post)) :
    next ≤ a ∧ (unreads pre).length+1 = a+1-next ∧
      Invariant (a+1) (held ++ List.range' next (a-next)) (promote pre ++ post) := by
  obtain ⟨ho, hr, hi, count, hu⟩ := h
  have hn := no_read_after_unread ho
  have hpre : reads pre = held := by simpa [hn] using hr
  have hu' : unreads pre ++ a :: unreads post = List.range' next count := by simpa using hu
  obtain ⟨ha, hup, hus⟩ := range_split hu'
  have hdiff : a-next = (unreads pre).length := by omega
  refine ⟨by omega, by omega, ?_⟩
  refine ⟨ordered_promote_prefix pre (List.pairwise_cons.mp (List.pairwise_append.mp ho).2.1).2,
    ?_, hi.record (by omega), (unreads post).length, ?_⟩
  · rw [reads_append, reads_promote (ordered_prefix ho), hn, List.append_nil, hpre, hup, hdiff]
  · simpa using hus

/-- The update is a literal shortened-decoder step, or epsilon for D. This
extends *any* continuation and is independent of machine widths and acceptance.
There is no assumed annotation-to-deletion equivalence in the hypotheses. -/
theorem update_decodes {next : Nat} {held : List Nat} {pre post : List Cell} {selected : Cell}
    (h : Invariant next held (pre ++ selected :: post)) :
    ∃ next' held', Invariant next' held' (update pre selected post).2 ∧
      ∀ limit code output, Decodes limit next' held' code output →
        Decodes limit next held ((update pre selected post).1.toList ++ code)
          (match selected with | .D _ => output | .R a | .U a => a :: output) := by
  cases selected with
  | D a =>
    exact ⟨next, held, invariant_deleted h, fun _ _ _ ht => ht⟩
  | R a =>
    obtain ⟨he, ha, hi⟩ := invariant_read h
    refine ⟨next, reads pre ++ reads post, hi, ?_⟩
    intro limit code output ht
    change Decodes limit next held (.H ((reads pre).length+1) :: code) (a :: output)
    rw [he]
    exact Decodes.held ha ht
  | U a =>
    obtain ⟨ha, hb, hi⟩ := invariant_unread h
    refine ⟨a+1, held ++ List.range' next (a-next), hi, ?_⟩
    intro limit code output ht
    simpa only [update, Option.toList, List.singleton_append, hb] using Decodes.record ha ht


/-- The Python encoding is U=0, R=1, D=2. -/
def tag : Cell → Nat
  | .U _ => 0
  | .R _ => 1
  | .D _ => 2

def tags (cells : List Cell) : List Nat := cells.map tag

@[simp] theorem tags_append (xs ys : List Cell) : tags (xs ++ ys) = tags xs ++ tags ys := by
  simp [tags]

def promoteTag (t : Nat) : Nat := if t = 0 then 1 else t

/-- Annotation-only split update, with the same 2/1/else branch order as Python.
On erased Cell lists the else branch is exactly U=0. -/
def updateTags (pre : List Nat) (selected : Nat) (post : List Nat) : Option Letter × List Nat :=
  if selected = 2 then (none, pre ++ post)
  else if selected = 1 then (some (.H (pre.count 1+1)), pre ++ post)
  else (some (.N (pre.count 0+1)), pre.map promoteTag ++ post)

theorem reads_length_count (cells : List Cell) : (reads cells).length = (tags cells).count 1 := by
  induction cells with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [tags, tag, ih]

theorem unreads_length_count (cells : List Cell) : (unreads cells).length = (tags cells).count 0 := by
  induction cells with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [tags, tag, ih]

theorem tags_promote (cells : List Cell) : tags (promote cells) = (tags cells).map promoteTag := by
  induction cells with
  | nil => rfl
  | cons c cs ih => cases c <;> simpa [tags, tag, promote, promoteCell, promoteTag] using ih

/-- Erasing all numerical labels commutes exactly with the executable update.
The transport proof therefore applies to the actual R/U/D annotation counts. -/
theorem update_tags (pre post : List Cell) (selected : Cell) :
    updateTags (tags pre) (tag selected) (tags post) =
      ((update pre selected post).1, tags (update pre selected post).2) := by
  cases selected <;> simp [updateTags, update, tag, reads_length_count, unreads_length_count, tags_promote]

/-- Index API mirrors Python's inclusive slice a[:index+1], then deletion.
Out-of-range indices are rejected rather than silently assigned a tag. -/
def updateAt (cells : List Nat) (index : Nat) : Option (Option Letter × List Nat) := do
  let selected ← cells[index]?
  pure (updateTags (cells.take index) selected (cells.drop (index+1)))

/-- Every valid zero-based index is exactly the split update; no off-by-one
translation is left implicit between index and one-based emitted rank. -/
theorem updateAt_split (pre post : List Nat) (selected : Nat) :
    updateAt (pre ++ selected :: post) pre.length = some (updateTags pre selected post) := by
  simp [updateAt]

/-- The annotation-only indexed update enjoys the literal decoder transport
proved above, while carrying no absolute labels in its executable result. -/
theorem updateAt_decodes {next : Nat} {held : List Nat} {pre post : List Cell} {selected : Cell}
    (h : Invariant next held (pre ++ selected :: post)) :
    ∃ letter after next' held',
      updateAt (tags (pre ++ selected :: post)) pre.length = some (letter, tags after) ∧
      Invariant next' held' after ∧
      ∀ limit code output, Decodes limit next' held' code output →
        Decodes limit next held (letter.toList ++ code)
          (match selected with | .D _ => output | .R a | .U a => a :: output) := by
  obtain ⟨next', held', hi, ht⟩ := update_decodes h
  refine ⟨(update pre selected post).1, (update pre selected post).2, next', held', ?_, hi, ht⟩
  have he := updateAt_split (tags pre) (tags post) (tag selected)
  rw [update_tags] at he
  simpa [tags] using he

/-- Retained output value, already in shortened coordinates; D emits no value. -/
def emittedValue : Cell → Option Nat
  | .D _ => none
  | .R a | .U a => some a

/-- Exact executable encoder transport for every suffix, not just a supplied
successful machine run or an accepted shortened continuation. -/
theorem update_encode {next : Nat} {held : List Nat} {pre post : List Cell} {selected : Cell}
    (h : Invariant next held (pre ++ selected :: post)) :
    ∃ next' held', Invariant next' held' (update pre selected post).2 ∧
      ∀ output, encode next held ((emittedValue selected).toList ++ output) =
        (update pre selected post).1.toList ++ encode next' held' output := by
  cases selected with
  | D a => exact ⟨next, held, invariant_deleted h, fun _ => rfl⟩
  | R a =>
    obtain ⟨he, ha, hi⟩ := invariant_read h
    have hn : (reads pre ++ a :: reads post).Nodup := by
      rw [← he]; exact h.2.2.1.nodup
    have hnot : a ∉ reads pre := by
      intro hm
      exact (List.nodup_append.mp hn).2.2 a hm a (by simp) rfl
    refine ⟨next, reads pre ++ reads post, hi, ?_⟩
    intro output
    change encode next held (a :: output) =
      .H ((reads pre).length+1) :: encode next (reads pre ++ reads post) output
    simp [encode, ha, he, List.idxOf_append, hnot, List.erase_append_right]
  | U a =>
    obtain ⟨ha, hb, hi⟩ := invariant_unread h
    refine ⟨a+1, held ++ List.range' next (a-next), hi, ?_⟩
    intro output
    change encode next held (a :: output) = .N ((unreads pre).length+1) :: _
    simp [encode, Nat.not_lt.mpr ha, hb]

/-- Counting retained tags never counts a deleted placeholder. -/
theorem retained_count_le (cells : List Cell) :
    (reads cells).length + (unreads cells).length ≤ cells.length := by
  induction cells with
  | nil => simp [reads, unreads]
  | cons c cs ih => cases c <;> simp_all <;> omega

/-- The shortened U step's physical transient height fits inside the original
available annotation pool. The selected record is counted in this bound. -/
theorem unread_physical_height {next a : Nat} {held : List Nat} {pre post : List Cell}
    (h : Invariant next held (pre ++ .U a :: post)) :
    held.length + ((unreads pre).length+1) ≤ (pre ++ .U a :: post).length := by
  have hn := no_read_after_unread h.1
  have hr : reads pre = held := by simpa [hn] using h.2.1
  have hc := retained_count_le pre
  simp only [List.length_append, List.length_cons]
  rw [← hr]
  omega

/-- The shortened H rank is positive and within the shortened held dictionary. -/
theorem read_rank_valid {next a : Nat} {held : List Nat} {pre post : List Cell}
    (h : Invariant next held (pre ++ .R a :: post)) :
    0 < (reads pre).length+1 ∧ (reads pre).length+1 ≤ held.length := by
  have he := (invariant_read h).1
  simp [he]


/-- Every U/D-only sequence has no U-before-R inversion. -/
theorem ordered_of_no_R {cells : List Cell} (h : ∀ v, Cell.R v ∉ cells) : Ordered cells := by
  induction cells with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
    have ht : ∀ v, Cell.R v ∉ cs := fun v hv => h v (by simp [hv])
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih ht⟩
    intro b hb
    cases c <;> cases b <;> simp only [NotUR]
    exact ht _ hb

theorem ordered_read_prefix (values : List Nat) {cells : List Cell}
    (h : Ordered cells) : Ordered (values.map Cell.R ++ cells) := by
  induction values with
  | nil => exact h
  | cons a values ih =>
    apply List.pairwise_cons.mpr
    exact ⟨fun b _ => by cases b <;> trivial, ih⟩

@[simp] theorem reads_map_R (values : List Nat) : reads (values.map Cell.R) = values := by
  induction values with
  | nil => rfl
  | cons v vs ih => simpa using congrArg (v :: ·) ih
@[simp] theorem unreads_map_R (values : List Nat) : unreads (values.map Cell.R) = [] := by
  induction values with
  | nil => rfl
  | cons v vs ih => exact ih
@[simp] theorem reads_map_U (values : List Nat) : reads (values.map Cell.U) = [] := by
  induction values with
  | nil => rfl
  | cons v vs ih => exact ih
@[simp] theorem unreads_map_U (values : List Nat) : unreads (values.map Cell.U) = values := by
  induction values with
  | nil => rfl
  | cons v vs ih => simpa using congrArg (v :: ·) ih

/-- Birth of a shadow when deleting the (i+1)st member of a new batch with
j later retained members. The surviving labels are already standardized: the
second U interval starts at next+i, closing the deleted label's gap. This is a
local birth invariant; it does not assert original-prefix recognition. -/
theorem new_shadow_invariant {next : Nat} {held : List Nat} (h : HeldInvariant next held)
    (i j : Nat) :
    Invariant next held
      (held.map Cell.R ++ (List.range' next i).map Cell.U ++
        Cell.D (next+i) :: (List.range' (next+i) j).map Cell.U) := by
  have ho : Ordered ((List.range' next i).map Cell.U ++
        Cell.D (next+i) :: (List.range' (next+i) j).map Cell.U) := by
    apply ordered_of_no_R
    intro v
    simp
  refine ⟨by simpa [List.append_assoc] using ordered_read_prefix held ho, by simp,
    h, i+j, ?_⟩
  simp only [unreads_append, unreads_map_R, unreads_map_U, unreads_cons_D, List.nil_append]
  simp

/-- Symbolic all-batch-size record-deletion boundary case. No N is emitted and
all other members of the newly arrived batch remain U, not R. -/
theorem record_deleted_delays (h b : Nat) :
    updateAt (List.replicate h 1 ++ List.replicate b 0 ++ [2]) (h+b) =
      some (none, List.replicate h 1 ++ List.replicate b 0) := by
  have he := updateAt_split (List.replicate h 1 ++ List.replicate b 0) [] 2
  simpa [updateTags] using he


#print axioms range_split
#print axioms invariant_deleted
#print axioms invariant_read
#print axioms invariant_unread
#print axioms update_decodes
#print axioms update_tags
#print axioms updateAt_split
#print axioms updateAt_decodes
#print axioms update_encode
#print axioms unread_physical_height
#print axioms read_rank_valid
#print axioms new_shadow_invariant
#print axioms record_deleted_delays

end Shadow
end LazyCode
end StackSorting.Generalized
