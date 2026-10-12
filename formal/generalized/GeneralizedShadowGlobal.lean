import GeneralizedShadowTransport

/-! Global exact fixed-value deletion shadow transport over literal original
lazy codes. Annotation positions track actual original held labels in order.
No merging, rejection pruning, finite closure, or serialized DFA is asserted. -/
namespace StackSorting.Generalized
namespace LazyCode
namespace Shadow
open List

/-- Inverse of standardization on the surviving labels. -/
def restoreRank (v a : Nat) : Nat := if a < v then a else a+1

def originalValue (v : Nat) : Cell → Nat
  | .D _ => v
  | .R a | .U a => restoreRank v a

@[simp] theorem restoreRank_ne (v a : Nat) : restoreRank v a ≠ v := by
  unfold restoreRank
  split <;> omega
@[simp] theorem deleteRank_restoreRank (v a : Nat) : deleteRank v (restoreRank v a) = a := by
  unfold restoreRank deleteRank
  split <;> split <;> omega

theorem restoreRank_deleteRank {v a : Nat} (h : a ≠ v) :
    restoreRank v (deleteRank v a) = a := by
  unfold restoreRank deleteRank
  split <;> split <;> omega

/-- Every retained cell carries precisely its original label's deletion rank. -/
theorem emittedValue_original (v : Nat) (c : Cell) :
    (emittedValue c).toList = deleteWord v [originalValue v c] := by
  cases c <;> simp [emittedValue, originalValue, deleteWord]

@[simp] theorem originalValue_promoteCell (v : Nat) (c : Cell) :
    originalValue v (promoteCell c) = originalValue v c := by cases c <;> rfl
@[simp] theorem originalValue_promote (v : Nat) (cells : List Cell) :
    (promote cells).map (originalValue v) = cells.map (originalValue v) := by
  simp [promote, List.map_map]

def arrivalCell (v a : Nat) : Cell := if a = v then .D a else .U (deleteRank v a)
def arrivals (v start count : Nat) : List Cell := (List.range' start count).map (arrivalCell v)

@[simp] theorem originalValue_arrivalCell (v a : Nat) :
    originalValue v (arrivalCell v a) = a := by
  by_cases h : a = v
  · simp [arrivalCell, h, originalValue]
  · simp [arrivalCell, h, originalValue, restoreRank_deleteRank h]
@[simp] theorem originalValue_arrivals (v start count : Nat) :
    (arrivals v start count).map (originalValue v) = List.range' start count := by
  simp [arrivals, List.map_map, Function.comp_def]
@[simp] theorem arrivals_length (v start count : Nat) : (arrivals v start count).length = count := by
  simp [arrivals]

theorem arrival_no_R (v : Nat) (xs : List Nat) :
    ∀ a, Cell.R a ∉ xs.map (arrivalCell v) := by
  intro a ha
  obtain ⟨b, _, he⟩ := List.mem_map.mp ha
  unfold arrivalCell at he
  split at he <;> cases he

@[simp] theorem reads_arrivals (v start count : Nat) : reads (arrivals v start count) = [] :=
  reads_eq_nil_of_no_R (arrival_no_R v _)

theorem unreads_arrival_map (v : Nat) (xs : List Nat) :
    unreads (xs.map (arrivalCell v)) = deleteWord v xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a = v <;> simp [arrivalCell, h, deleteWord_cons, ih]

@[simp] theorem unreads_arrivals (v start count : Nat) :
    unreads (arrivals v start count) =
      List.range' (deleteRank v start) (deleteRank v (start+count)-deleteRank v start) := by
  rw [arrivals, unreads_arrival_map, deleteWord_range']

theorem ordered_append_no_R {cells more : List Cell} (ho : Ordered cells)
    (hn : ∀ a, Cell.R a ∉ more) : Ordered (cells ++ more) := by
  apply List.pairwise_append.mpr
  refine ⟨ho, ordered_of_no_R hn, ?_⟩
  intro a _ b hb
  cases a <;> cases b <;> simp only [NotUR]
  exact hn _ hb

/-- Global alignment and exact frontier endpoint, including postponed arrivals
following deletion of an original record. -/
def GlobalInvariant (v originalNext : Nat) (originalHeld : List Nat)
    (next : Nat) (held : List Nat) (cells : List Cell) : Prop :=
  Invariant next held cells ∧
  cells.map (originalValue v) = originalHeld ∧
  next + (unreads cells).length = deleteRank v originalNext

theorem global_initial (v : Nat) : GlobalInvariant v 0 [] 0 [] [] := by
  simp [GlobalInvariant, Invariant, Ordered, reads, unreads, HeldInvariant, deleteRank]


/-- At every global state, surviving annotations are exactly the standardized
actual original held labels, in their original dictionary order. -/
theorem retained_values_eq_deleteWord (v : Nat) (cells : List Cell) :
    cells.filterMap emittedValue = deleteWord v (cells.map (originalValue v)) := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    have he := emittedValue_original v c
    have ha : deleteWord v (originalValue v c :: cs.map (originalValue v)) =
        deleteWord v [originalValue v c] ++ deleteWord v (cs.map (originalValue v)) := by
      change deleteWord v ([originalValue v c] ++ cs.map (originalValue v)) = _
      simp only [deleteWord, List.filter_append, List.map_append]
    simp only [List.map_cons, ha, ← he, ← ih]
    cases c <;> rfl

theorem global_retained {v originalNext next : Nat} {originalHeld held : List Nat}
    {cells : List Cell} (h : GlobalInvariant v originalNext originalHeld next held cells) :
    cells.filterMap emittedValue = deleteWord v originalHeld := by
  rw [retained_values_eq_deleteWord, h.2.1]

/-- A complete original decoding leaves no phantom annotation or held label.
The shortened frontier is exactly the compressed original terminal frontier. -/
theorem global_terminal {v n next : Nat} {held : List Nat} {cells : List Cell}
    (h : GlobalInvariant v n [] next held cells) :
    cells = [] ∧ held = [] ∧ next = deleteRank v n := by
  have hc : cells = [] := List.map_eq_nil_iff.mp h.2.1
  subst cells
  exact ⟨rfl, h.1.2.1.symm, by simpa [unreads] using h.2.2⟩

/-- Original N batches append U/D cells in their exact original input order;
the unread compressed interval extends with no gap and no premature promotion. -/
theorem global_arrivals {v originalNext next : Nat} {originalHeld held : List Nat}
    {cells : List Cell} (h : GlobalInvariant v originalNext originalHeld next held cells)
    (count : Nat) :
    GlobalInvariant v (originalNext+count) (originalHeld ++ List.range' originalNext count)
      next held (cells ++ arrivals v originalNext count) := by
  obtain ⟨⟨ho, hr, hi, oldCount, hu⟩, halign, hend⟩ := h
  have hc : next+oldCount = deleteRank v originalNext := by simpa [hu] using hend
  have hle := deleteRank_mono v (Nat.le_add_right originalNext count)
  refine ⟨⟨ordered_append_no_R ho (arrival_no_R v _), by simp [hr], hi,
    oldCount+(deleteRank v (originalNext+count)-deleteRank v originalNext), ?_⟩,
    by simp [halign], ?_⟩
  · simp only [unreads_append, hu, unreads_arrivals]
    rw [← hc]
    simpa only [Nat.one_mul] using (List.range'_append (s := next) (m := oldCount)
      (n := deleteRank v (originalNext+count)-(next+oldCount)) (step := 1))
  · simp only [unreads_append, List.length_append, unreads_arrivals, List.length_range']
    omega

/-- Promotion and removal preserve the ordered original-label dictionary. -/
theorem update_original (v : Nat) (pre post : List Cell) (selected : Cell) :
    (update pre selected post).2.map (originalValue v) =
      pre.map (originalValue v) ++ post.map (originalValue v) := by
  cases selected <;> simp [update]

/-- Strong local transport additionally preserves the exact compressed endpoint.
The emitted output is the actual selected original value under deletion. -/
theorem global_update {v originalNext next : Nat} {held : List Nat}
    {pre post : List Cell} {selected : Cell}
    (h : GlobalInvariant v originalNext
      (pre.map (originalValue v) ++ originalValue v selected :: post.map (originalValue v))
      next held (pre ++ selected :: post)) :
    ∃ next' held',
      GlobalInvariant v originalNext (pre.map (originalValue v) ++ post.map (originalValue v))
        next' held' (update pre selected post).2 ∧
      ∀ output, encode next held (deleteWord v (originalValue v selected :: output)) =
        (update pre selected post).1.toList ++ encode next' held' (deleteWord v output) := by
  have hemit : ∀ output, deleteWord v (originalValue v selected :: output) =
      (emittedValue selected).toList ++ deleteWord v output := by
    intro output
    rw [emittedValue_original v selected]
    change deleteWord v ([originalValue v selected] ++ output) = _
    simp only [deleteWord, List.filter_append, List.map_append]
  cases selected with
  | D a =>
    refine ⟨next, held, ⟨invariant_deleted h.1, update_original _ _ _ _, ?_⟩, ?_⟩
    · simpa [update] using h.2.2
    · intro output; rw [hemit]; rfl
  | R a =>
    obtain ⟨hheld, ha, hi⟩ := invariant_read h.1
    -- Use the explicit encoder equation to retain the literal successor state.
    have hn : a ∉ reads pre := by
      have hh := h.1.2.2.1.nodup
      rw [hheld] at hh
      intro hm
      exact (List.nodup_append.mp hh).2.2 a hm a (by simp) rfl
    refine ⟨next, reads pre ++ reads post,
      ⟨hi, update_original _ _ _ _, ?_⟩, ?_⟩
    · simpa [update] using h.2.2
    · intro output
      rw [hemit]
      simp [emittedValue, encode, ha, hheld, List.idxOf_append, hn, List.erase_append_right, update]
  | U a =>
    obtain ⟨ha, hb, hi⟩ := invariant_unread h.1
    refine ⟨a+1, held ++ List.range' next (a-next),
      ⟨hi, update_original _ _ _ _, ?_⟩, ?_⟩
    · have hend := h.2.2
      simp only [unreads_append, unreads_cons_U, List.length_append, List.length_cons] at hend
      simp only [update, unreads_append, unreads_promote, List.nil_append]
      omega
    · intro output
      rw [hemit]
      simp [emittedValue, encode, Nat.not_lt.mpr ha, update, hb]


/-- Label-carrying indexed update. It is the same split update as updateAt. -/
def updateCellsAt (cells : List Cell) (index : Nat) : Option (Option Letter × List Cell) := do
  let selected ← cells[index]?
  pure (update (cells.take index) selected (cells.drop (index+1)))

@[simp] theorem updateCellsAt_split (pre post : List Cell) (selected : Cell) :
    updateCellsAt (pre ++ selected :: post) pre.length = some (update pre selected post) := by
  simp [updateCellsAt]

/-- Executable fixed-value shadow, driven only by the original N/H letters.
The original input frontier identifies the unique deleted arrival. Original H
indices and the final index of every inclusive N batch are used literally. -/
def transduce (v originalNext : Nat) (cells : List Cell) : List Letter → Option (List Letter)
  | [] => some []
  | .H k :: code => if 0 < k then do
      let (letter, after) ← updateCellsAt cells (k-1)
      let tail ← transduce v originalNext after code
      pure (letter.toList ++ tail)
    else none
  | .N b :: code => if 0 < b then do
      let (letter, after) ← updateCellsAt (cells ++ arrivals v originalNext b) (cells.length+b-1)
      let tail ← transduce v (originalNext+b) after code
      pure (letter.toList ++ tail)
    else none

theorem aligned_split {v : Nat} {cells : List Cell} {pre post : List Nat} {a : Nat}
    (h : cells.map (originalValue v) = pre ++ a :: post) :
    ∃ before selected after, cells = before ++ selected :: after ∧
      before.map (originalValue v) = pre ∧ originalValue v selected = a ∧
      after.map (originalValue v) = post := by
  obtain ⟨before, tail, he, hp, ht⟩ := List.map_eq_append_iff.mp h
  obtain ⟨selected, after, hs, ha, hpost⟩ := List.map_eq_cons_iff.mp ht
  exact ⟨before, selected, after, by rw [he, hs], hp, ha, hpost⟩

theorem arrivals_record {v originalNext a : Nat} (ha : originalNext ≤ a) :
    arrivals v originalNext (a+1-originalNext) =
      arrivals v originalNext (a-originalNext) ++ [arrivalCell v a] := by
  have hb : a+1-originalNext = (a-originalNext)+1 := by omega
  have he : originalNext+(a-originalNext) = a := by omega
  simp [arrivals, hb, List.range'_concat, he]

/-- All-length global semantic connection. The hypotheses concern the actual
original decoding and the explicit label/frontier invariant, never equality of
the emitted shadow code with a shortened encoding. -/
theorem transduce_eq_encode {v limit originalNext next : Nat}
    {originalHeld held output : List Nat} {cells : List Cell} {code : List Letter}
    (hd : Decodes limit originalNext originalHeld code output)
    (h : GlobalInvariant v originalNext originalHeld next held cells) :
    transduce v originalNext cells code = some (encode next held (deleteWord v output)) := by
  induction hd generalizing next held cells with
  | nil => simp [transduce, deleteWord, encode]
  | @held originalNext a pre post code output old tail ih =>
    obtain ⟨before, selected, after, hcells, hpre, ha, hpost⟩ := aligned_split h.2.1
    have hlen : pre.length = before.length := by rw [← hpre]; simp
    subst cells
    have hglobal : GlobalInvariant v originalNext
        (before.map (originalValue v) ++ originalValue v selected :: after.map (originalValue v))
        next held (before ++ selected :: after) := by simpa [hpre, ha, hpost] using h
    obtain ⟨next', held', hinv, hencode⟩ := global_update hglobal
    have htail : GlobalInvariant v originalNext (pre ++ post) next' held'
        (update before selected after).2 := by simpa [hpre, hpost] using hinv
    have hrun := ih htail
    rw [← ha, hencode]
    simp [transduce, hlen, hrun]
  | @record originalNext a originalHeld code output new tail ih =>
    let before := cells ++ arrivals v originalNext (a-originalNext)
    let selected := arrivalCell v a
    have hbefore : before.map (originalValue v) = originalHeld ++ List.range' originalNext (a-originalNext) := by
      simp [before, h.2.1]
    have hselected : originalValue v selected = a := originalValue_arrivalCell v a
    have hfull : cells ++ arrivals v originalNext (a+1-originalNext) = before ++ selected :: [] := by
      simp only [arrivals_record new, List.append_assoc, before, selected]
    have hnext : originalNext+(a+1-originalNext) = a+1 := by omega
    have hidx : cells.length+(a+1-originalNext)-1 = before.length := by
      simp [before]; omega
    have hglobal : GlobalInvariant v (a+1)
        (before.map (originalValue v) ++ originalValue v selected :: [].map (originalValue v))
        next held (before ++ selected :: []) := by
      have hg := global_arrivals h (a+1-originalNext)
      rw [hnext, hfull] at hg
      have hb : a+1-originalNext = (a-originalNext)+1 := by omega
      have he : originalNext+(a-originalNext) = a := by omega
      simpa [hbefore, hselected, hb, List.range'_concat, he] using hg
    obtain ⟨next', held', hinv, hencode⟩ := global_update hglobal
    have htail : GlobalInvariant v (a+1) (originalHeld ++ List.range' originalNext (a-originalNext))
        next' held' (update before selected []).2 := by simpa [hbefore] using hinv
    have hrun := ih htail
    have he := hencode output
    rw [hselected] at he
    rw [he]
    have positive : 0 < a+1-originalNext := by omega
    simp only [transduce, positive, ite_true, hnext, hfull, hidx, updateCellsAt_split]
    simp [hrun]

/-- Initialization is proved for every deletion value, including the case that
its arrival lies after many already processed original outputs. -/
theorem transduce_initial_eq_encode {v n : Nat} {code : List Letter} {output : List Nat}
    (hd : Decodes n 0 [] code output) :
    transduce v 0 [] code = some (encode 0 [] (deleteWord v output)) :=
  transduce_eq_encode hd (global_initial v)


/-- Erasing label bookkeeping commutes with every indexed update, including
out-of-range failure. -/
theorem updateCellsAt_tags (cells : List Cell) (index : Nat) :
    updateAt (tags cells) index =
      (updateCellsAt cells index).map (fun p => (p.1, tags p.2)) := by
  simp only [updateAt, updateCellsAt, tags, List.getElem?_map]
  cases he : cells[index]? with
  | none => simp
  | some c =>
    simpa [← List.map_take, ← List.map_drop, tags] using
      congrArg some (update_tags (cells.take index) (cells.drop (index+1)) c)

def arrivalTags (v start count : Nat) : List Nat :=
  (List.range' start count).map (fun a => if a = v then 2 else 0)

@[simp] theorem tags_arrivals (v start count : Nat) :
    tags (arrivals v start count) = arrivalTags v start count := by
  simp only [tags, arrivals, arrivalTags, List.map_map]
  apply List.map_congr_left
  intro a _
  by_cases h : a = v <;> simp [arrivalCell, h, tag]


theorem arrivalTags_absent {v start count : Nat}
    (h : v ∉ List.range' start count) : arrivalTags v start count = List.replicate count 0 := by
  unfold arrivalTags
  have he : ∀ a ∈ List.range' start count, (if a = v then 2 else 0) = 0 := by
    intro a ha
    have hn : a ≠ v := by intro hv; subst a; exact h ha
    simp [hn]
  simpa using List.map_eq_replicate_iff.mpr he

/-- Before deletion's unique input arrival, ordinary batches append all U. -/
theorem arrivalTags_before {v start count : Nat} (h : start+count ≤ v) :
    arrivalTags v start count = List.replicate count 0 := by
  apply arrivalTags_absent
  intro hm
  have hh := List.mem_range'.mp hm
  omega

/-- The exact Python birth vector: h old R cells, i U cells, one D, then j U.
The deleted original value is start+i, and the inclusive batch is i+1+j. -/
theorem birth_tags (held : List Nat) (start i j : Nat) :
    tags (held.map Cell.R ++ arrivals (start+i) start (i+1+j)) =
      List.replicate held.length 1 ++ List.replicate i 0 ++ 2 :: List.replicate j 0 := by
  have hpre := arrivalTags_before (v := start+i) (start := start) (count := i) (by omega)
  have hpost : arrivalTags (start+i) (start+i+1) j = List.replicate j 0 := by
    apply arrivalTags_absent
    intro hm
    have hh := List.mem_range'.mp hm
    omega
  have hrange : List.range' start (i+1+j) =
      List.range' start i ++ (start+i) :: List.range' (start+i+1) j := by
    have hcount : i+1+j = i+(j+1) := by omega
    rw [hcount, ← List.range'_append (s := start) (m := i) (n := j+1) (step := 1)]
    simp [List.range'_succ]
  have htags : tags (held.map Cell.R) = List.replicate held.length 1 := by
    simp only [tags, List.map_map, Function.comp_def, tag]
    exact List.map_eq_replicate_iff.mpr (fun _ _ => rfl)
  rw [tags_append, htags, tags_arrivals]
  simp only [arrivalTags, hrange, List.map_append, List.map_cons, ite_true]
  change List.replicate held.length 1 ++ (arrivalTags (start+i) start i ++ 2 :: arrivalTags (start+i) (start+i+1) j) = _
  rw [hpre, hpost, List.append_assoc]

/-- An unmaterialized deletion shadow agrees with the original code before
birth: inclusive N updates append exactly N and return only R cells. -/
theorem before_birth_record (h b : Nat) :
    updateAt (List.replicate h 1 ++ List.replicate b 0 ++ [0]) (h+b) =
      some (some (.N (b+1)), List.replicate (h+b) 1) := by
  have he := updateAt_split (List.replicate h 1 ++ List.replicate b 0) [] 0
  simpa [updateTags, promoteTag, List.count_replicate] using he

/-- The corresponding original H rank is unchanged before birth. -/
theorem before_birth_held (i j : Nat) :
    updateAt (List.replicate i 1 ++ 1 :: List.replicate j 1) i =
      some (some (.H (i+1)), List.replicate (i+j) 1) := by
  have he := updateAt_split (List.replicate i 1) (List.replicate j 1) 1
  simpa [updateTags] using he

/-- Annotation-only global driver: U=0, R=1, D=2, with the Python inclusive
output indices and D/H/N update. The deletion is scheduled by its input label;
no standardized output permutation is consulted by this executable function. -/
def transduceTags (v originalNext : Nat) (cells : List Nat) : List Letter → Option (List Letter)
  | [] => some []
  | .H k :: code => if 0 < k then do
      let (letter, after) ← updateAt cells (k-1)
      let tail ← transduceTags v originalNext after code
      pure (letter.toList ++ tail)
    else none
  | .N b :: code => if 0 < b then do
      let (letter, after) ← updateAt (cells ++ arrivalTags v originalNext b) (cells.length+b-1)
      let tail ← transduceTags v (originalNext+b) after code
      pure (letter.toList ++ tail)
    else none

theorem transduce_tags (v originalNext : Nat) (cells : List Cell) (code : List Letter) :
    transduceTags v originalNext (tags cells) code = transduce v originalNext cells code := by
  induction code generalizing originalNext cells with
  | nil => rfl
  | cons letter code ih =>
    cases letter with
    | H k =>
      simp only [transduceTags, transduce]
      split
      · rw [updateCellsAt_tags]
        cases he : updateCellsAt cells (k-1) with
        | none => rfl
        | some p => simp [ih]
      · rfl
    | N b =>
      simp only [transduceTags, transduce]
      split
      · rw [← tags_arrivals, ← tags_append]
        have hlen : (tags cells).length = cells.length := by simp [tags]
        rw [hlen, updateCellsAt_tags]
        cases he : updateCellsAt (cells ++ arrivals v originalNext b) (cells.length+b-1) with
        | none => rfl
        | some p => simp [ih]
      · rfl

/-- Exact whole-word semantics of the label-free annotation transducer. -/
theorem transduceTags_initial_eq_encode {v n : Nat} {code : List Letter} {output : List Nat}
    (hd : Decodes n 0 [] code output) :
    transduceTags v 0 [] code = some (encode 0 [] (deleteWord v output)) := by
  rw [← show tags [] = [] from rfl]
  rw [transduce_tags]
  exact transduce_initial_eq_encode hd

/-- Rejection of the original and acceptance of every streamed single-deletion
code. This does not merge shadows or prune prefixes. -/
def shadowDeletionCheck (r s : Nat) (code : List Letter) : Bool :=
  !recognizes r s code && (List.range code.length).all (fun v =>
    match transduceTags v 0 [] code with
    | none => false
    | some shortened => recognizes r s shortened)

theorem shadowDeletionCheck_eq {r s n : Nat} {code : List Letter} {output : List Nat}
    (hd : Decodes n 0 [] code output) :
    shadowDeletionCheck r s code = oneDeletionCheck r s output := by
  have hcode := hd.encode_eq (by simp [HeldInvariant])
  simp only [shadowDeletionCheck, oneDeletionCheck, hcode, hd.length,
    transduceTags_initial_eq_encode hd]

/-- The streamed all-deletion checker has the exact ordinary one-deletion
minimality semantics of the direct recomputing oracle. -/
theorem shadowDeletionCheck_iff {r s n : Nat} {code : List Letter} {output : List Nat}
    (hd : Decodes n 0 [] code output) (hr : 0 < r) (hs : 0 < s) :
    shadowDeletionCheck r s code = true ↔
      (¬ Run r s [] (List.range n) output []) ∧
      ∀ v ∈ List.range n, Run r s [] (List.range (n-1)) (deleteWord v output) [] := by
  rw [shadowDeletionCheck_eq hd]
  apply oneDeletionCheck_iff _ hr hs
  simpa [List.range_eq_range'] using hd.supply.2

#print axioms global_retained
#print axioms global_terminal
#print axioms birth_tags
#print axioms before_birth_record
#print axioms before_birth_held
#print axioms updateCellsAt_tags
#print axioms transduce_tags
#print axioms transduceTags_initial_eq_encode
#print axioms shadowDeletionCheck_eq
#print axioms shadowDeletionCheck_iff

#print axioms global_initial
#print axioms global_arrivals
#print axioms global_update
#print axioms transduce_eq_encode
#print axioms transduce_initial_eq_encode

end Shadow
end LazyCode
end StackSorting.Generalized
