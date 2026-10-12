import GeneralizedShadowGlobal

/-! Exact all-length set-merging quotient for the deletion-shadow builder.
The recognizer table is a parameter. Original state is shared, births use its
pre-step state, and deletion IDs are erased only at the merging boundary.
No assertion about exploration pruning or a serialized automaton is made. -/
namespace StackSorting.Generalized
namespace LazyCode
namespace Shadow
namespace Merging
open List

abbrev Pair := List Nat × Nat
abbrev Indexed := Nat × Pair
abbrev Table := Nat → Letter → Option Nat

/-- Equality as sets, without importing a finite-set representation. -/
def SameMembers (xs ys : List α) : Prop := ∀ x, x ∈ xs ↔ x ∈ ys

/-- A rejected member rejects the entire collection, as in the Python loops. -/
def collect (f : α → Option β) (xs : List α) : Option (List β) :=
  if xs.all (fun x => (f x).isSome) then some (xs.filterMap f) else none

/-- Equality of failure status and, on success, equality of output sets. -/
def ResultEq (xs ys : Option (List α)) : Prop :=
  match xs, ys with
  | none, none => True
  | some xs, some ys => SameMembers xs ys
  | _, _ => False

theorem same_refl (xs : List α) : SameMembers xs xs := fun _ => Iff.rfl

theorem same_map (f : α → β) {xs ys : List α} (h : SameMembers xs ys) :
    SameMembers (xs.map f) (ys.map f) := by
  intro y
  simp only [List.mem_map]
  constructor <;> rintro ⟨x, hx, rfl⟩
  · exact ⟨x, (h x).mp hx, rfl⟩
  · exact ⟨x, (h x).mpr hx, rfl⟩

theorem same_append {xs ys us vs : List α} (h : SameMembers xs ys)
    (k : SameMembers us vs) : SameMembers (xs ++ us) (ys ++ vs) := by
  intro x
  simp only [List.mem_append, h x, k x]

theorem collect_congr (f : α → Option β) {xs ys : List α}
    (h : SameMembers xs ys) : ResultEq (collect f xs) (collect f ys) := by
  have ha : xs.all (fun x => (f x).isSome) = ys.all (fun x => (f x).isSome) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro hx y hy; exact hx y ((h y).mpr hy)
    · intro hy x hx; exact hy x ((h x).mp hx)
  unfold collect
  rw [ha]
  split
  · intro y
    simp only [List.mem_filterMap]
    constructor <;> rintro ⟨x, hx, he⟩
    · exact ⟨x, (h x).mp hx, he⟩
    · exact ⟨x, (h x).mpr hx, he⟩
  · trivial

theorem collect_map (f : α → Option β) (g : β → γ) (xs : List α) :
    (collect f xs).map (List.map g) = collect (fun x => (f x).map g) xs := by
  simp only [collect, Option.isSome_map]
  split
  · simp [List.map_filterMap]
  · rfl

theorem collect_precompose (f : β → Option γ) (g : α → β) (xs : List α) :
    collect f (xs.map g) = collect (fun x => f (g x)) xs := by
  simp [collect, List.all_map, List.filterMap_map, Function.comp_def]

/-- Duplicate copies cannot add/remove a rejection or an output. -/
theorem collect_eraseDups [BEq α] [LawfulBEq α] (f : α → Option β) (xs : List α) :
    ResultEq (collect f xs.eraseDups) (collect f xs) :=
  collect_congr f (by intro x; simp)

/-- Literal annotation update followed by the recognizer and its height assert.
`none` means the step does not complete (rejection, invalid index, or failed
height assertion). The quotient preserves all these failures. -/
def updatePair (δ : Table) (height : Nat → Nat) (index : Nat) (sh : Pair) : Option Pair := do
  let (emitted, after) ← updateAt sh.1 index
  let q ← match emitted with
    | none => some sh.2
    | some l => δ sh.2 l
  if after.count 1 = height q then some (after, q) else none

/-- Original recognizer failure is `none`; existing shadows always have a
live Nat state. `next` only names births and is not used by the Python key. -/
structure Original where
  height : Nat
  next : Nat
  q : Option Nat
  deriving DecidableEq, Repr

structure State (α : Type) where
  original : Original
  shadows : List α
  deriving DecidableEq, Repr

abbrev MergedState := State Pair
abbrev IndexedState := State Indexed

def project (st : IndexedState) : MergedState :=
  ⟨st.original, st.shadows.map Prod.snd⟩

def Equivalent (xs : MergedState) (ys : IndexedState) : Prop :=
  xs.original = ys.original ∧ SameMembers xs.shadows (ys.shadows.map Prod.snd)

/-- A step's common recipe. Births are added before selecting the current
output cell; all newborns inherit the same original PRE-step q. -/
structure Recipe where
  after : Original
  extend : Pair → Pair
  births : List Indexed
  index : Nat

def birthVector (h b d : Nat) : List Nat :=
  List.replicate h 1 ++ (List.range b).map (fun j => if j = d then 2 else 0)

def births (h start b q : Nat) : List Indexed :=
  (List.range b).map (fun d => (start+d, (birthVector h b d, q)))

/-- Local step guards: positive, in-range letters and the physical bound.
The traversal's stronger N>=2 and terminal-pruning rules are separate. -/
def recipe (δ : Table) (bound : Nat) (o : Original) : Letter → Option Recipe
  | .N b => do
      let q ← o.q
      if 0 < b ∧ o.height+b ≤ bound then
        some ⟨⟨o.height+b-1, o.next+b, δ q (.N b)⟩,
          (fun sh => (sh.1 ++ List.replicate b 0, sh.2)),
          births o.height o.next b q, o.height+b-1⟩
      else none
  | .H k =>
      if 0 < k ∧ k ≤ o.height then
        some ⟨⟨o.height-1, o.next, o.q.bind (fun q => δ q (.H k))⟩,
          id, [], k-1⟩
      else none

def extendIndexed (r : Recipe) (sh : Indexed) : Indexed := (sh.1, r.extend sh.2)

def indexedInputs (r : Recipe) (xs : List Indexed) : List Indexed :=
  xs.map (extendIndexed r) ++ r.births

def mergedInputs (r : Recipe) (xs : List Pair) : List Pair :=
  xs.map r.extend ++ r.births.map Prod.snd

def updateIndexed (f : Pair → Option Pair) (sh : Indexed) : Option Indexed :=
  (f sh.2).map (fun out => (sh.1, out))

def indexedStep (δ : Table) (height : Nat → Nat) (bound : Nat)
    (st : IndexedState) (l : Letter) : Option IndexedState := do
  let r ← recipe δ bound st.original l
  let after ← collect (updateIndexed (updatePair δ height r.index)) (indexedInputs r st.shadows)
  pure ⟨r.after, after⟩

def mergedStep (δ : Table) (height : Nat → Nat) (bound : Nat)
    (st : MergedState) (l : Letter) : Option MergedState := do
  let r ← recipe δ bound st.original l
  let after ← collect (updatePair δ height r.index) (mergedInputs r st.shadows)
  pure ⟨r.after, after.eraseDups⟩

/-- This relation compares both failure and successful quotient states. -/
def StepEq (xs : Option MergedState) (ys : Option IndexedState) : Prop :=
  match xs, ys with
  | none, none => True
  | some xs, some ys => Equivalent xs ys
  | _, _ => False

theorem indexedInputs_project (r : Recipe) (xs : List Indexed) :
    (indexedInputs r xs).map Prod.snd = mergedInputs r (xs.map Prod.snd) := by
  simp [indexedInputs, mergedInputs, extendIndexed, List.map_map, Function.comp_def]

theorem collect_indexed_project (f : Pair → Option Pair) (xs : List Indexed) :
    (collect (updateIndexed f) xs).map (List.map Prod.snd) = collect f (xs.map Prod.snd) := by
  rw [collect_map, collect_precompose]
  simp [updateIndexed, Option.map_map, Function.comp_def]

theorem mergedInputs_congr (r : Recipe) {xs : List Pair} {ys : List Indexed}
    (h : SameMembers xs (ys.map Prod.snd)) :
    SameMembers (mergedInputs r xs) ((indexedInputs r ys).map Prod.snd) := by
  rw [indexedInputs_project]
  exact same_append (same_map r.extend h) (same_refl _)

theorem step_equivalent (δ : Table) (height : Nat → Nat) (bound : Nat)
    {xs : MergedState} {ys : IndexedState} (h : Equivalent xs ys) (l : Letter) :
    StepEq (mergedStep δ height bound xs l) (indexedStep δ height bound ys l) := by
  obtain ⟨ho, hm⟩ := h
  unfold mergedStep indexedStep
  rw [ho]
  cases hr : recipe δ bound ys.original l with
  | none => trivial
  | some r =>
    have hc := collect_congr (updatePair δ height r.index) (mergedInputs_congr r hm)
    rw [← collect_indexed_project] at hc
    cases hx : collect (updatePair δ height r.index) (mergedInputs r xs.shadows) <;>
      cases hy : collect (updateIndexed (updatePair δ height r.index)) (indexedInputs r ys.shadows) <;>
      simp only [hx, hy, Option.map_none, Option.map_some, ResultEq] at hc
    · simp [hx, hy, StepEq]
    · simpa [hx, hy, StepEq, Equivalent, SameMembers] using hc

def run (step : State α → Letter → Option (State α)) :
    State α → List Letter → Option (State α)
  | st, [] => some st
  | st, l :: ls => (step st l).bind (fun next => run step next ls)

/-- Main all-length quotient theorem, with no bound on code length and no
hypothesis that the original or any deletion will be accepted. -/
theorem run_equivalent (δ : Table) (height : Nat → Nat) (bound : Nat)
    {xs : MergedState} {ys : IndexedState} (h : Equivalent xs ys) (code : List Letter) :
    StepEq (run (mergedStep δ height bound) xs code)
      (run (indexedStep δ height bound) ys code) := by
  induction code generalizing xs ys with
  | nil => exact h
  | cons l ls ih =>
    have hs := step_equivalent δ height bound h l
    simp only [run]
    cases hx : mergedStep δ height bound xs l <;>
      cases hy : indexedStep δ height bound ys l <;>
      simp only [hx, hy, StepEq] at hs
    all_goals first | contradiction | exact ih hs | trivial

def initialMerged (q : Nat) : MergedState := ⟨⟨0, 0, some q⟩, []⟩
def initialIndexed (q : Nat) : IndexedState := ⟨⟨0, 0, some q⟩, []⟩

theorem initial_run_equivalent (δ : Table) (height : Nat → Nat) (bound q : Nat)
    (code : List Letter) :
    StepEq (run (mergedStep δ height bound) (initialMerged q) code)
      (run (indexedStep δ height bound) (initialIndexed q) code) :=
  run_equivalent δ height bound ⟨rfl, same_refl []⟩ code

/-- Successful collection neither drops nor relabels an indexed copy. -/
theorem collect_indexed_ids (f : Pair → Option Pair) {xs ys : List Indexed}
    (h : collect (updateIndexed f) xs = some ys) :
    ys.map Prod.fst = xs.map Prod.fst := by
  unfold collect at h
  split at h
  next ha =>
    have he := Option.some.inj h
    rw [← he]
    clear h he
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx : (f x.2).isSome = true := by simpa [updateIndexed] using (List.all_eq_true.mp ha x (by simp))
      have ht : xs.all (fun x => (updateIndexed f x).isSome) = true := by
        exact List.all_eq_true.mpr (fun y hy => List.all_eq_true.mp ha y (by simp [hy]))
      cases hf : f x.2 with
      | none => simp [hf] at hx
      | some y => simp [updateIndexed, hf, ih ht]
  next => contradiction

theorem births_ids (h start b q : Nat) :
    (births h start b q).map Prod.fst = List.range' start b := by
  simp [births, List.map_map, Function.comp_def, List.range'_eq_map_range]

/-- Every accepted prefix keeps exactly one labelled copy for every input
value already born. No two distinct IDs are merged in this reference driver. -/
def AllBorn (st : IndexedState) : Prop :=
  st.shadows.map Prod.fst = List.range st.original.next

theorem recipe_ids (δ : Table) (bound : Nat) {o : Original} {l : Letter} {r : Recipe}
    (hr : recipe δ bound o l = some r) :
    List.range o.next ++ r.births.map Prod.fst = List.range r.after.next := by
  cases l with
  | H k =>
    simp only [recipe] at hr
    split at hr
    · cases hr; simp
    · contradiction
  | N b =>
    simp only [recipe] at hr
    cases hq : o.q <;> simp only [hq] at hr
    · contradiction
    · split at hr
      · cases hr
        rw [births_ids, List.range'_eq_map_range, ← List.range_add]
      · contradiction

theorem step_allBorn (δ : Table) (height : Nat → Nat) (bound : Nat)
    {st after : IndexedState} {l : Letter} (hb : AllBorn st)
    (hs : indexedStep δ height bound st l = some after) : AllBorn after := by
  unfold indexedStep at hs
  cases hr : recipe δ bound st.original l with
  | none => simp [hr] at hs
  | some r =>
    cases hc : collect (updateIndexed (updatePair δ height r.index)) (indexedInputs r st.shadows) with
    | none => simp [hr, hc] at hs
    | some ys =>
      simp [hr, hc] at hs
      subst after
      unfold AllBorn
      rw [collect_indexed_ids _ hc]
      simp only [indexedInputs, List.map_append, List.map_map, extendIndexed, Function.comp_def]
      change st.shadows.map Prod.fst ++ r.births.map Prod.fst = _
      rw [hb]
      exact recipe_ids δ bound hr

theorem run_allBorn (δ : Table) (height : Nat → Nat) (bound : Nat)
    {st after : IndexedState} {code : List Letter} (hb : AllBorn st)
    (hs : run (indexedStep δ height bound) st code = some after) : AllBorn after := by
  induction code generalizing st with
  | nil => cases hs; exact hb
  | cons l code ih =>
    cases ht : indexedStep δ height bound st l with
    | none => simp [run, ht] at hs
    | some next =>
      simp only [run, ht, Option.bind_some] at hs
      exact ih (step_allBorn δ height bound hb ht) hs

theorem initial_run_allBorn (δ : Table) (height : Nat → Nat) (bound q : Nat)
    {code : List Letter} {after : IndexedState}
    (hs : run (indexedStep δ height bound) (initialIndexed q) code = some after) :
    AllBorn after := run_allBorn δ height bound (st := initialIndexed q) (by rfl) hs

/-- Original metadata agrees exactly, and each merged member is precisely a
surviving labelled deletion copy, possibly shared by several deletion IDs. -/
theorem initial_success_members (δ : Table) (height : Nat → Nat) (bound q : Nat)
    {code : List Letter} {merged : MergedState}
    (hm : run (mergedStep δ height bound) (initialMerged q) code = some merged) :
    ∃ indexed, run (indexedStep δ height bound) (initialIndexed q) code = some indexed ∧
      AllBorn indexed ∧ merged.original = indexed.original ∧
      ∀ sh, sh ∈ merged.shadows ↔ ∃ v, (v, sh) ∈ indexed.shadows := by
  have he := initial_run_equivalent δ height bound q code
  cases hi : run (indexedStep δ height bound) (initialIndexed q) code with
  | none => simp [hm, hi, StepEq] at he
  | some indexed =>
    simp only [hm, hi, StepEq] at he
    refine ⟨indexed, rfl, initial_run_allBorn δ height bound q hi, he.1, ?_⟩
    intro sh
    rw [he.2 sh]
    simp only [List.mem_map]
    constructor
    · rintro ⟨⟨v, pair⟩, hp, heq⟩
      simp only at heq
      subst pair
      exact ⟨v, hp⟩
    · rintro ⟨v, hv⟩
      exact ⟨(v, sh), hv, rfl⟩

/-- The birth vector is exactly the annotation projection of the previously
certified labelled arrivals, for the deletion whose original value is start+d. -/
theorem birthVector_eq_tags (held : List Nat) (start b d : Nat) :
    tags (held.map Cell.R ++ arrivals (start+d) start b) =
      birthVector held.length b d := by
  have htags : tags (held.map Cell.R) = List.replicate held.length 1 := by
    simp only [tags, List.map_map, Function.comp_def, tag]
    exact List.map_eq_replicate_iff.mpr (fun _ _ => rfl)
  rw [tags_append, htags, tags_arrivals]
  simp [birthVector, arrivalTags, List.range'_eq_map_range, List.map_map, Function.comp_def]

/-- Every newborn receives the shared PRE-step state, even when the original
transition on the current record will become rejecting. -/
theorem births_state {h start b q v : Nat} {sh : Pair}
    (hm : (v, sh) ∈ births h start b q) : sh.2 = q := by
  obtain ⟨d, _, he⟩ := List.mem_map.mp hm
  cases he
  rfl

/-- Label erasure commutes with one complete annotation/recognizer update.
The labelled-cell update does not inspect any standardized output word. -/
theorem updatePair_tags (δ : Table) (height : Nat → Nat) (index q : Nat)
    (cells : List Cell) :
    updatePair δ height index (tags cells, q) =
      (do
        let (emitted, after) ← updateCellsAt cells index
        let q' ← match emitted with
          | none => some q
          | some l => δ q l
        if (tags after).count 1 = height q' then some (tags after, q') else none) := by
  unfold updatePair
  rw [updateCellsAt_tags]
  cases hu : updateCellsAt cells index <;> rfl

theorem initial_failure_iff (δ : Table) (height : Nat → Nat) (bound q : Nat)
    (code : List Letter) :
    run (mergedStep δ height bound) (initialMerged q) code = none ↔
      run (indexedStep δ height bound) (initialIndexed q) code = none := by
  have he := initial_run_equivalent δ height bound q code
  cases hm : run (mergedStep δ height bound) (initialMerged q) code <;>
    cases hi : run (indexedStep δ height bound) (initialIndexed q) code <;>
    simp_all [StepEq]

/-- The Python local acceptance observation depends only on shared metadata.
This does not claim its exploration pruning enumerates every relevant path. -/
def accepts (st : State α) : Bool := st.original.height == 0 && st.original.q.isNone

theorem equivalent_accepts {xs : MergedState} {ys : IndexedState}
    (h : Equivalent xs ys) : accepts xs = accepts ys := by
  simp only [accepts, h.1]

/-- Universal conditions on shadows, including final recognizer observations,
are unchanged by dropping deletion IDs and deduplicating equal pairs. -/
theorem equivalent_forall {xs : MergedState} {ys : IndexedState}
    (h : Equivalent xs ys) (P : Pair → Prop) :
    (∀ sh ∈ xs.shadows, P sh) ↔ (∀ entry ∈ ys.shadows, P entry.2) := by
  constructor
  · intro hx entry he
    exact hx entry.2 ((h.2 entry.2).mpr (List.mem_map.mpr ⟨entry, he, rfl⟩))
  · intro hy sh hs
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp ((h.2 sh).mp hs)
    exact hy entry he

end Merging
end Shadow
end LazyCode
end StackSorting.Generalized
