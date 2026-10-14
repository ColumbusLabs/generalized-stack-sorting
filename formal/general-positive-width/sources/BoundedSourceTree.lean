import ShortestPredecessor
import RootPathBags

/-! An unlabeled apex joins every anchor. Actual anchor-to-vertex counted
walks construct a shortest predecessor tree whose source ancestor list has
at most k entries. The graph may be disconnected before adding the apex. -/
namespace StackSorting.GraphWidth
open FinitePort UCurve UCurve.PlaneGrid

namespace SourceApex

/-- The apex is zero; source vertex v has code v.succ. -/
def decode {n} : Fin (n+1) → Option (Fin n) := Fin.cases none some

@[simp] theorem decode_zero {n} : decode (0 : Fin (n+1)) = none := rfl
@[simp] theorem decode_succ {n} (v : Fin n) : decode v.succ = some v := rfl

theorem decode_eq_some_iff {n} (i : Fin (n+1)) (v : Fin n) :
    decode i = some v ↔ i = v.succ := by
  refine Fin.cases ?_ (fun u => ?_) i
  · constructor
    · intro h; cases h
    · intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ] at hh
      omega
  · simp [decode, Fin.succ_inj]

def OptionAdj {n} (G : Graph n) (anchor : Fin n → Prop) :
    Option (Fin n) → Option (Fin n) → Prop
  | none, none => False
  | none, some v => anchor v
  | some u, none => anchor u
  | some u, some v => G.Adj u v

def graph {n} (G : Graph n) (anchor : Fin n → Prop) : Graph (n+1) where
  Adj := fun i j => OptionAdj G anchor (decode i) (decode j)
  symm := by
    intro i j hij
    have aux : ∀ a b, OptionAdj G anchor a b → OptionAdj G anchor b a := by
      intro a b h
      cases a with
      | none => cases b with
        | none => exact h
        | some v => exact h
      | some u => cases b with
        | none => exact h
        | some v => exact G.symm h
    exact aux _ _ hij
  loopless := by
    intro i hi
    have aux : ∀ a, ¬ OptionAdj G anchor a a := by
      intro a h
      cases a with
      | none => exact h
      | some v => exact G.loopless v h
    exact aux _ hi

@[simp] theorem adj_source {n} (G : Graph n) (anchor : Fin n → Prop) (u v : Fin n) :
    (graph G anchor).Adj u.succ v.succ ↔ G.Adj u v := Iff.rfl

@[simp] theorem adj_apex {n} (G : Graph n) (anchor : Fin n → Prop) (v : Fin n) :
    (graph G anchor).Adj 0 v.succ ↔ anchor v := Iff.rfl

/-- The hypotheses consist only of actual counted walks from anchors. -/
def Radius {n} (G : Graph n) (anchor : Fin n → Prop) (k : Nat) : Prop :=
  ∀ v, ∃ a length, anchor a ∧ length ≤ k-1 ∧ CountWalk G.Adj length a v

theorem reachable {n k} (G : Graph n) (anchor : Fin n → Prop) (radius : Radius G anchor k) :
    RootReachable (graph G anchor).Adj 0 where
  reachable := by
    intro i
    refine Fin.cases ?_ (fun v => ?_) i
    · exact ⟨0, .refl 0⟩
    · obtain ⟨a, length, ha, _, hw⟩ := radius v
      exact ⟨length+1, .step (b := a.succ) ha (hw.map Fin.succ (fun _ _ h => h))⟩

/-- Shortest distance includes the initial apex edge but no apex label. -/
theorem distance_bound {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (hk : 0 < k) (i : Fin (n+1)) :
    (reachable G anchor radius).distance i ≤ k := by
  refine Fin.cases ?_ (fun v => ?_) i
  · simp
  · obtain ⟨a, length, ha, hl, hw⟩ := radius v
    have h := (reachable G anchor radius).distance_le
      (CountWalk.step (b := a.succ) ha (hw.map Fin.succ (fun _ _ h => h)))
    omega

theorem anchor_distance {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) {v : Fin n} (hv : anchor v) :
    (reachable G anchor radius).distance v.succ = 1 := by
  have hle := (reachable G anchor radius).distance_le
    (CountWalk.step (a := (0 : Fin (n+1))) (b := v.succ) hv (CountWalk.refl v.succ))
  have hpos : (reachable G anchor radius).distance v.succ ≠ 0 := by
    intro h
    have he := ((reachable G anchor radius).distance_zero_iff v.succ).mp h
    have := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_zero] at this
    omega
  omega

/-- Every anchor selects the apex, because its shortest distance is one. -/
theorem anchor_predecessor {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) {v : Fin n} (hv : anchor v) :
    (reachable G anchor radius).predecessor v.succ = 0 := by
  have hn : v.succ ≠ (0 : Fin (n+1)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have hp := (reachable G anchor radius).predecessor_distance v.succ hn
  rw [anchor_distance G anchor radius hv] at hp
  exact ((reachable G anchor radius).distance_zero_iff _).mp (by omega)

/-- Actual source/apex parent edges, expressed in original source names. -/
theorem source_parent_edge {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (v : Fin n) :
    let R := reachable G anchor radius
    (R.predecessor v.succ = 0 ∧ anchor v) ∨
      ∃ u : Fin n, R.predecessor v.succ = u.succ ∧ G.Adj u v := by
  let R := reachable G anchor radius
  have hn : v.succ ≠ (0 : Fin (n+1)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have he := R.predecessor_edge v.succ hn
  have aux : ∀ p : Fin (n+1), (graph G anchor).Adj p v.succ →
      (p = 0 ∧ anchor v) ∨ ∃ u : Fin n, p = u.succ ∧ G.Adj u v := by
    intro p
    refine Fin.cases ?_ (fun u => ?_) p
    · intro h; exact Or.inl ⟨rfl, h⟩
    · intro h; exact Or.inr ⟨u, rfl, h⟩
  exact aux _ he

/-- Parent edges in the final numbered tree retain their original source names. -/
theorem numbered_source_parent_edge {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (v : Fin n) :
    let R := reachable G anchor radius
    let p := R.numbered.label (R.numbered.tree.parent (R.numbered.index v.succ))
    (p = 0 ∧ anchor v) ∨ ∃ u : Fin n, p = u.succ ∧ G.Adj u v := by
  dsimp only
  rw [(reachable G anchor radius).numbered.parent_exact,
    (reachable G anchor radius).numbered.label_index]
  exact source_parent_edge G anchor radius v

/-- Source labels along the actual numbered root path; the apex is erased. -/
noncomputable def sourcePath {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (i : Fin (n+1)) : List (Fin n) :=
  (rootPath (reachable G anchor radius).numbered.tree i).filterMap
    (fun j => decode ((reachable G anchor radius).numbered.label j))

/-- Exact count, not a depth certificate supplied by a caller. -/
theorem sourcePath_length {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (i : Fin (n+1)) :
    (sourcePath G anchor radius i).length =
      (reachable G anchor radius).distance ((reachable G anchor radius).numbered.label i) := by
  let R := reachable G anchor radius
  change ((rootPath R.numbered.tree i).filterMap (fun j => decode (R.numbered.label j))).length =
    R.distance (R.numbered.label i)
  rw [rootPath]
  split
  · rename_i hi
    have hr : R.numbered.label i = 0 := R.numbered.label_root i hi
    simp [hr]
  · rename_i hi
    have hstep := R.numbered_parent_distance i hi
    have ih := sourcePath_length G anchor radius (R.numbered.tree.parent i)
    have hn : R.numbered.label i ≠ (0 : Fin (n+1)) := by
      intro h
      exact hi ((R.numbered.label_eq_root_iff i).mp h)
    have hd : ∃ v, decode (R.numbered.label i) = some v := by
      have aux : ∀ p : Fin (n+1), p ≠ 0 → ∃ v, decode p = some v := by
        intro p
        refine Fin.cases ?_ (fun v => ?_) p
        · intro h; exact False.elim (h rfl)
        · intro _; exact ⟨v, rfl⟩
      exact aux _ hn
    obtain ⟨v, hv⟩ := hd
    simp only [List.filterMap_cons, hv, List.length_cons]
    change (sourcePath G anchor radius (R.numbered.tree.parent i)).length + 1 = _
    rw [ih]
    exact hstep
termination_by i.val
decreasing_by all_goals apply (reachable G anchor radius).numbered.tree.parent_lt; omega

theorem sourcePath_bound {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (hk : 0 < k) (i : Fin (n+1)) :
    (sourcePath G anchor radius i).length ≤ k := by
  rw [sourcePath_length]
  exact distance_bound G anchor radius hk _

/-- Membership is exactly source ancestry in the constructed numbered tree. -/
theorem mem_sourcePath {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (i : Fin (n+1)) (v : Fin n) :
    v ∈ sourcePath G anchor radius i ↔
      Ancestor (reachable G anchor radius).numbered.tree
        ((reachable G anchor radius).numbered.index v.succ) i := by
  let R := reachable G anchor radius
  simp only [sourcePath, List.mem_filterMap, mem_rootPath, decode_eq_some_iff]
  constructor
  · rintro ⟨j, hj, he⟩
    have hji : j = R.numbered.index v.succ := by rw [← he, R.numbered.index_label]
    simpa only [hji] using hj
  · intro h
    exact ⟨R.numbered.index v.succ, h, R.numbered.label_index _⟩

/-- Any duplicate-free list of source ancestors has at most k entries. -/
theorem source_ancestor_bound {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) (hk : 0 < k) (i : Fin (n+1))
    (xs : List (Fin n)) (hn : xs.Nodup)
    (ha : ∀ v ∈ xs, Ancestor (reachable G anchor radius).numbered.tree
      ((reachable G anchor radius).numbered.index v.succ) i) : xs.length ≤ k := by
  have hle := hn.length_le_of_subset (l₂ := sourcePath G anchor radius i)
    (by intro v hv; exact (mem_sourcePath G anchor radius i v).mpr (ha v hv))
  exact Nat.le_trans hle (sourcePath_bound G anchor radius hk i)

/-- The numbered tree sends every anchor directly to the unlabeled apex. -/
theorem numbered_anchor_parent {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : Radius G anchor k) {v : Fin n} (hv : anchor v) :
    let R := reachable G anchor radius
    R.numbered.tree.parent (R.numbered.index v.succ) = R.numbered.index 0 := by
  dsimp only
  rw [(reachable G anchor radius).numbered.parent_index]
  exact congrArg (reachable G anchor radius).numbered.index (anchor_predecessor G anchor radius hv)

end SourceApex
end StackSorting.GraphWidth
