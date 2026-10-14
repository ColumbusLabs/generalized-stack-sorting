import AllColumnLocality

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

/-- The concrete occurrence selected by an ordinary bounded list index. -/
def occurrenceAt : (ps : List (Packed k)) → (i : Fin ps.length) → Occurrence (ps.get i) ps
  | [], i => Fin.elim0 i
  | _P :: ps, i => Fin.cases (Occurrence.head ps)
      (fun j => Occurrence.tail (occurrenceAt ps j)) i

@[simp] theorem occurrenceAt_index (ps : List (Packed k)) (i : Fin ps.length) :
    (occurrenceAt ps i).index = i.val := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons P ps ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact congrArg (· + 1) (ih i)

/-- The actual global vertex bearing a selected side/name in a selected
column, if that port exists. This retains partial interface presence. -/
noncomputable def globalPort (ps : List (Packed k)) (i : Fin ps.length) (p : Port k) :
    Option (Packed.eval ps).Vertex :=
  ((ps.get i).graph.port p).map (occurrenceAt ps i).column

/-- Slot-preserving presence, reflected using injectivity of the real column. -/
theorem globalPort_eq_some (ps : List (Packed k)) (i : Fin ps.length) (p : Port k)
    (v : (ps.get i).Vertex) :
    globalPort ps i p = some ((occurrenceAt ps i).column v) ↔ (ps.get i).graph.port p = some v := by
  rw [globalPort,Option.map_eq_some_iff]
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Occurrence.column_injective _ he) ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

@[simp] theorem globalPort_eq_none (ps : List (Packed k)) (i : Fin ps.length) (p : Port k) :
    globalPort ps i p = none ↔ (ps.get i).graph.port p = none :=
  Option.map_eq_none_iff

@[simp] theorem globalPort_left (ps : List (Packed k)) (i : Fin ps.length) (j : Fin k) :
    globalPort ps i (false,j) = ((ps.get i).graph.left j).map (occurrenceAt ps i).column := rfl

@[simp] theorem globalPort_right (ps : List (Packed k)) (i : Fin ps.length) (j : Fin k) :
    globalPort ps i (true,j) = ((ps.get i).graph.right j).map (occurrenceAt ps i).column := rfl

/-- Global equality of two slots in one column is exactly equality of their
original interface vertices; quotient gluing makes no within-column mergers. -/
theorem globalPort_identity (ps : List (Packed k)) (i : Fin ps.length) (p q : Port k) :
    (∃ v, globalPort ps i p = some v ∧ globalPort ps i q = some v) ↔
      ∃ w, (ps.get i).graph.port p = some w ∧ (ps.get i).graph.port q = some w := by
  constructor
  · rintro ⟨v,hp,hq⟩
    obtain ⟨w,hw,hv⟩ := Option.map_eq_some_iff.mp hp
    refine ⟨w,hw,?_⟩
    apply (globalPort_eq_some ps i q w).mp
    exact hv.symm ▸ hq
  · rintro ⟨w,hp,hq⟩
    exact ⟨(occurrenceAt ps i).column w,(globalPort_eq_some ps i p w).mpr hp,
      (globalPort_eq_some ps i q w).mpr hq⟩

theorem globalPort_window (ps : List (Packed k)) (i : Fin ps.length) (p : Port k)
    {v : (Packed.eval ps).Vertex} (hv : globalPort ps i p = some v) :
    v ∈ columnWindow ps i.val 1 := by
  obtain ⟨w,_,hw⟩ := Option.map_eq_some_iff.mp hv
  exact hw ▸ mem_columnWindow (occurrenceAt ps i) w i.val 1
    (by simp) (by simp)

/-- The numeric-index form of genuine radius-one locality. -/
theorem idempotent_indexed_locality (e : Abstract k) (he : e * e = e)
    (ps : List (Packed.{0} k)) (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (i : Fin ps.length) (x y : (ps.get i).Vertex)
    (hxy : Reach (Packed.eval ps).graph.Adj ((occurrenceAt ps i).column x)
      ((occurrenceAt ps i).column y)) :
    Through (Packed.eval ps).graph.Adj (columnWindow ps i.val 1)
      ((occurrenceAt ps i).column x) ((occurrenceAt ps i).column y) := by
  simpa only [occurrenceAt_index] using idempotent_column_locality e he ps hp
    (occurrenceAt ps i) x y hxy

/-- A globally reachable named root of this column is reachable by a real
finite walk inside its radius-one column window. -/
theorem reachable_globalPort_local (e : Abstract k) (he : e * e = e)
    (ps : List (Packed.{0} k)) (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (i : Fin ps.length) (x : (ps.get i).Vertex) (p : Port k)
    (r : (Packed.eval ps).Vertex) (hr : globalPort ps i p = some r)
    (hxr : Reach (Packed.eval ps).graph.Adj ((occurrenceAt ps i).column x) r) :
    Through (Packed.eval ps).graph.Adj (columnWindow ps i.val 1)
      ((occurrenceAt ps i).column x) r := by
  obtain ⟨y,_,hy⟩ := Option.map_eq_some_iff.mp hr
  subst r
  exact idempotent_indexed_locality e he ps hp i x y hxr

#print axioms occurrenceAt_index
#print axioms idempotent_indexed_locality
end StackSorting.BiInterface.RepeatedColumn
