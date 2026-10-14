import ColumnGeometry
import ColumnCoverage
import ColumnRegionalGuidance
import ColumnCaptureCombination

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord GuidedPathwidth
variable {k : Nat}

namespace Occurrence
/-- The canonical finite index retains the exact heterogeneous factor and
its actual occurrence, including repetitions of equal letters. -/
theorem indexed {P : Packed k} {ps : List (Packed k)} (h : Occurrence P ps) :
    ∃ i : Fin ps.length, ∃ _e : P = ps.get i, HEq h (occurrenceAt ps i) := by
  induction h with
  | head ps => exact ⟨⟨0,by simp⟩,rfl,HEq.rfl⟩
  | @tail Q ps h ih =>
    obtain ⟨i,e,he⟩ := ih
    cases e
    have hh := eq_of_heq he
    subst h
    exact ⟨i.succ,rfl,HEq.rfl⟩
end Occurrence

noncomputable def wordColumnGeometry (ps : List (Packed.{0} k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) :
    ColumnGeometry (Packed.eval ps).graph.simple ps.length where
  part := fun i => Set.range (occurrenceAt ps i).column
  boundary := fun i => columnBoundary (occurrenceAt ps i)
  boundaryInside := by rintro i v ⟨x,_,rfl⟩; exact ⟨x,rfl⟩
  vertexCovered := by
    intro v
    obtain ⟨P,h,x,hx⟩ := eval_vertex_covered ps v
    obtain ⟨i,e,he⟩ := h.indexed
    cases e
    have hh := eq_of_heq he
    subst h
    exact ⟨i,x,hx⟩
  edgeCovered := by
    intro v w hvw
    obtain ⟨P,h,x,y,_,hx,hy⟩ := eval_edge_covered ps hvw
    obtain ⟨i,e,he⟩ := h.indexed
    cases e
    have hh := eq_of_heq he
    subst h
    exact ⟨i,⟨x,hx⟩,⟨y,hy⟩⟩
  interiorUnique := by
    rintro i j v ⟨⟨x,hx⟩,hn⟩ ⟨y,hy⟩
    by_contra hij
    have hi : (occurrenceAt ps i).index ≠ (occurrenceAt ps j).index := by
      simpa only [occurrenceAt_index] using (fun h => hij (Fin.ext h))
    have hb := (column_overlap_boundary (occurrenceAt ps i) (occurrenceAt ps j) hi
      x y (hx.trans hy.symm)).1
    exact hn ⟨x,hb,hx⟩
  overlapConsecutive := by
    rintro i j v ⟨x,hx⟩ ⟨y,hy⟩
    simpa only [occurrenceAt_index] using column_overlap_indices
      (occurrenceAt ps i) (occurrenceAt ps j) hd x y (hx.trans hy.symm)

theorem wordColumnGeometry_interior (ps : List (Packed.{0} k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) (i : Fin ps.length) :
    (wordColumnGeometry ps hd).interior i = columnInterior (occurrenceAt ps i) := by
  ext v
  constructor
  · rintro ⟨⟨x,hx⟩,hn⟩
    exact ⟨x,fun hb => hn ⟨x,hb,hx⟩,hx⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x,rfl⟩,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx ((Occurrence.column_injective _ he) ▸ hy)

/-- The concrete8k regional system satisfies every named-column root route
needed by the actual decomposition graft construction. -/
theorem columnGuides_routes (e : Abstract k) (he : e*e=e)
    (ps : List (Packed.{0} k)) (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) :
    (wordColumnGeometry ps hd).Routes (columnGuides ps hd) := by
  rintro i v ⟨x,rfl⟩ r ⟨y,hy,rfl⟩ hvr
  obtain ⟨p,hpY⟩ := hy
  exact columnGuides_route e he ps hp hd i x p ((occurrenceAt ps i).column y)
    ((globalPort_eq_some ps i p y).mpr hpY) hvr.2.2
end StackSorting.BiInterface.RepeatedColumn
