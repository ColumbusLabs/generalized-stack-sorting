import CutedgeBoundaryTrace

namespace FiniteFlow.Hypergraph
variable {V E : Type*} {inc : V → E → Prop} {s t : V}

/-- Consecutive canonical boundary labels occupy consecutive finite list
positions. This converts the accepted abstract classification to actual indices
usable by the bag construction. -/
theorem boundaryAdjacent_get_iff [DecidableEq E] (p : Path inc s t)
    (i j : Fin (boundaryTrace p).length) :
    BoundaryAdjacent p ((boundaryTrace p).get i) ((boundaryTrace p).get j) ↔
      i.val + 1 = j.val := by
  constructor
  · intro h
    have hij := (boundaryTrace_get_before p i j).mp h.1
    by_contra hne
    have hmid : i.val + 1 < (boundaryTrace p).length := by omega
    let m : Fin (boundaryTrace p).length := ⟨i.val+1,hmid⟩
    apply h.2
    refine ⟨(boundaryTrace p).get m,
      (mem_boundaryTrace p _).mp (List.get_mem _ m), ?_, ?_⟩
    · apply (boundaryTrace_get_before p i m).mpr
      change i.val < i.val+1
      omega
    · apply (boundaryTrace_get_before p m j).mpr
      change i.val+1 < j.val
      omega
  · intro hij
    refine ⟨(boundaryTrace_get_before p i j).mpr (by change i.val < j.val; omega), ?_⟩
    rintro ⟨b, hb, hib, hbj⟩
    obtain ⟨m, rfl⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p b).mpr hb)
    have him := (boundaryTrace_get_before p i m).mp hib
    have hmj := (boundaryTrace_get_before p m j).mp hbj
    have hi : i.val < m.val := him
    have hj : m.val < j.val := hmj
    omega

/-- Every bridge has actual consecutive list indices; no indexing witness is
assumed. Empty cutedge traces retain source and sink at consecutive positions. -/
theorem indexed_cutedge_component_classification [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (x : V) :
    (∃ e, Cutedge inc s t e ∧
      ∀ b, BoundaryValid (inc := inc) (s := s) (t := t) b →
        (ComponentTouches (inc := inc) (s := s) (t := t) x b ↔ b = .cut e)) ∨
    (∃ i j : Fin (boundaryTrace p).length, i.val + 1 = j.val ∧
      ∀ b, BoundaryValid (inc := inc) (s := s) (t := t) b →
        (ComponentTouches (inc := inc) (s := s) (t := t) x b ↔
          b = (boundaryTrace p).get i ∨ b = (boundaryTrace p).get j)) := by
  rcases cutedge_component_classification connected p x with happ | hbridge
  · exact Or.inl happ
  · obtain ⟨a,b,ha,hb,hab,hall⟩ := hbridge
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p a).mpr ha)
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p b).mpr hb)
    exact Or.inr ⟨i,j,(boundaryAdjacent_get_iff p i j).mp hab,hall⟩

end FiniteFlow.Hypergraph
