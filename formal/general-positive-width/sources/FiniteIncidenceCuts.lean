import DualCotreeConnectivity
import RotationCut

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

/-- The no-leaf boundary condition follows from an actual finite injective
rotation preserving vertices and the ordinary face/rotation identity. -/
theorem incidence_cut_continues {α V F n} (I : IncidenceMap α V F) (C : FiniteCode α n)
    (rot : α → α) (hr : Function.Injective rot) (ht : ∀ d, I.tail (rot d)=I.tail d)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d)) : CutContinues I := by
  intro color d hd
  have hx : color (I.face d)≠color (I.face (rot d)) := by
    simpa only [hf,FaceCut] using hd
  obtain ⟨e,he,het,_,hc⟩ := rotation_cut_has_second_crossing_same_tail C rot hr I.tail ht
    (fun d => color (I.face d)) d hx
  refine ⟨e,het,he,?_⟩
  simpa only [hf,FaceCut] using hc

def MapGenerators {α V F} (I : IncidenceMap α V F) (rot : α → α) (a b : α) : Prop :=
  OrbitStep rot a b ∨ OrbitStep I.reverse a b

theorem fullDual_of_generators {α V F} (I : IncidenceMap α V F) (rot : α → α)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d)) {a b}
    (h : MapGenerators I rot a b) : FullDualAdj I (I.face a) (I.face b) := by
  obtain (h | h) | (h | h) := h
  · rw [← h]
    exact ⟨a,rfl,(hf a).symm⟩
  · rw [← h]
    exact fullDualAdj_symm I ⟨b,rfl,(hf b).symm⟩
  · rw [← h]
    exact ⟨a,rfl,rfl⟩
  · rw [← h]
    exact fullDualAdj_symm I ⟨b,rfl,rfl⟩

/-- Ordinary primal map connectivity also supplies actual full dual
connectivity; it is not a separate plane-map certificate. -/
theorem fullDual_connected_of_map {α V F} (I : IncidenceMap α V F) (rot : α → α)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d))
    (hs : ∀ f, ∃ d, I.face d=f)
    (hc : ∀ d e, Walk (MapGenerators I rot) (fun _ => True) d e) :
    ∀ a b, Walk (FullDualAdj I) (fun _ => True) a b := by
  intro a b
  obtain ⟨d,rfl⟩ := hs a
  obtain ⟨e,rfl⟩ := hs b
  exact walk_map I.face (fun h => fullDual_of_generators I rot hf h) (hc d e)

end StackSorting.GraphWidth.UCurve.PlaneGrid
