import RealizedGuidedDecomposition
import GuidanceGraphSemantics

namespace StackSorting.GuidedPathwidth.IncidenceAdapter
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership
variable {D : Model} {n : Nat} {G : SimpleGraph (Fin n)} {P : Set (Fin n)}

def namedVertex (names : Fin n ≃ Vertex D) (x : Fin n) : Element D := .inl (names x)
def edgeLeft (e : Edge D) : Vertex D := ⟨e.val.1,e.property.2.1⟩
def edgeRight (e : Edge D) : Vertex D := ⟨e.val.2,e.property.2.2.1⟩
def leftName (names : Fin n ≃ Vertex D) (e : Edge D) : Fin n := names.symm (edgeLeft e)
def rightName (names : Fin n ≃ Vertex D) (e : Edge D) : Fin n := names.symm (edgeRight e)

@[simp] theorem names_left (names : Fin n ≃ Vertex D) (e : Edge D) :
    (names (leftName names e)).val = e.val.1 := by
  change (names (names.symm (edgeLeft e))).val = e.val.1
  rw [names.apply_symm_apply]
  rfl
@[simp] theorem names_right (names : Fin n ≃ Vertex D) (e : Edge D) :
    (names (rightName names e)).val = e.val.2 := by
  change (names (names.symm (edgeRight e))).val = e.val.2
  rw [names.apply_symm_apply]
  rfl

theorem incident_named_iff (names : Fin n ≃ Vertex D) (x : Fin n) (e : Edge D) :
    Incident (names x) e ↔ x = leftName names e ∨ x = rightName names e := by
  constructor
  · intro h
    rcases h with h | h
    · left
      apply names.injective
      apply Subtype.ext
      simpa using h
    · right
      apply names.injective
      apply Subtype.ext
      simpa using h
  · rintro (rfl | rfl)
    · exact Or.inl (names_left names e)
    · exact Or.inr (names_right names e)

/-- Select actual incidence vertices, edges and roots from an original-edge
rooted forest. Edges are existing owned incidence elements, never new pairs. -/
def colorData (names : Fin n ≃ Vertex D) (C : RootedColor G P) :
    SparseEndpointMSO.Guidance.ColorData D where
  vertices := fun a => match a with
    | .inl v => names.symm v ∈ C.selected
    | .inr _ => False
  edges := fun a => match a with
    | .inl _ => False
    | .inr e => C.graph.Adj (leftName names e) (rightName names e)
  roots := fun a => match a with
    | .inl v => names.symm v ∈ C.roots
    | .inr _ => False

@[simp] theorem color_vertices_named (names : Fin n ≃ Vertex D) (C : RootedColor G P)
    (x : Fin n) : (colorData names C).vertices (namedVertex names x) ↔ x ∈ C.selected := by
  simp [colorData,namedVertex]
@[simp] theorem color_roots_named (names : Fin n ≃ Vertex D) (C : RootedColor G P)
    (x : Fin n) : (colorData names C).roots (namedVertex names x) ↔ x ∈ C.roots := by
  simp [colorData,namedVertex]

theorem color_typed (names : Fin n ≃ Vertex D) (C : RootedColor G P) :
    SparseEndpointMSO.Guidance.Typed (colorData names C).vertices
      (colorData names C).edges (colorData names C).roots := by
  constructor
  · intro a ha
    cases a with
    | inl v => trivial
    | inr e => exact ha.elim
  · intro a ha
    cases a with
    | inl v => exact ha.elim
    | inr e => trivial
  · intro a ha
    cases a with
    | inl v => exact C.rootSelected ha
    | inr e => exact ha.elim
  · intro e a he ha
    cases e with
    | inl v => exact he.elim
    | inr e =>
      cases a with
      | inr f => exact ha.elim
      | inl v =>
        have hi : Incident (names (names.symm v)) e := by
          rw [names.apply_symm_apply]
          simpa only [ElementIncident] using ha
        rcases (incident_named_iff names (names.symm v) e).mp hi with h | h
        · change names.symm v ∈ C.selected
          rw [h]
          exact (C.edgeSelected he).1
        · change names.symm v ∈ C.selected
          rw [h]
          exact (C.edgeSelected he).2

end StackSorting.GuidedPathwidth.IncidenceAdapter
