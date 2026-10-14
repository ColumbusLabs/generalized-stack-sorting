import SuppliedOuterPresentation
import CanonicalPhysicalGraphInput

namespace StackSorting.GraphWidth.GeneralConstruction
open FinitePort Generalized SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership

/-- Reflexive physical isomorphism, used only to obtain the already proved
original-incidence ownership laws. -/
def modelSelfIso (A : Model) : Isomorphism A A where
  toFun := id
  invFun := id
  to_mem _ h := h
  inv_mem _ h := h
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  insert_iff _ _ := Iff.rfl
  remove_iff _ _ := Iff.rfl
  successor_iff _ _ _ _ := Iff.rfl
  matching_iff _ _ _ _ := Iff.rfl

noncomputable def canonicalNames (output : List Nat) :
    Fin (canonicalEvents 0 output).length ≃ Vertex (canonicalDiagram output) :=
  Nested.IntroductionSyntax.timeNames _ (eventDiagram_path _)

theorem canonicalLaws {n : Nat} {output : List Nat} (hp : output.Perm (List.range n)) :
    Laws (canonicalDiagram output) := laws_of_canonical_isomorphism hp (modelSelfIso _)

/-- Incidence and the actual bounded-width graph agree on precisely the
original chronological vertices, with no orientation or adjacency oracle. -/
theorem canonicalIncidenceGraph (output : List Nat) (u v : Fin (canonicalEvents 0 output).length) :
    (sparseGraph (canonicalDiagram output) (canonicalEvents 0 output).length).Adj u v ↔
      Adjacent (canonicalDiagram output) (canonicalNames output u).val (canonicalNames output v).val := by
  constructor
  · rintro ⟨hn,he⟩
    exact ⟨(canonicalNames output u).property,(canonicalNames output v).property,
      fun h => hn (Fin.ext h),he⟩
  · rintro ⟨_,_,hn,he⟩
    exact ⟨fun h => hn (congrArg Fin.val h),he⟩

/-- The nonempty physical model now has actual outer data suitable for the
local marginal A.2 construction. Only the fixed Stack widths enter the
numerical bounds or literal outer interpretation. -/
theorem canonical_outer_presentation {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n))
    (hrun : Run r s [] (List.range n) output [])
    (hne : (canonicalDiagram output).domain ≠ []) :
    ∃ t, ∃ T : RootedTree t,
      ∃ D : Decomposition (sparseGraph (canonicalDiagram output) (canonicalEvents 0 output).length) T,
        D.BagBound (12*max r s+1) ∧
        Nonempty (OuterPresentation D (12*max r s) (canonicalNames output)
          (canonicalLaws hp) (canonicalIncidenceGraph output)) := by
  obtain ⟨t,T,D,hb⟩ := CanonicalInput.canonical_bounded_decomposition hp hrun
  refine ⟨t,T,D,hb,?_⟩
  have hn : 0 < (canonicalEvents 0 output).length := by
    by_contra h
    have hz : (canonicalEvents 0 output).length=0 := by omega
    apply hne
    change List.range (canonicalEvents 0 output).length=[]
    rw [hz]
    rfl
  exact exists_outer_presentation D (12*max r s)
    (CanonicalInput.event_sparseGraph_connected _) hn hb
    (canonicalNames output) (canonicalLaws hp) (canonicalIncidenceGraph output)

#print axioms canonical_outer_presentation
end StackSorting.GraphWidth.GeneralConstruction
