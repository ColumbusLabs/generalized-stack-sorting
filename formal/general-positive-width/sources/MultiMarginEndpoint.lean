import MultiMarginCompletionAdapter
import MultiMarginAcyclic

namespace StackSorting.GraphWidth.MultiMargin.ActualC2
open FinitePort Nested
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership CapturedLinkExtraction CapturedLinkExtraction.MultiMargin
variable {A : Model} {n t k : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (C : Colors A k) (hc : C.Valid) (hcap : Captured D names C)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)

/- If the actual outer node domain is empty, vertex coverage forces the
original incidence domain empty as well; no representative is chosen. -/
include D names in
theorem empty_original (ht : t=0) : IsEmpty (IncidenceOwnership.Element A) := by
  have hn : ∀ u : Fin n, False := by
    intro u
    obtain ⟨x,_⟩ := D.vertex u
    have := x.isLt
    omega
  refine ⟨?_⟩
  rintro (v | e)
  · exact hn (names.symm v)
  · exact hn (names.symm ⟨e.val.1,e.property.2.1⟩)

include names in
theorem empty_completed (ht : t=0) :
    IsEmpty (CompletionIncidence.Actual (D := A) D) := by
  let := empty_original D names ht
  refine ⟨?_⟩
  rintro (v | e)
  · exact isEmptyElim v
  · obtain ⟨x,_⟩ := D.vertex e.val.1
    have := x.isLt
    omega

/- Required C.2 endpoint: a fixed literal interpretation and a supported
parameter tuple realize the exact supplied outer decomposition on its actual
original incidence elements and original nodes. This includes the empty case. -/
include C hc hcap in
theorem exists_supported_realization (s : Sane D) :
    ∃ params : Fin ((0+parameterCount k*3)+4*(CompletionIncidence.count k*3)) → Nat → Prop,
      CanonicalChoice.SupportedTuple A params ∧
      Nonempty (Parametric.Realization (interpretation k) A params
        (IncidenceOwnership.Element A ⊕ Fin t) (retained D names hA hG).outputAtoms) := by
  let R := projectedRealization D names C hc hcap hA
  have hs : CanonicalChoice.SupportedTuple A (CompletionIncidence.params D names C hcap hA) :=
    CompletionIncidence.params_supported D names C hcap hA
  by_cases ht : 0<t
  · let X := (completed D names hA hG).parameters s ht
    refine ⟨Parametric.flattenedSets (CompletionIncidence.params D names C hcap hA)
      (fun i => R.liftSet (X i)),?_,⟨(retained D names hA hG).realization s ht R⟩⟩
    exact Parametric.flattenedSets_supported _ _ _ _ hs (fun i => R.liftSet_supported (X i))
  · have hz : t=0 := by omega
    let := empty_original D names hz
    let := empty_completed D names hz
    have hi : IsEmpty (Fin t) := ⟨fun x => by have := x.isLt; omega⟩
    let := hi
    let X : Fin 4 → CompletionIncidence.Actual (D := A) D → Prop := fun _ _ => False
    let Q := R.compose Syntax.interpretation X
    let : IsEmpty (Parametric.StepElement Syntax.interpretation (Syntax.atoms (relations D names)) X) :=
      ⟨fun x => isEmptyElim x.val.2⟩
    let E : Parametric.StepElement Syntax.interpretation (Syntax.atoms (relations D names)) X ≃
        (IncidenceOwnership.Element A ⊕ Fin t) := Equiv.equivOfIsEmpty _ _
    refine ⟨Parametric.flattenedSets (CompletionIncidence.params D names C hcap hA)
      (fun i => R.liftSet (X i)),?_,?_⟩
    · exact Parametric.flattenedSets_supported _ _ _ _ hs (fun i => R.liftSet_supported (X i))
    · refine ⟨Retained.transportRealization Q E (retained D names hA hG).outputAtoms ?_⟩
      intro r atom env
      cases atom <;> exact isEmptyElim (env 0)

/- One extra output-set variable adds the fixed final number of copies.
All arities depend only on guidance colors and the formula, never on |G|. -/
theorem output_set_arity (k b : Nat) :
    ((0+parameterCount k*3)+4*(CompletionIncidence.count k*3))+b*(2*(CompletionIncidence.count k*3)) =
      ((0+parameterCount k*3)+(4+b*2)*(CompletionIncidence.count k*3)) := by
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]

#print axioms empty_original
#print axioms empty_completed
#print axioms exists_supported_realization
#print axioms output_set_arity
end StackSorting.GraphWidth.MultiMargin.ActualC2
