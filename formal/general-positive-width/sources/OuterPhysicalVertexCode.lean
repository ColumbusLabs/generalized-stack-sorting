import MultiMarginEndpoint

/-!
The constructed C.2 realization has a fixed physical original-vertex tag.
This strengthens the existence interface with actual code preservation;
an arbitrary realizing bijection is not chosen or assumed.
-/
namespace StackSorting.GraphWidth.MultiMargin.ActualC2
open FinitePort Nested
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership CapturedLinkExtraction
open CapturedLinkExtraction.MultiMargin
open Parametric
variable {A : Model} {n t k : Nat} {G : Graph n} {T : RootedTree t}

/-- The original incidence channel followed by its actual vertex channel. -/
noncomputable def completionVertexTag (k : Nat) : Fin (CompletionIncidence.count k*3) :=
  finProdFinEquiv (CompletionIncidence.tagEquiv k (.inl ()),(0 : Fin 3))

/-- One fixed copy tag, independent of the actual graph and all witnesses. -/
noncomputable def physicalVertexTag (k : Nat) : Fin (2*(CompletionIncidence.count k*3)) :=
  finProdFinEquiv ((0 : Fin 2),completionVertexTag k)

variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (C : Colors A k) (hc : C.Valid) (hcap : Captured D names C)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)

/-- Completion retains each original vertex at its exact original number. -/
theorem completion_vertex_rep (v : Fin n) :
    (projectedRealization D names C hc hcap hA).rep
      (completionVertexTag k,(names v).val) (.inl (.inl (names v))) := by
  change outerTag (completionVertexTag k) = CompletionIncidence.tagEquiv k (.inl ()) ∧
    Represents A (innerTag (completionVertexTag k)) (names v).val (.inl (names v))
  simp [completionVertexTag,outerTag,innerTag,Represents]

/-- C.2's retained-original channel composes this exact code through the
actual outer-node realization, without a numerical naming convention. -/
theorem realization_physical_vertex (s : Sane D) (ht : 0<t) (v : Fin n) :
    (realization D names C hc hcap hA hG s ht).rep
      (physicalVertexTag k,(names v).val) (.inl (.inl (names v))) := by
  change outerTag (physicalVertexTag k) = 0 ∧
    (projectedRealization D names C hc hcap hA).rep
      (innerTag (physicalVertexTag k),(names v).val) (.inl (.inl (names v)))
  constructor
  · simp only [physicalVertexTag,outerTag,Equiv.symm_apply_apply]
  · simpa only [physicalVertexTag,innerTag,Equiv.symm_apply_apply] using
      completion_vertex_rep D names C hc hcap hA v

/-- The fixed tag does not permit a second original vertex name to denote
the same output vertex. This is an exact pointwise equality consequence. -/
theorem realization_physical_vertex_iff (s : Sane D) (ht : 0<t) (u v : Fin n) :
    (realization D names C hc hcap hA hG s ht).rep
      (physicalVertexTag k,(names u).val) (.inl (.inl (names v))) ↔ u=v := by
  constructor
  · intro h
    have he := ((realization D names C hc hcap hA hG s ht).equal _ _ _ _
      (realization_physical_vertex D names C hc hcap hA hG s ht u) h).mp rfl
    exact names.injective (Sum.inl.inj (Sum.inl.inj he))
  · rintro rfl
    exact realization_physical_vertex D names C hc hcap hA hG s ht u

include C hc hcap in
/-- The supported outer witness is chosen with its proved physical code,
rather than obtaining an arbitrary realization from a bare existence result. -/
theorem exists_supported_physical_realization (s : Sane D) (ht : 0<t) :
    ∃ params : Fin ((0+parameterCount k*3)+4*(CompletionIncidence.count k*3)) → Nat → Prop,
      CanonicalChoice.SupportedTuple A params ∧
      ∃ R : Parametric.Realization (interpretation k) A params
        (IncidenceOwnership.Element A ⊕ Fin t) (retained D names hA hG).outputAtoms,
        ∀ v, R.rep (physicalVertexTag k,(names v).val) (.inl (.inl (names v))) := by
  let R := projectedRealization D names C hc hcap hA
  let X := (completed D names hA hG).parameters s ht
  refine ⟨Parametric.flattenedSets (CompletionIncidence.params D names C hcap hA)
    (fun i => R.liftSet (X i)),?_,realization D names C hc hcap hA hG s ht,?_⟩
  · exact Parametric.flattenedSets_supported _ _ _ _
      (CompletionIncidence.params_supported D names C hcap hA)
      (fun i => R.liftSet_supported (X i))
  · exact realization_physical_vertex D names C hc hcap hA hG s ht

#print axioms exists_supported_physical_realization
#print axioms realization_physical_vertex
end StackSorting.GraphWidth.MultiMargin.ActualC2
