import GenericCapturedLinks
import CapturedAdhesionWitness

namespace StackSorting.GuidedPathwidth.GenericIncidence.System
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open GraphWidth SameVertexForest ConnectedConeNormalization CapturedLinkExtraction
variable {n k : Nat} {H : SimpleGraph (Fin n)} (S : System H)

/-- Genuine incidence capture, with no sparse-model representation premise. -/
def AdhesionsCaptured (C : Fin k → S.ColorData) (G : Graph n) (O : RankedOrder n) : Prop :=
  ∀ a, (∃ u, RegionAdhesion G O a u) → ∃ z,
    ∀ u, RegionAdhesion G O a u → ∃ i, S.ColorRoot C i z (.inl u)

theorem original_incidence {u v : Fin n} (h : H.Adj u v) :
    ∃ e, S.isEdge e ∧ S.incident (.inl u) e ∧ S.incident (.inl v) e := by
  obtain ⟨e,he | he⟩ := S.complete h
  · exact ⟨.inr e,trivial,Or.inl he.1.symm,Or.inr he.2.symm⟩
  · exact ⟨.inr e,trivial,Or.inr he.2.symm,Or.inl he.1.symm⟩

/-- Actual normalized parent links are supplied by original graph edges or
by two rigid roots capturing the same real local adhesion. -/
theorem normalized_parent_available (C : Fin k → S.ColorData) (G : Graph n)
    (hG : ∀ u v, G.Adj u v ↔ H.Adj u v) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hc : S.AdhesionsCaptured C G (normalizedOrder G O)) (u v)
    (hp : ParentAdj (normalizedOrder G O) u v) : S.Available C u v := by
  have hf : FilledAdhesionsAdj G (normalizedOrder G O) u v := by
    rcases hp with ⟨hne,hp⟩ | ⟨hne,hp⟩
    · apply filledAdhesions_symm G _
      exact hp ▸ normalized_parent_adhesion_filled G O he hne
    · exact hp ▸ normalized_parent_adhesion_filled G O he hne
  rcases hf.2 with hadj | ⟨a,hu,hv⟩
  · exact Or.inl (S.original_incidence ((hG u v).mp hadj))
  · obtain ⟨z,hz⟩ := hc a ⟨u,hu⟩
    obtain ⟨i,hi⟩ := hz u hu
    obtain ⟨j,hj⟩ := hz v hv
    exact Or.inr ⟨i,j,z,hi,hj⟩

/-- Fixed generic-incidence tuple, ready for disjoint-owner merging and the
accepted parameter-dependent pullback. No assumption about global guidance. -/
theorem exists_earlier_of_captured_adhesions (C : Fin k → S.ColorData)
    (hC : ∀ i, (C i).Valid) (G : Graph n)
    (hG : ∀ u v, G.Adj u v ↔ H.Adj u v) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hc : S.AdhesionsCaptured C G (normalizedOrder G O)) :
    ∃ X : Fin (parameterCount k) → S.IncSet, ∀ u v,
      ActualEval S.atoms (capturedEarlierFormula (fixedIndices k) (0 : Fin 2) 1)
        (Fin.cases (.inl u) (fun _ => .inl v)) X ↔ (normalizedOrder G O).rel u v := by
  refine ⟨S.chosenSets C (S.forestSelection C (normalizedOrder G O)),?_⟩
  intro u v
  exact S.earlier_forest_exact C hC _ (S.normalized_parent_available C G hG O he hc) u v

#print axioms original_incidence
#print axioms normalized_parent_available
#print axioms exists_earlier_of_captured_adhesions
end StackSorting.GuidedPathwidth.GenericIncidence.System
