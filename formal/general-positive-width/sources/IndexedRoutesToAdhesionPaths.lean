import IndexedRoutingState

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
variable {n : Nat}
namespace IndexedRoutes
variable {G : Graph n} {O : RankedOrder n} {r : Fin n}
    {D : IncomingDemands G O r} {A : RootedSelection O r}
    (R : IndexedRoutes G O r D A)
noncomputable section

/-- Every original (base,target) route becomes exactly its numbered 5.10
index. The representative and support are the ones actually constructed. -/
def toAdhesionPaths (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) :
    AdhesionGuidance.Paths (A.contractedDecomposition G hall helim) where
  representative i := (A.selectedLabel i).val
  representative_mem i := A.actual_margin_representative G hall helim i
  walk i := R.outgoing (A.selectedLabel i.val.1).val (A.selectedLabel i.val.1).property i.val.2
    ((mem_regionAdhesionSet G O _ _).mpr ((A.actual_adhesion_iff G hall helim _ _).mp i.property))
  contained := by
    intro i v hv hne
    apply (A.actual_component_iff G hall helim _ _).mpr
    exact R.outgoing_inside _ _ _ _ v hv hne

def indexTag (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : AdhesionGuidance.Index (A.contractedDecomposition G hall helim)) : DemandTag n :=
  ((A.selectedLabel i.val.1).val,i.val.2)

theorem indexTag_injective (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) :
    Function.Injective (indexTag (A := A) hall helim) := by
  intro i j he
  apply Subtype.ext
  apply Prod.ext
  · apply A.selectedLabel_injective
    exact Subtype.ext (congrArg Prod.fst he)
  · exact congrArg (fun p : DemandTag n => p.2) he

/-- The numbered strict-ancestor load maps injectively into the constructed
original-tag load. Repeated target values at distinct bases remain distinct. -/
theorem adhesion_load_le (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (x : Fin (Fintype.card A.Selected)) :
    ((R.toAdhesionPaths hall helim).load x).card ≤
      (R.internalLoad (A.selectedLabel x).val).card := by
  classical
  apply Finset.card_le_card_of_injOn (indexTag (A := A) hall helim)
  · intro i hi
    obtain ⟨hancestor,hne,v,hwalk,hcomponent⟩ := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(A.selectedLabel i.val.1).property,
      (mem_regionAdhesionSet G O _ _).mpr ((A.actual_adhesion_iff G hall helim _ _).mp i.property),?_,
      v,hwalk,(A.actual_component_iff G hall helim _ _).mp hcomponent⟩
    have hc := A.selected_ancestor_cone hancestor
    apply hc.resolve_right
    intro he
    exact hne (A.selectedLabel_injective (Subtype.ext he))
  · intro i _ j _ he
    exact indexTag_injective hall helim he

theorem toAdhesionPaths_bounded (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (hR : R.Bounded k) : (R.toAdhesionPaths hall helim).Bounded k (2*k^3) := by
  classical
  constructor
  · intro x
    rw [AdhesionGuidance.Paths.based_card]
    have he : (AdhesionGuidance.adhesion (A.contractedDecomposition G hall helim) x).toFinset =
        regionAdhesionSet G O (A.selectedLabel x).val := by
      ext v
      simp only [Set.mem_toFinset,mem_regionAdhesionSet,A.actual_adhesion_iff]
    rw [he]
    exact regionAdhesion_card_le G O k width _
  · intro x
    exact (R.adhesion_load_le hall helim x).trans
      (R.bounded_load k hR _ (A.selectedLabel x).property)

end
end IndexedRoutes
end StackSorting.LowPathwidthParts
