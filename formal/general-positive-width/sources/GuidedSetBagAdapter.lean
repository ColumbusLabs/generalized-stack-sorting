import NamedIndexTreeAdapter
import RealizedGuidedDecomposition

/-! Actual set-bag/ReachIn guidance output to the accepted numbered-tree
normalizer. This leaf is outside the first extraction freeze and must not be
compiled against unbound guidance author objects. -/
namespace StackSorting.IndexTreeAdapter
open GraphWidth FinitePort GuidedPathwidth
variable {n c : Nat} {H : SimpleGraph (Fin n)}

def finiteGraph (H : SimpleGraph (Fin n)) : Graph n where
  Adj := H.Adj
  symm := fun h => h.symm
  loopless := fun _ h => h.ne rfl

noncomputable def setBagList (B : Set (Fin n)) : List (Fin n) := by
  classical
  exact (Finset.univ.filter (fun u => u ∈ B)).toList

@[simp] theorem mem_setBagList (B : Set (Fin n)) (u : Fin n) :
    u ∈ setBagList B ↔ u ∈ B := by
  classical
  simp [setBagList]

theorem length_setBagList (B : Set (Fin n)) : (setBagList B).length = Nat.card B := by
  classical
  simp only [setBagList,Finset.length_toList,Nat.card_eq_fintype_card,Fintype.card_subtype]

noncomputable def namedGuidedDecomposition (D : ForestGuidedDecomposition H Set.univ c) :
    NamedDecomposition (finiteGraph H) D.decomposition.forest where
  bag a := setBagList (D.decomposition.bag a)
  nodup a := by
    classical
    exact Finset.nodup_toList _
  vertex u := by
    obtain ⟨a,ha⟩ := D.decomposition.vertex u trivial
    exact ⟨a,(mem_setBagList _ _).mpr ha⟩
  edge := by
    intro u v huv
    obtain ⟨a,ha,hb⟩ := D.decomposition.edge huv trivial trivial
    exact ⟨a,(mem_setBagList _ _).mpr ha,(mem_setBagList _ _).mpr hb⟩
  running := by
    intro u a b ha hb
    have h := D.decomposition.running u a b
      ((mem_setBagList _ _).mp ha) ((mem_setBagList _ _).mp hb)
    obtain ⟨p⟩ := h.induced
    exact (induced_to_guarded p).mono (fun a ha => (mem_setBagList _ _).mpr ha)

theorem namedGuidedDecomposition_bound (D : ForestGuidedDecomposition H Set.univ c) (a) :
    ((namedGuidedDecomposition D).bag a).length ≤ c := by
  change (setBagList (D.decomposition.bag a)).length ≤ c
  rw [length_setBagList]
  exact D.bag_card_le a

theorem forestCaptures_mono (C : Fin c → RootedColor H Set.univ) {A B : Set (Fin n)}
    (h : ForestCaptures C B) (hs : A ⊆ B) : ForestCaptures C A := by
  intro ha
  obtain ⟨x,hx⟩ := h (ha.mono hs)
  exact ⟨x,fun r hr => hx r (hs hr)⟩

/-- Every normalized bag has an exact old named index-tree origin and is
captured by the same actual original-edge forest colors. -/
theorem normalized_guided_capture (D : ForestGuidedDecomposition H Set.univ c)
    (N : NamedNumberedTree D.decomposition.forest) (v) :
    ForestCaptures D.colors {u | u ∈ (ConnectedConeNormalization.normalizeSupplied
      (reindexDecomposition N (namedGuidedDecomposition D))).bag v} := by
  apply normalized_named_capture N (namedGuidedDecomposition D)
    (fun A => ForestCaptures D.colors {u | A u})
    (fun _ _ hs h => forestCaptures_mono D.colors h hs)
  intro a
  simpa only [namedGuidedDecomposition,mem_setBagList,Set.ofPred_mem_eq] using D.captured a

/-- The guidance tree output supplies the normalizer input without any
orientation, numbering, or occurrence-walk premise being assumed. -/
noncomputable def guidedNumbering (D : ForestGuidedDecomposition H Set.univ c)
    (ht : D.decomposition.forest.IsTree) : NamedNumberedTree D.decomposition.forest := by
  let : Fintype D.decomposition.Node := Fintype.ofFinite _
  exact numberNamedTree ht

/-- Adhesions are subsets of actual normalized bags, so their guidance is
inherited without assuming any parent edge or a root choice for empty sets. -/
theorem normalized_guided_adhesion_capture
    (D : ForestGuidedDecomposition H Set.univ c)
    (N : NamedNumberedTree D.decomposition.forest) (v) :
    ForestCaptures D.colors {u | ConnectedConeNormalization.RegionAdhesion
      (finiteGraph H) (ConnectedConeNormalization.normalizedOrder (finiteGraph H)
        (introductionOrder
          (reindexDecomposition N (namedGuidedDecomposition D)))) v u} := by
  apply forestCaptures_mono D.colors (normalized_guided_capture D N v)
  intro u hu
  have hb := (ConnectedConeNormalization.regionAdhesion_iff _ _ v u).mp hu
  change u ∈ eliminationFrontierSet
    (ConnectedConeNormalization.normalizedOrder (finiteGraph H)
      (introductionOrder
        (reindexDecomposition N (namedGuidedDecomposition D)))).forest
    (finiteGraph H) v
  classical
  simp only [eliminationFrontierSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (ConnectedConeNormalization.regionBag_iff_frontier _ _ v u).mp hb.1

#print axioms namedGuidedDecomposition
#print axioms normalized_guided_capture
#print axioms guidedNumbering
#print axioms normalized_guided_adhesion_capture
end StackSorting.IndexTreeAdapter
