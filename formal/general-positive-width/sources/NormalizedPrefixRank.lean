import NormalizedPrefixIncidence
import ReplacementGlobalPathwidth

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization FiniteFlow.Hypergraph
variable {n : Nat}

/-- Every actual original edge is covered by one normalized bag. This avoids
assuming k≥1 when deriving the rank of its two endpoints. -/
theorem original_edge_in_bag (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (a b : Fin n) (hab : G.Adj a b) :
    ∃ z, a ∈ regionBagSet G O z ∧ b ∈ regionBagSet G O z := by
  rcases helim hab with h | h
  · exact ⟨b,(mem_regionBagSet G O b a).mpr (Or.inr ⟨h,b,cone_refl O b,hab⟩),
      (mem_regionBagSet G O b b).mpr (Or.inl rfl)⟩
  · exact ⟨a,(mem_regionBagSet G O a a).mpr (Or.inl rfl),
      (mem_regionBagSet G O a b).mpr (Or.inr ⟨h,a,cone_refl O a,G.symm hab⟩)⟩

/-- All prefix edge ranks are derived from the supplied normalized bag bound;
frontier edges use the actual adhesion bound k. -/
theorem prefix_hyperedge_rank (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r : Fin n) (Z : Finset (Fin n)) (e : (Fin n × Fin n) ⊕ Fin n) :
    (hyperedgeVertices (PrefixHypertorsoInc G O r Z) e).card ≤ k+1 := by
  classical
  cases e with
  | inl e =>
    by_cases h : G.Adj e.1 e.2
    · obtain ⟨z,ha,hb⟩ := original_edge_in_bag G O helim e.1 e.2 h
      apply (Finset.card_le_card ?_).trans (width z)
      intro x hx
      have hx' : PrefixHypertorsoInc G O r Z x (.inl e) := (Finset.mem_filter.mp hx).2
      exact hx'.2.2.2.elim (fun he => he.symm ▸ ha) (fun he => he.symm ▸ hb)
    · have hempty : hyperedgeVertices (PrefixHypertorsoInc G O r Z) (.inl e) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact h ((Finset.mem_filter.mp hx).2.1)
      simp [hempty]
  | inr z =>
    have hsub : hyperedgeVertices (PrefixHypertorsoInc G O r Z) (.inr z) ⊆ regionAdhesionSet G O z := by
      intro x hx
      exact (mem_regionAdhesionSet G O z x).mpr (Finset.mem_filter.mp hx).2.2
    exact ((Finset.card_le_card hsub).trans (regionAdhesion_card_le G O k width z)).trans (Nat.le_succ k)

end StackSorting.PrefixGrowth
