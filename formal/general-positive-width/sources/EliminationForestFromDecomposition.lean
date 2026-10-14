import IntroductionForestOrder
import RankedForestParent

namespace StackSorting.GraphWidth
open FinitePort

noncomputable def introductionOrder {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) : SameVertexForest.RankedOrder n where
  rel := IntroductionEarlier D
  irrefl := introductionEarlier_irrefl D
  trans := introductionEarlier_trans D
  predecessors := introductionEarlier_predecessors D
  rank := introductionRank D
  increasing := introductionEarlier_rank_lt D

/-- A finite parent forest on exactly the original graph vertices. -/
noncomputable def eliminationForest {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) : SameVertexForest.Forest n := (introductionOrder D).forest

theorem eliminationForest_ancestor_iff {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v : Fin n} :
    SameVertexForest.Ancestor (eliminationForest D) u v ↔ IntroductionEarlier D u v ∨ u = v :=
  (introductionOrder D).ancestor_iff

theorem eliminationForest_covers {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v : Fin n} (h : G.Adj u v) :
    SameVertexForest.Ancestor (eliminationForest D) u v ∨
      SameVertexForest.Ancestor (eliminationForest D) v u := by
  rcases introductionEarlier_eliminates D h with h | h
  · exact Or.inl ((eliminationForest_ancestor_iff D).mpr (Or.inl h))
  · exact Or.inr ((eliminationForest_ancestor_iff D).mpr (Or.inl h))

/-- Exact frontier formula of the constructed actual parent forest. -/
def EliminationFrontier {n} (F : SameVertexForest.Forest n) (G : Graph n)
    (v u : Fin n) : Prop :=
  u = v ∨ SameVertexForest.Ancestor F u v ∧ u ≠ v ∧
    ∃ w, SameVertexForest.Ancestor F v w ∧ G.Adj u w

theorem eliminationFrontier_iff {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v u : Fin n) :
    EliminationFrontier (eliminationForest D) G v u ↔ IntroductionFrontier D v u := by
  simp only [EliminationFrontier, IntroductionFrontier, eliminationForest_ancestor_iff]
  constructor
  · rintro (h | ⟨huv, hne, w, hw, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨huv.resolve_right hne, w, hw.symm, he⟩
  · rintro (h | ⟨huv, w, hw, he⟩)
    · exact Or.inl h
    · refine Or.inr ⟨Or.inl huv, ?_, w, hw.symm, he⟩
      intro e
      subst u
      exact introductionEarlier_irrefl D v huv

noncomputable def eliminationFrontierSet {n} (F : SameVertexForest.Forest n)
    (G : Graph n) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (EliminationFrontier F G v)

theorem eliminationFrontier_bound {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {b : Nat} (hb : D.BagBound b) (v : Fin n) :
    (eliminationFrontierSet (eliminationForest D) G v).card ≤ b := by
  have he : eliminationFrontierSet (eliminationForest D) G v = introductionFrontierSet D v := by
    classical
    ext u
    simp only [eliminationFrontierSet, introductionFrontierSet, Finset.mem_filter, Finset.mem_univ,
      true_and, eliminationFrontier_iff]
  rw [he]
  exact introductionFrontier_bound D hb v

/-- The conclusion is an actual same-vertex finite parent forest, edge
elimination and the original numerical frontier bound. The input is an
actual decomposition; no definability or decomposition existence is assumed
by this theorem beyond that explicitly supplied object. -/
theorem decomposition_gives_eliminationForest {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {b : Nat} (hb : D.BagBound b) :
    ∃ F : SameVertexForest.Forest n,
      (∀ u v, G.Adj u v → SameVertexForest.Ancestor F u v ∨ SameVertexForest.Ancestor F v u) ∧
      ∀ v, (eliminationFrontierSet F G v).card ≤ b :=
  ⟨eliminationForest D, fun _ _ h => eliminationForest_covers D h, eliminationFrontier_bound D hb⟩

#print axioms eliminationForest_ancestor_iff
#print axioms decomposition_gives_eliminationForest
end StackSorting.GraphWidth
