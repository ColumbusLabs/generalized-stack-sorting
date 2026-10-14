import InheritedBranchLabels
import SubdivisionRelabel

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

noncomputable def spanningCode {m} {H : Graph m} {root : Fin m}
    {P : PrescribedPrefix H.Adj root} (E : PreservingSpanningTree P) : FiniteCode (Fin m) m :=
  ⟨E.spanning.index,E.spanning.label,E.spanning.label_index,E.spanning.index_label⟩

/-- Actual source-branch connected lift after the parent-preserving full-graph
extension. Old edge witnesses and old fibers are retained literally. -/
noncomputable def inheritedBranchLift {m n} (H : Graph m) (G : Graph n) {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n)
    (hcover : ∀ v, ∃ i, old i=v)
    (hedge : ∀ {u v}, G.Adj u v → ∃ i j, H.Adj P.vertices[i.val] P.vertices[j.val] ∧ old i=u ∧ old j=v)
    (hfiber : ∀ i j, old i=old j → Walk (TreeAdj P.tree) (fun z => old z=old i) i j) :
    ConnectedLift (reindexGraph H (spanningCode E)) G where
  labels := fun i => [inheritedBranch P E old i]
  vertex := by
    intro v
    obtain ⟨i,hi⟩ := hcover v
    refine ⟨P.embed i,?_⟩
    simp only [List.mem_singleton,inheritedBranch_old,hi]
  edge := by
    intro u v huv
    obtain ⟨i,j,hij,hi,hj⟩ := hedge huv
    apply Or.inr
    refine ⟨P.embed i,P.embed j,?_,?_,?_⟩
    · change H.Adj (E.spanning.label (P.embed i)) (E.spanning.label (P.embed j))
      rw [E.labels,E.labels]
      exact hij
    · simp only [List.mem_singleton,inheritedBranch_old,hi]
    · simp only [List.mem_singleton,inheritedBranch_old,hj]
  fiber := by
    intro v i j hi hj
    simp only [List.mem_singleton] at hi hj
    have hab : inheritedBranch P E old i=inheritedBranch P E old j := hi.symm.trans hj
    have w := inheritedBranch_fiber P E old hfiber hab
    have mapped := walk_map_predicate (adj' := (reindexGraph H (spanningCode E)).Adj)
      (Q := fun z => v ∈ [inheritedBranch P E old z]) id (fun h => E.spanning.edge H.symm h)
      (fun z hz => by simp only [List.mem_singleton]; exact hi.trans hz.symm) w
    exact mapped

end StackSorting.GraphWidth.UCurve.SubdivisionTree
