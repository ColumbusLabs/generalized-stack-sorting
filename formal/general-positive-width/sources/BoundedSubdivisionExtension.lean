import InheritedSourceBound
import SubdivisionPrefix

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

/-- Expand the actual shortest source tree, attach every non-tree route tail,
and extend to the whole connected target without changing any old parent.
The resulting full tree has at most k distinct original-source labels on each
root path, irrespective of route lengths or added target vertices. -/
theorem bounded_subdivision_extension {n m k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : SourceApex.Radius G anchor k) (hk : 0<k) (H : Graph m)
    (S : Realization (SourceApex.graph G anchor) H)
    (connected : ∀ u v, Walk H.Adj (fun _ => True) u v) :
    ∃ (C : FiniteCode (Fin m) m) (T : RootedTree m) (L : ConnectedLift (reindexGraph H C) G),
      (∀ i, i.val≠0 → (reindexGraph H C).Adj (T.parent i) i) ∧
      ∀ i, (rootPathLabels T L.labels i).length≤k := by
  let R := SourceApex.reachable G anchor radius
  let C := sourceTreeCode G anchor radius
  let S' := S.reindex C
  let T := R.numbered.tree
  have he : ∀ i, i.val≠0 → (reindexGraph (SourceApex.graph G anchor) C).Adj (T.parent i) i :=
    R.numbered_parent_edge
  let r := R.numbered.index 0
  have hr : r.val=0 := R.numbered.index_root_val
  let P := S'.prefix T he r hr
  let E := preservingSpanningTree P connected
  let L0 := S'.extendedBranchLift T he r hr E
  let L := eraseApexLift G anchor (reindexGraph H (spanningCode E)) C L0
  refine ⟨spanningCode E,E.spanning.tree,L,?_,?_⟩
  · intro i hi
    exact E.spanning.parent_edge i hi
  · intro i
    exact inherited_source_root_bound G anchor radius hk P E (S'.prefixBranch T he r hr)
      (S'.prefixBranch_parent_ancestor T he r hr) i

end StackSorting.GraphWidth.UCurve.SubdivisionTree
