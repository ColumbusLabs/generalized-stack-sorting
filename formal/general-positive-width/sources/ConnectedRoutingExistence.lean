import SubtreeRoutingExistence
import ConnectedRootSpecialization
import IndexedRoutesToAdhesionPaths
import ActualMarginalPathFamily

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
variable {n : Nat}

/-- The top-level pending family is literally empty, with no external origins. -/
def emptyIncoming (G : Graph n) (O : RankedOrder n) (r : Fin n) : IncomingDemands G O r where
  indices := ∅
  source := fun _ => r
  target := fun _ => r
  endpoints := by simp
  above := by simp

/-- Connected, nonempty graphs admit an actual covering selected-root solution.
The bounded old bags and connected cone walks are still explicit inputs and
are supplied by the accepted normalization of a genuine tree decomposition. -/
theorem exists_connected_routing (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (connected : ∀ u v, GraphWidth.Walk G.Adj (fun _ => True) u v)
    (hn : 0 < n) (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1) :
    ∃ r, (∀ v, Cone O r v) ∧ Nonempty (SubtreeRoutingSolution G O r (emptyIncoming G O r) k) := by
  obtain ⟨r,_hr,hall⟩ := exists_covering_root G O helim connected hn
  exact ⟨r,hall,exists_subtree_routing_solution G O helim cones k width r
    (emptyIncoming G O r) (by simp [emptyIncoming])⟩

/-- The constructed solution simultaneously supplies the two exact downstream
interfaces: actual original-edge adhesion paths with indexed load, and finite
ordered bags for every completed introduction-fiber marginal. -/
theorem solution_downstream {G : Graph n} {O : RankedOrder n} {r : Fin n} {k : Nat}
    (S : SubtreeRoutingSolution G O r (emptyIncoming G O r) k)
    (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (width : ∀ z, (regionBagSet G O z).card ≤ k+1) :
    (∃ P : AdhesionGuidance.Paths (S.selected.contractedDecomposition G hall helim),
      P.Bounded k (2*k^3)) ∧
    Nonempty (MarginalA2.Local.PathFamily (S.selected.contractedDecomposition G hall helim) k) := by
  exact ⟨⟨S.routes.toAdhesionPaths hall helim,
    S.routes.toAdhesionPaths_bounded hall helim k width S.bounded⟩,
    ⟨S.selected.actualPathFamily G hall helim k S.parts⟩⟩

end StackSorting.LowPathwidthParts
