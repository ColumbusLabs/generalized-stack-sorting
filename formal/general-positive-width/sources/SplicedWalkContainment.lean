import SplicedDemandWalks

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}
namespace ChildRoutingSolutions
variable {G : Graph n} {O : RankedOrder n} {r : Fin n} {D : IncomingDemands G O r}
    {k : Nat} {Z : Finset (Fin n)} {hp : RelativePrefix O r Z}
    {F : PrefixRoutingFamily G O r D Z} (C : ChildRoutingSolutions G O r D k Z hp F)

theorem initial_vertices_visible (hp : RelativePrefix O r Z) (c : InitialDemand D) :
    ∀ x ∈ (c.path F).walk.vertices, x ∈ prefixVertices G O r Z := by
  classical
  apply (c.path F).walk.vertices_supported
  · intro x e he
    exact prefixHypertorso_support G O r Z hp x e.val he.1
  · cases c with
    | inl i => exact Finset.mem_union_right _ ((mem_regionAdhesionSet G O r _).mpr (D.endpoints i.val i.property).1)
    | inr v => exact Finset.mem_union_left _ hp.2.1

theorem spliced_inside (c : InitialDemand D) (x : Fin n)
    (hx : x ∈ (C.splicedWalk c).support) (hs : x ≠ c.source) (ht : x ≠ c.target) :
    Cone O r x := by
  classical
  rcases C.spliced_support c x hx with hx | ⟨z,hz,hzx,_⟩
  · have hv := initial_vertices_visible (F := F) hp c x hx
    rcases Finset.mem_union.mp hv with hxZ | hxA
    · exact hp.2.2 x hxZ
    · have ha := c.allowed F x hx
      exact (ha.elim (fun h => h ((mem_regionAdhesionSet G O r x).mp hxA))
        (fun h => h.elim hs ht)).elim
  · exact cone_trans O (Or.inl (relative_frontier_cone O r Z hp z hz).1) hzx

theorem spliced_hits_child (c : InitialDemand D) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) (x : Fin n)
    (hx : x ∈ (C.splicedWalk c).support) (hzx : Cone O z x) :
    C.childSupport z hz c.tag x := by
  apply spliced_support_child G O r Z hp C.childSupport c.tag z hz _ hzx
  rcases C.spliced_support c x hx with hv | hh
  · exact Or.inl (initial_vertices_visible (F := F) hp c x hv)
  · exact Or.inr hh

end ChildRoutingSolutions
end StackSorting.LowPathwidthParts
