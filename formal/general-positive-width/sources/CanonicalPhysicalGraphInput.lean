import ActualSourceWidthBoundary
import PhysicalNormalCodec
import RepresentedDecompositionAdmissibility

namespace StackSorting.GraphWidth.CanonicalInput
open FinitePort Generalized SparseEndpointMSO
open SparseEndpointMSO.EliminationSyntax SparseEndpointMSO.CanonicalChoice

/-- The actual chronological event incidence cannot create a sparse loop,
including matching edges, whose two event constructors are disjoint. -/
theorem event_modelAdjacent_irrefl (events : List EndpointEvent) (x : Nat) :
    ¬ ModelAdjacent (eventDiagram events) x x := by
  intro h
  rcases h with h | h | h | h
  · have he := h.2.2
    omega
  · have he := h.2.2
    omega
  · rcases h with ⟨v,h | h⟩ <;> have he := h.1.symm.trans h.2 <;> cases he
  · rcases h with ⟨v,h | h⟩ <;> have he := h.1.symm.trans h.2 <;> cases he

/-- Exact raw original S/M adjacency. The explicit loopless guard in
sparseGraph loses no actual event edge. -/
theorem event_sparseGraph_exact (events : List EndpointEvent)
    (u v : Fin events.length) :
    (sparseGraph (eventDiagram events) events.length).Adj u v ↔
      ModelAdjacent (eventDiagram events) u.val v.val := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    intro he
    subst v
    exact event_modelAdjacent_irrefl events u.val h

/-- Actual successor paths connect every pair of event vertices. The graph
uses original finite time indices; no arbitrary name ordering is assumed. -/
theorem event_sparseGraph_connected (events : List EndpointEvent) :
    ∀ u v, GraphWidth.Walk (sparseGraph (eventDiagram events) events.length).Adj
      (fun _ => True) u v := by
  let M := eventDiagram events
  let G := sparseGraph M events.length
  let e := Nested.IntroductionSyntax.timeNames M (eventDiagram_path events)
  have hg : ∀ u v, G.Adj u v ↔ ModelAdjacent M (e u).val (e v).val :=
    event_sparseGraph_exact events
  intro u v
  have hu : u.val ∈ M.domain := List.mem_range.mpr u.isLt
  have hv : v.val ∈ M.domain := List.mem_range.mpr v.isLt
  have lift {a b : Fin events.length} (ha : a.val ∈ M.domain) (hb : b.val ∈ M.domain)
      (w : SparseEndpointMSO.Walk M a.val b.val) :
      GraphWidth.Walk G.Adj (fun _ => True) a b := by
    have h := named_successor_walk e G hg ha hb w
    have he (z : Fin events.length) (hz : z.val ∈ M.domain) :
        e.symm ⟨z.val,hz⟩=z := by
      apply Fin.ext
      rfl
    rw [he a ha,he b hb] at h
    exact h
  rcases Nat.le_total u.val v.val with h | h
  · exact lift hu hv ((walk_iff_le M events.length (eventDiagram_path events) hu hv).mpr h)
  · exact (lift hv hu ((walk_iff_le M events.length (eventDiagram_path events) hv hu).mpr h)).reverse G.symm

/-- The accepted geometric theorem supplies a real canonical-time graph
decomposition at a width-only bound. One unit of harmless bag-bound slack
keeps the interface total at width zero without any count assertion there. -/
theorem canonical_bounded_decomposition {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hrun : Run r s [] (List.range n) output []) :
    ∃ t, ∃ T : RootedTree t,
      ∃ D : Decomposition (sparseGraph (canonicalDiagram output)
        (canonicalEvents 0 output).length) T,
        D.BagBound (12*max r s+1) := by
  obtain ⟨t,T,D,hb⟩ := UCurve.generated_sparse_treewidth_all hp hrun
  refine ⟨t,T,D,?_⟩
  intro i
  have h := hb i
  omega

#print axioms event_modelAdjacent_irrefl
#print axioms event_sparseGraph_exact
#print axioms event_sparseGraph_connected
#print axioms canonical_bounded_decomposition
end StackSorting.GraphWidth.CanonicalInput
