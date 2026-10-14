import HWalkOperations
import HypergraphTwoPaths

/-!
# Prefix invariance of unavoidable hyperedge identifiers

Splicing uses actual walks. The accepted walk/path equivalence for cutedges
justifies this without pretending that the spliced walk is simple.
-/
namespace FiniteFlow.Hypergraph

variable {V E : Type*} {inc : V → E → Prop} {s t : V}

/-- Once a cutedge has occurred before an edge `f` in an edge-simple source--sink
walk, every source-to-`f` prefix must already have used that cutedge. -/
theorem cutedge_mem_every_prefix {e f : E} (he : Cutedge inc s t e)
    (w : HWalk inc s t) (hw : w.edges.Nodup)
    {a b c : V} (pre : HWalk inc s a) (suf : HWalk inc b t)
    (hs : w.edges = pre.edges ++ f :: suf.edges) (hb : inc b f)
    (other : HWalk inc s c) (hc : inc c f)
    (hm : e ∈ pre.edges) : e ∈ other.edges := by
  have hall : (pre.edges ++ f :: suf.edges).Nodup := hs ▸ hw
  have hn : e ∉ f :: suf.edges := by
    intro h
    exact (List.pairwise_append.mp hall).2.2 e hm e h rfl
  let splice : HWalk inc s t := other.append (.cons f hc hb suf)
  have h := (cutedge_iff_every_walk inc s t e).mp he splice
  have hmem : e ∈ other.edges ++ f :: suf.edges := by
    simpa only [splice, HWalk.edges_append, HWalk.edges] using h
  exact (List.mem_append.mp hmem).resolve_right hn

/-- Prefix cutedge membership is independent of the chosen simple path and
the chosen incidence vertices at the common split edge. -/
theorem cutedge_prefix_mem_iff {e f : E} (he : Cutedge inc s t e)
    (p q : Path inc s t) {a b c d : V}
    (pp : HWalk inc s a) (ps : HWalk inc b t)
    (qp : HWalk inc s c) (qs : HWalk inc d t)
    (hp : p.walk.edges = pp.edges ++ f :: ps.edges)
    (hq : q.walk.edges = qp.edges ++ f :: qs.edges)
    (ha : inc a f) (hb : inc b f) (hc : inc c f) (hd : inc d f) :
    e ∈ pp.edges ↔ e ∈ qp.edges := by
  constructor
  · exact cutedge_mem_every_prefix he p.walk p.edges_nodup pp ps hp hb qp hc
  · exact cutedge_mem_every_prefix he q.walk q.edges_nodup qp qs hq hd pp ha

end FiniteFlow.Hypergraph
