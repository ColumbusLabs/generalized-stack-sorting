import HypergraphPathEmbedding

namespace FiniteFlow.Hypergraph
variable {V E : Type} {inc : V → E → Prop}
namespace Path

def changeEndpoints {s t u v : V} (p : Path inc s t) (hs : s = u) (ht : t = v) : Path inc u v := by
  subst u
  subst v
  exact p

@[simp] theorem edges_changeEndpoints {s t u v : V} (p : Path inc s t) (hs : s = u) (ht : t = v) :
    (p.changeEndpoints hs ht).walk.edges = p.walk.edges := by
  subst u
  subst v
  rfl

@[simp] theorem vertices_changeEndpoints {s t u v : V} (p : Path inc s t) (hs : s = u) (ht : t = v) :
    (p.changeEndpoints hs ht).walk.vertices = p.walk.vertices := by
  subst u
  subst v
  rfl

end Path
end FiniteFlow.Hypergraph
