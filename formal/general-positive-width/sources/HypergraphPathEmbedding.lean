import PrunedPrefixIncidence

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {inc : V → E → Prop} {inc' : V → F → Prop} {s t : V}

namespace Path
/-- Relabel along an injective incidence-preserving map, keeping the exact
vertex sequence and actual simple path properties. -/
def embedEdges (f : E → F) (inj : Function.Injective f)
    (forward : ∀ x e, inc x e → inc' x (f e)) (p : Path inc s t) : Path inc' s t where
  walk := p.walk.mapEdges f forward
  vertices_nodup := by rw [HWalk.vertices_mapEdges]; exact p.vertices_nodup
  edges_nodup := by rw [HWalk.edges_mapEdges]; exact p.edges_nodup.map inj
end Path

namespace HWalk
theorem vertices_supported (P : V → Prop) (support : ∀ x e, inc x e → P x)
    {a b : V} (w : HWalk inc a b) (ha : P a) : ∀ x ∈ w.vertices, P x := by
  induction w with
  | nil a =>
    intro x hx
    have he : x = a := List.mem_singleton.mp hx
    exact he.symm ▸ ha
  | @cons a b c e hab hbc tail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · exact he.symm ▸ ha
    · exact ih (support b e hbc) x hx
end HWalk
end FiniteFlow.Hypergraph
