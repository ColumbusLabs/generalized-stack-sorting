import NormalizedPrefixSeparation

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {inc : V → E → Prop} {inc' : V → F → Prop} {s t : V}

/-- Collapsing parallel original-edge copies cannot create a shared boundary
edge when the forgetting map is injective on every nonoriginal fiber. Actual
paths are recovered by loop erasure, so no output path is assumed. -/
theorem forget_original_copies (f : E → F)
    (forward : ∀ x e, inc x e → inc' x (f e))
    (original : E → Prop) (original' : F → Prop)
    (preserves : ∀ e, original e → original' (f e))
    (boundary_fiber : ∀ e d, f e = f d → ¬ original' (f e) → e = d)
    (p q : Path inc s t)
    (shared : ∀ e, e ∈ p.walk.edges → e ∈ q.walk.edges → original e) :
    ∃ a b : Path inc' s t,
      ∀ e, e ∈ a.walk.edges → e ∈ b.walk.edges → original' e := by
  obtain ⟨a,ha⟩ := (p.walk.mapEdges f forward).exists_path
  obtain ⟨b,hb⟩ := (q.walk.mapEdges f forward).exists_path
  refine ⟨a,b,?_⟩
  intro e he hf
  by_contra hn
  have hpa := ha e he
  have hqb := hb e hf
  rw [HWalk.edges_mapEdges] at hpa hqb
  obtain ⟨u,hu,hue⟩ := List.mem_map.mp hpa
  obtain ⟨v,hv,hve⟩ := List.mem_map.mp hqb
  have huv : u = v := boundary_fiber u v (hue.trans hve.symm) (hue.symm ▸ hn)
  exact hn (hue ▸ preserves u (shared u hu (huv.symm ▸ hv)))

/-- A full-edge bag covers a quotient edge whenever all its original copies
have the same incident vertices. Thus opposite orientations can be forgotten
without any bag enlargement. -/
theorem covers_original_quotient [DecidableEq V] {P : Finset V} {b : Nat}
    (D : BagPath P b) (hD : D.Covers inc) (f : E → F)
    (surj : Function.Surjective f)
    (incidence : ∀ x e, inc' x (f e) ↔ inc x e) : D.Covers inc' := by
  intro e
  obtain ⟨a,rfl⟩ := surj e
  obtain ⟨i,hi,hcover⟩ := hD a
  exact ⟨i,hi,fun x hx he => hcover x hx ((incidence x a).mp he)⟩

end FiniteFlow.Hypergraph
