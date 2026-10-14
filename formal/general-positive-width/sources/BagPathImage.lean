import HypergraphBagPath

namespace FiniteFlow.Hypergraph
namespace BagPath
variable {V W : Type} [DecidableEq V] [DecidableEq W] {region : Finset V} {b : Nat}

/-- Injective renaming preserves actual ordered bags and their interval
property; arbitrary image renaming still cannot increase cardinalities. -/
def map (D : BagPath region b) (f : V → W) (inj : Function.Injective f) :
    BagPath (region.image f) b where
  last := D.last
  bag i := (D.bag i).image f
  inside := by
    intro i hi y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x,D.inside i hi hx,rfl⟩
  bounded i hi := (Finset.card_image_le).trans (D.bounded i hi)
  vertex := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i,hi,hxi⟩ := D.vertex x hx
    exact ⟨i,hi,Finset.mem_image.mpr ⟨x,hxi,rfl⟩⟩
  interval := by
    intro i j k hij hjk hk y hiy hky
    obtain ⟨x,hxi,hxy⟩ := Finset.mem_image.mp hiy
    obtain ⟨z,hzk,hzy⟩ := Finset.mem_image.mp hky
    have he : x = z := inj (hxy.trans hzy.symm)
    exact Finset.mem_image.mpr ⟨x,D.interval i j k hij hjk hk x hxi (he.symm ▸ hzk),hxy⟩

omit [DecidableEq V] in
@[simp] theorem mem_map_bag (D : BagPath region b) (f : V → W) (inj : Function.Injective f)
    (i : Nat) (x : V) : f x ∈ (D.map f inj).bag i ↔ x ∈ D.bag i := by
  exact Finset.mem_image.trans ⟨fun ⟨y,hy,he⟩ => inj he ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩

end BagPath
end FiniteFlow.Hypergraph
