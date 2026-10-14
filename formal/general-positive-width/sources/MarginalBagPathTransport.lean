import BagPathWordAdapter

namespace StackSorting.LowPathwidthParts
open FiniteFlow.Hypergraph
variable {V W E : Type} [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Restriction and renaming along an actual injection retain the finite bag
order and cardinal bound, without introducing a scalar pathwidth oracle. -/
noncomputable def pullbackBagPath {region : Finset V} {b : Nat} (D : BagPath region b)
    (f : W → V) (inj : Function.Injective f) (inside : ∀ x, f x ∈ region) :
    BagPath (Finset.univ : Finset W) b where
  last := D.last
  bag i := Finset.univ.filter (fun x => f x ∈ D.bag i)
  inside _ _ _ _ := Finset.mem_univ _
  bounded := by
    intro i hi
    have hsub : (Finset.univ.filter (fun x => f x ∈ D.bag i)).image f ⊆ D.bag i := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ inj] at hcard
    exact hcard.trans (D.bounded i hi)
  vertex := by
    intro x _
    obtain ⟨i,hi,hx⟩ := D.vertex (f x) (inside x)
    exact ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩
  interval := by
    intro i j k hij hjk hk x hi hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,D.interval i j k hij hjk hk (f x)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hx).2⟩

/-- The exact marginal-graph join: every original or child-completion edge
must be witnessed in one actual covered hyperedge. -/
noncomputable def hyperedgeBagPathToGraphWord {region : Finset V} {b : Nat}
    (D : BagPath region b) (inc : V → E → Prop) (cover : D.Covers inc)
    (G : BiInterface.PathWord.Original W) (f : W → V) (inj : Function.Injective f)
    (inside : ∀ x, f x ∈ region)
    (edge : ∀ {x y}, G.Adj x y → ∃ e, inc (f x) e ∧ inc (f y) e) : BiInterface.PathWord.Decomposition G b :=
  bagPathToPathWord (pullbackBagPath D f inj inside) G (by
    intro x y hxy
    obtain ⟨e,hx,hy⟩ := edge hxy
    obtain ⟨i,hi,he⟩ := cover e
    exact ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he (f x) (inside x) hx⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he (f y) (inside y) hy⟩⟩)

end StackSorting.LowPathwidthParts
