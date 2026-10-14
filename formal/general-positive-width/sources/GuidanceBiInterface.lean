import GuidanceRegionalConstruction
import BiInterfaceGraph

namespace StackSorting.BiInterface

/-- Forget just the interface names; retain the actual graph and all vertices. -/
def Graph.simple {k : Nat} {V : Type*} (G : Graph k V) : SimpleGraph V where
  Adj := G.Adj
  symm := ⟨fun _ _ h => G.symm h⟩
  loopless := ⟨G.loopless⟩

@[simp] theorem Graph.simple_adj {k : Nat} {V : Type*} (G : Graph k V) (x y : V) :
    G.simple.Adj x y ↔ G.Adj x y := Iff.rfl
end StackSorting.BiInterface
