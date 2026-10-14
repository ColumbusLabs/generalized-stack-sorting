import RankedParentTree
import FiniteOrbitCounts

namespace StackSorting.GraphWidth
open FinitePort UCurve.PlaneGrid

/-- Transport an arbitrary finite ranked parent function into the exact
numbering constructor. The supplied code concerns only the vertex set. -/
def rankedParentFromCode {α n} (C : FiniteCode α n) (root : α)
    (parent : α → α) (rank : α → Nat) (hroot : parent root = root)
    (hlt : ∀ v, v ≠ root → rank (parent v) < rank v) : RankedParent n where
  root := C.encode root
  parent := fun i => C.encode (parent (C.decode i))
  rank := fun i => rank (C.decode i)
  parent_root := by rw [C.decode_encode, hroot]
  rank_lt := by
    intro i hi
    rw [C.decode_encode]
    apply hlt
    intro h
    apply hi
    rw [← C.encode_decode i, h]

/-- Decoding the constructed numbered tree preserves the original parent
function exactly, including at the root. -/
theorem rankedParentFromCode_parent_exact {α n} (C : FiniteCode α n) (root : α)
    (parent : α → α) (rank : α → Nat) (hroot : parent root = root)
    (hlt : ∀ v, v ≠ root → rank (parent v) < rank v) (i : Fin n) :
    let N := (rankedParentFromCode C root parent rank hroot hlt).numbered
    C.decode (N.label (N.tree.parent i)) = parent (C.decode (N.label i)) := by
  dsimp only
  rw [RankedParent.Numbered.parent_exact]
  exact C.decode_encode _

end StackSorting.GraphWidth
