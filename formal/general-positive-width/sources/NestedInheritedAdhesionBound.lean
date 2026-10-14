import NestedFlattenedBags

namespace StackSorting.GraphWidth.Nested
open FinitePort
variable {n s t W : Nat} {G : Graph n} {S : RootedTree s} {T : RootedTree t}

/-- Exact original-bag containment bounds every actual adhesion list after
arbitrary local marginal decompositions have been assembled. Outer bags may
be unbounded; they are not used as a boundedness premise. -/
theorem inherited_adhesionList_bound (original : Decomposition G S)
    (D : Decomposition G T) (N : NestedInput D) (hb : original.BagBound W)
    (contained : ∀ y, ∃ x, ∀ v, outerAdhesion D y v → v∈original.bag x) :
    ∀ y, (N.adhesionList y).length ≤ W := by
  classical
  intro y
  obtain ⟨x,hx⟩ := contained y
  have hd : (N.adhesionList y).Nodup := (D.nodup y).filter _
  have hs : N.adhesionList y ⊆ original.bag x :=
    fun v hv => hx v ((N.mem_adhesionList y v).mp hv)
  exact (hd.length_le_of_subset hs).trans (hb x)

#print axioms inherited_adhesionList_bound
end StackSorting.GraphWidth.Nested
