import RootedLocalForest

namespace StackSorting.GraphWidth.MarginalA2.RootedLocal
open FinitePort SameVertexForest ConnectedConeNormalization
variable {n : Nat} {G : Graph n}

theorem label_eq_none_iff (O : RankedOrder n) (i : Fin (Fintype.card (Node n))) :
    label O i=none ↔ i.val=0 := by
  constructor
  · intro h
    apply ((numbered O).label_eq_root_iff i).mp
    apply (nodeEquiv n).symm.injective
    simpa only [label,ranked,Equiv.symm_apply_apply] using h
  · exact exact_root O i

@[simp] theorem index_none_val (O : RankedOrder n) : (index O none).val=0 :=
  (label_eq_none_iff O _).mp (label_index O none)

theorem mem_bag_iff (F : ForestDecomposition G) (j : Fin (Fintype.card (Node n))) (u : Fin n) :
    u∈(decomposition F).bag j ↔ ∃ v, label F.order j=some v ∧ u∈F.bag v := by
  cases h : label F.order j <;> simp [decomposition,bag,h]

#print axioms label_eq_none_iff
#print axioms mem_bag_iff
end StackSorting.GraphWidth.MarginalA2.RootedLocal
