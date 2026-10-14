import BinarySiblingLinearOrder

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type} {n : Nat}

/-- A normalized shape is the original first-child/next-sibling encoding of
its reconstructed parent tree, with the supplied independent sibling order. -/
theorem normalPositionTree_rebuild_numbered (a : α) (l : BinaryTree α)
    (O : FixedOrder (BinaryTree.node a l .nil).numNodes)
    (ho : SiblingOrderCompatible O (.node a l .nil) (positionIndexEquiv _)) :
    build (normalPositionTree a l) O (BinaryTree.node a l .nil).numNodes
      [positionIndexEquiv _ .root] =
      positionRelabel (.node a l .nil) (positionIndexEquiv _) := by
  have h := build_from_parent_and_order (normalPositionTree a l) O (.node a l .nil)
    (positionIndexEquiv _) (fun p q => (normalPositionTree_exact_parent a l p q).symm) ho
  simpa only [positionRoots, List.map_nil, List.map_cons] using h

/-- Exact labelled inverse, valid even if every original node label is equal.
The carrier has precisely the positive binary nodes, without a dummy vertex. -/
theorem normalPositionTree_rebuild (a : α) (l : BinaryTree α)
    (O : FixedOrder (BinaryTree.node a l .nil).numNodes)
    (ho : SiblingOrderCompatible O (.node a l .nil) (positionIndexEquiv _)) :
    (build (normalPositionTree a l) O (BinaryTree.node a l .nil).numNodes
      [positionIndexEquiv _ .root]).map
        (fun i => ((positionIndexEquiv (.node a l .nil)).symm i).label) =
      .node a l .nil := by
  rw [normalPositionTree_rebuild_numbered a l O ho, positionRelabel_map]
  simpa only [Equiv.symm_apply_apply] using positionRelabel_labels (.node a l .nil)

/-- The general normalized inverse uses any exact finite carrier bijection,
not only the preorder numbering selected by normalPositionTree. -/
theorem normalized_rebuild (T : RootedTree n) (O : FixedOrder n)
    (a : α) (l : BinaryTree α) (e : Position (.node a l .nil) ≃ Fin n)
    (hp : ∀ p q, ParentPosition p q ↔ (e q).val ≠ 0 ∧ T.parent (e q) = e p)
    (ho : SiblingOrderCompatible O (.node a l .nil) e) :
    (build T O n [e .root]).map (fun i => (e.symm i).label) = .node a l .nil := by
  have h := build_from_parent_and_order T O (.node a l .nil) e hp ho
  simp only [positionRoots, List.map_nil, List.map_cons] at h
  rw [h, positionRelabel_map]
  simpa only [Equiv.symm_apply_apply] using positionRelabel_labels (.node a l .nil)

/-- Exact semantic parent recovery already forces each root of a finite
rooted carrier to have index zero. It is not an additional shape assumption. -/
theorem exact_parent_root_zero (T : RootedTree n) (t : BinaryTree α)
    (e : Position t ≃ Fin n)
    (hp : ∀ p q, ParentPosition p q ↔ (e q).val ≠ 0 ∧ T.parent (e q) = e p)
    (p : Position t) (hr : RootSibling p) : (e p).val = 0 := by
  by_contra hz
  have hpar : ParentPosition (e.symm (T.parent (e p))) p := by
    apply (hp _ _).mpr
    exact ⟨hz, (e.apply_symm_apply _).symm⟩
  exact rootSibling_no_parent hr hpar

/-- Strict sibling comparisons in the independent linear order suffice for
the exact labelled inverse. This interface is suitable for an MSO translation. -/
theorem normalPositionTree_rebuild_of_strict_order (a : α) (l : BinaryTree α)
    (O : FixedOrder (BinaryTree.node a l .nil).numNodes)
    (ho : SiblingOrderStrict O (.node a l .nil) (positionIndexEquiv _)) :
    (build (normalPositionTree a l) O (BinaryTree.node a l .nil).numNodes
      [positionIndexEquiv _ .root]).map
        (fun i => ((positionIndexEquiv (.node a l .nil)).symm i).label) =
      .node a l .nil := by
  exact normalPositionTree_rebuild a l O ((siblingOrder_iff_strict O _ _).mpr ho)

/-- Two normalized labelled binary trees with the same parent structure,
independent sibling order, root and node labels are literally equal. -/
theorem normalized_unique (T : RootedTree n) (O : FixedOrder n)
    (a b : α) (l r : BinaryTree α)
    (e : Position (.node a l .nil) ≃ Fin n)
    (f : Position (.node b r .nil) ≃ Fin n)
    (he : ∀ p q, ParentPosition p q ↔ (e q).val ≠ 0 ∧ T.parent (e q) = e p)
    (hf : ∀ p q, ParentPosition p q ↔ (f q).val ≠ 0 ∧ T.parent (f q) = f p)
    (oe : SiblingOrderCompatible O (.node a l .nil) e)
    (of : SiblingOrderCompatible O (.node b r .nil) f)
    (hl : ∀ i, (e.symm i).label = (f.symm i).label) :
    BinaryTree.node a l .nil = BinaryTree.node b r .nil := by
  have hr : e .root = f .root := Fin.ext
    ((exact_parent_root_zero T _ e he .root .root).trans
      (exact_parent_root_zero T _ f hf .root .root).symm)
  rw [← normalized_rebuild T O a l e he oe, ← normalized_rebuild T O b r f hf of, hr]
  have hh : (fun i => (e.symm i).label) = (fun i => (f.symm i).label) := funext hl
  rw [hh]

#print axioms normalPositionTree_rebuild_numbered
#print axioms normalPositionTree_rebuild
#print axioms normalized_rebuild
#print axioms exact_parent_root_zero
#print axioms normalPositionTree_rebuild_of_strict_order
#print axioms normalized_unique
end StackSorting.FinitePort.ChildSibling
