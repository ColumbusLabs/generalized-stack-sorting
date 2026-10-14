import ContractedRegions
import RankedParentTree
import Mathlib.Data.Fintype.EquivFin

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
variable {n : Nat}
namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

noncomputable section
local instance selectedDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

abbrev Selected := {x : Fin n // x ∈ A.nodes}

def selectedRoot : A.Selected := ⟨r,A.root_mem⟩

theorem contractedParent_root : A.contractedParent A.selectedRoot = A.selectedRoot := by
  simp [contractedParent,selectedRoot]

def selectedCode : A.Selected ≃ Fin (Fintype.card A.Selected) := Fintype.equivFin _

def selectedRankedParent : RankedParent (Fintype.card A.Selected) where
  root := A.selectedCode A.selectedRoot
  parent i := A.selectedCode (A.contractedParent (A.selectedCode.symm i))
  rank i := O.rank (A.selectedCode.symm i).val
  parent_root := by simp [A.contractedParent_root]
  rank_lt := by
    intro i hi
    simp only [Equiv.symm_apply_apply]
    apply O.increasing
    apply A.contractedParent_below
    intro he
    have hs : A.selectedCode.symm i = A.selectedRoot := Subtype.ext he
    exact hi (by rw [← A.selectedCode.apply_symm_apply i,hs])

def selectedNumbered := A.selectedRankedParent.numbered

def selectedTree : RootedTree (Fintype.card A.Selected) := A.selectedNumbered.tree

def selectedLabel (i : Fin (Fintype.card A.Selected)) : A.Selected :=
  A.selectedCode.symm (A.selectedNumbered.label i)

def selectedIndex (a : A.Selected) : Fin (Fintype.card A.Selected) :=
  A.selectedNumbered.index (A.selectedCode a)

@[simp] theorem selectedLabel_index (a : A.Selected) :
    A.selectedLabel (A.selectedIndex a) = a := by
  simp [selectedLabel,selectedIndex,RankedParent.Numbered.label_index]

@[simp] theorem selectedIndex_label (i : Fin (Fintype.card A.Selected)) :
    A.selectedIndex (A.selectedLabel i) = i := by
  simp [selectedLabel,selectedIndex,RankedParent.Numbered.index_label]

theorem selectedLabel_injective : Function.Injective A.selectedLabel := by
  intro i j h
  simpa using congrArg A.selectedIndex h

theorem selectedLabel_root (i : Fin (Fintype.card A.Selected)) (hi : i.val = 0) :
    A.selectedLabel i = A.selectedRoot := by
  unfold selectedLabel
  rw [A.selectedNumbered.label_root i hi]
  exact A.selectedCode.symm_apply_apply _

/-- Numbering preserves the chosen nearest-selected parent, rather than
rerooting an undirected spanning tree. -/
theorem selected_parent_exact (i : Fin (Fintype.card A.Selected)) :
    A.selectedLabel (A.selectedTree.parent i) = A.contractedParent (A.selectedLabel i) := by
  unfold selectedLabel selectedTree
  rw [A.selectedNumbered.parent_exact]
  exact A.selectedCode.symm_apply_apply _

theorem selectedIndex_parent (a : A.Selected) :
    A.selectedTree.parent (A.selectedIndex a) = A.selectedIndex (A.contractedParent a) := by
  apply A.selectedLabel_injective
  rw [A.selected_parent_exact,A.selectedLabel_index,A.selectedLabel_index]

end
end RootedSelection
end StackSorting.LowPathwidthParts
