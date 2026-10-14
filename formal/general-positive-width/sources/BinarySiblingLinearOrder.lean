import BinaryForestReconstruction
import Mathlib.Data.List.Sort

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type} {n : Nat} (O : FixedOrder n)

/-- The independently supplied vertex chronology, expressed by strict ranks
in its duplicate-free exhaustive list. This is not the preorder numbering. -/
def OrderBefore (u v : Fin n) : Prop := O.vertices.idxOf u < O.vertices.idxOf v

theorem fixedOrder_pairwise : O.vertices.Pairwise (OrderBefore O) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  unfold OrderBefore
  simpa only [O.nodup.idxOf_getElem] using hij

/-- All pairs in each literal next-sibling chain must respect the independently
specified strict linear order. -/
def SiblingOrderStrict (t : BinaryTree α) (e : Position t → Fin n) : Prop :=
  ∀ p, ((positionChildren p).map e).Pairwise (OrderBefore O)

theorem siblingOrder_iff_strict (t : BinaryTree α) (e : Position t → Fin n) :
    SiblingOrderCompatible O t e ↔ SiblingOrderStrict O t e := by
  let : Std.Antisymm (OrderBefore O) := ⟨fun _ _ hab hba =>
    False.elim ((Nat.lt_asymm hab) hba)⟩
  let : Std.Irrefl (OrderBefore O) := ⟨fun _ => Nat.lt_irrefl _⟩
  constructor
  · intro h p
    exact (fixedOrder_pairwise O).sublist (h p)
  · intro h p
    apply List.sublist_of_subperm_of_pairwise _ (h p) (fixedOrder_pairwise O)
    exact List.subperm_of_subset (h p).nodup (fun _ _ => O.complete _)

#print axioms fixedOrder_pairwise
#print axioms siblingOrder_iff_strict
end StackSorting.FinitePort.ChildSibling
