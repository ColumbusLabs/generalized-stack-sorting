import BinaryParentReachability
import FiniteAlphabetBinaryCode

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic GraphWidth
variable {α β : Type}

theorem parent_positionMapEquiv (f : α → β) (t : BinaryTree α)
    (p q : Position t) :
    ParentPosition (positionMapEquiv f t p) (positionMapEquiv f t q) ↔ ParentPosition p q := by
  rw [parentPosition_iff_reach,parentPosition_iff_reach]
  constructor
  · rintro ⟨z,hz,hq⟩
    refine ⟨unmapPosition f t z, ?_, ?_⟩
    · simpa only [positionMapEquiv,Equiv.coe_fn_mk,unmap_mapPosition] using
        child_unmapPosition f t hz
    · have h := hq.lift (unmapPosition f t) (fun _ _ e => child_unmapPosition f t e)
      simpa only [Function.onFun,positionMapEquiv,Equiv.coe_fn_mk,unmap_mapPosition] using h
  · rintro ⟨z,hz,hq⟩
    exact ⟨mapPosition f z,child_mapPosition f hz,
      hq.lift (mapPosition f) (fun _ _ e => child_mapPosition f e)⟩

/-- The finite-alphabet binary code's parent is the exact original numbered
parent, independently of repeated finite labels. -/
theorem binaryCode_parent {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (p q : Position (binaryCode E O hn)) :
    ParentPosition p q ↔ (binaryCodeIndexEquiv E O hn q).val ≠ 0 ∧
      E.tree.parent (binaryCodeIndexEquiv E O hn q) = binaryCodeIndexEquiv E O hn p := by
  unfold binaryCode at p q
  let t := build E.tree O n [⟨0,hn⟩]
  let f := alphabetCode E.code E.bounded
  have h := parent_positionMapEquiv f t ((positionMapEquiv f t).symm p)
    ((positionMapEquiv f t).symm q)
  change ParentPosition (mapPosition f (unmapPosition f t p))
      (mapPosition f (unmapPosition f t q)) ↔
      ParentPosition (unmapPosition f t p) (unmapPosition f t q) at h
  dsimp [t,f] at h
  simp only [map_unmapPosition] at h
  exact h.trans (original_parent_position E.tree O ⟨0,hn⟩ rfl _ _)

#print axioms parent_positionMapEquiv
#print axioms binaryCode_parent
end StackSorting.FinitePort.ChildSibling
