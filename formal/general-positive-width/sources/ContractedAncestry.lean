import ContractedDecomposition

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
variable {n : Nat}
namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)
noncomputable section
local instance ancestryDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

theorem selectedLabel_ne_root {i : Fin (Fintype.card A.Selected)} (hi : i.val ≠ 0) :
    (A.selectedLabel i).val ≠ r := by
  intro he
  have hs : A.selectedLabel i = A.selectedRoot := Subtype.ext he
  have hcode := congrArg A.selectedCode hs
  have hlabel : A.selectedNumbered.label i = A.selectedRankedParent.root := by
    simpa [selectedLabel,selectedRankedParent] using hcode
  exact hi ((A.selectedNumbered.label_eq_root_iff i).mp hlabel)

theorem selected_ancestor_cone {i j : Fin (Fintype.card A.Selected)}
    (h : Ancestor A.selectedTree i j) : Cone O (A.selectedLabel i).val (A.selectedLabel j).val := by
  induction h with
  | refl => exact cone_refl O _
  | @step j hj h ih =>
    rw [A.selected_parent_exact] at ih
    exact cone_trans O ih (Or.inl (A.contractedParent_below _ (A.selectedLabel_ne_root hj)))

theorem cone_selected_ancestor (a b : A.Selected) (h : Cone O a.val b.val) :
    Ancestor A.selectedTree (A.selectedIndex a) (A.selectedIndex b) := by
  by_cases hab : a = b
  · subst b
    exact .refl _
  · have hv : a.val ≠ b.val := fun he => hab (Subtype.ext he)
    have hrel : O.rel a.val b.val := h.resolve_right hv
    have hb : b.val ≠ r := by
      intro he
      have har := A.inside a.val a.property
      have hba : Cone O b.val a.val := by simpa only [he] using har
      exact O.irrefl a.val (by
        rcases hba with har | har
        · exact O.trans hrel har
        · exact har ▸ hrel)
    have hr : O.rel r b.val := (A.inside b.val b.property).resolve_right (Ne.symm hb)
    have hc : Cone O a.val (A.contractedParent b).val := by
      rw [A.contractedParent_eq b hb hr]
      exact A.owner_nearest _ _ a.property (cone_parent O hrel)
    apply Ancestor.step (A.selectedIndex_nonzero b hb)
    rw [A.selectedIndex_parent]
    exact cone_selected_ancestor a (A.contractedParent b) hc
termination_by O.rank b.val
decreasing_by exact O.increasing (A.contractedParent_below b hb)

theorem selected_ancestor_iff (i j : Fin (Fintype.card A.Selected)) :
    Ancestor A.selectedTree i j ↔ Cone O (A.selectedLabel i).val (A.selectedLabel j).val := by
  constructor
  · exact A.selected_ancestor_cone
  · intro h
    simpa using A.cone_selected_ancestor (A.selectedLabel i) (A.selectedLabel j) h

end
end RootedSelection
end StackSorting.LowPathwidthParts
