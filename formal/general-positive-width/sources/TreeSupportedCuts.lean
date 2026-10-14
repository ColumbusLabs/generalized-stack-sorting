import RectangleConnected

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

/-- Incidence data only. No plane, Euler or width property is included. -/
structure IncidenceMap (DartType : Type) (vertices faces : Nat) where
  tail : DartType → Fin vertices
  reverse : DartType → DartType
  reverse_reverse : ∀ d, reverse (reverse d)=d
  face : DartType → Fin faces
  endpoints_injective : ∀ {d e}, tail d=tail e → tail (reverse d)=tail (reverse e) → d=e

def FaceCut {α V F} (I : IncidenceMap α V F) (color : Fin F → Bool) (d : α) : Prop :=
  color (I.face d)≠color (I.face (I.reverse d))

theorem faceCut_reverse {α V F} (I : IncidenceMap α V F) (color : Fin F → Bool) {d : α}
    (h : FaceCut I color d) : FaceCut I color (I.reverse d) := by
  unfold FaceCut at *
  rw [I.reverse_reverse]
  exact Ne.symm h

/-- This local condition will be derived from actual finite vertex-rotation
cycles. It is not an assumption of planarity or of a dual decomposition. -/
def CutContinues {α V F} (I : IncidenceMap α V F) : Prop :=
  ∀ color : Fin F → Bool, ∀ d : α, FaceCut I color d →
    ∃ e : α, I.tail e=I.tail d ∧ e≠d ∧ FaceCut I color e

/-- A nonempty face boundary satisfying local cycle continuation cannot be
supported entirely on the edges of a parent tree. The increasing-tail proof
is bounded by the actual finite vertex numbering. -/
theorem tree_supported_cut_false {α V F} (I : IncidenceMap α V F)
    (T : RootedTree V) (hc : CutContinues I) (color : Fin F → Bool)
    (hs : ∀ d, FaceCut I color d → TreeAdj T (I.tail d) (I.tail (I.reverse d)))
    (d : α) (hd : FaceCut I color d) : False := by
  have hadj := hs d hd
  by_cases hu : (I.tail d).val<(I.tail (I.reverse d)).val
  · exact tree_supported_cut_false I T hc color hs (I.reverse d) (faceCut_reverse I color hd)
  · obtain ⟨e,ht,hne,he⟩ := hc color d hd
    have heAdj := hs e he
    rw [ht] at heAdj
    by_cases hv : (I.tail d).val<(I.tail (I.reverse e)).val
    · exact tree_supported_cut_false I T hc color hs (I.reverse e) (faceCut_reverse I color he)
    · have hlt_d : (I.tail (I.reverse d)).val<(I.tail d).val := by
        have hn : I.tail (I.reverse d)≠I.tail d := by
          intro hh
          exact treeAdj_loopless T _ (hh ▸ hadj)
        have hn' : (I.tail (I.reverse d)).val≠(I.tail d).val := fun h => hn (Fin.ext h)
        omega
      have hlt_e : (I.tail (I.reverse e)).val<(I.tail d).val := by
        have hn : I.tail (I.reverse e)≠I.tail d := by
          intro hh
          exact treeAdj_loopless T _ (hh ▸ heAdj)
        have hn' : (I.tail (I.reverse e)).val≠(I.tail d).val := fun h => hn (Fin.ext h)
        omega
      have hh := tree_smaller_neighbor_unique T hadj heAdj hlt_d hlt_e
      exact hne (I.endpoints_injective ht hh.symm)
termination_by V-(I.tail d).val
decreasing_by
  all_goals have hb := (I.tail (I.reverse d)).isLt
  all_goals try { have hb' := (I.tail (I.reverse e)).isLt }
  all_goals omega

end StackSorting.GraphWidth.UCurve.PlaneGrid
