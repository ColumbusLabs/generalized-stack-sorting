import FiniteIncidenceCuts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

theorem ancestor_larger_neighbor {V} (T : RootedTree V) {v x y : Fin V}
    (ha : Ancestor T v x) (he : TreeAdj T x y) (hlt : x.val<y.val) :
    Ancestor T v y := by
  obtain ⟨hx,hp⟩ | ⟨hy,hp⟩ := he
  · have := T.parent_lt x hx
    rw [hp] at this
    omega
  · exact .step hy (hp ▸ ha)

/-- The tree-boundary contradiction works within a rooted descendant subtree:
its only possible exiting tree edge points down, while the proof follows
strictly increasing vertices. -/
theorem subtree_supported_cut_false {α V F} (I : IncidenceMap α V F)
    (T : RootedTree V) (hc : CutContinues I) (v : Fin V) (color : Fin F → Bool)
    (hs : ∀ d, Ancestor T v (I.tail d) → FaceCut I color d →
      TreeAdj T (I.tail d) (I.tail (I.reverse d)))
    (d : α) (ha : Ancestor T v (I.tail d)) (hd : FaceCut I color d) : False := by
  have hadj := hs d ha hd
  by_cases hu : (I.tail d).val<(I.tail (I.reverse d)).val
  · exact subtree_supported_cut_false I T hc v color hs (I.reverse d)
      (ancestor_larger_neighbor T ha hadj hu) (faceCut_reverse I color hd)
  · obtain ⟨e,ht,hne,he⟩ := hc color d hd
    have hea : Ancestor T v (I.tail e) := ht ▸ ha
    have heAdj := hs e hea he
    rw [ht] at heAdj
    by_cases hv : (I.tail d).val<(I.tail (I.reverse e)).val
    · exact subtree_supported_cut_false I T hc v color hs (I.reverse e)
        (ancestor_larger_neighbor T ha heAdj hv) (faceCut_reverse I color he)
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
