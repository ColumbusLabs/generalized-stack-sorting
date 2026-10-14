import RankedForestParent
import ConnectedFiberDecomposition

namespace StackSorting.SameVertexForest.RankedOrder
variable {n : Nat} (O : RankedOrder n)

noncomputable def root (O : RankedOrder n) (v : Fin n) : Fin n :=
  if _h : O.parent v = v then v else root O (O.parent v)
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (by assumption)

theorem root_fixed (O : RankedOrder n) (v : Fin n) : O.parent (O.root v) = O.root v := by
  rw [root]
  split
  · assumption
  · exact root_fixed O (O.parent v)
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (by assumption)

theorem root_ancestor (O : RankedOrder n) (v : Fin n) : Ancestor O.forest (O.root v) v := by
  rw [root]
  split
  · exact Ancestor.refl _
  · rename_i h
    exact Ancestor.step h (root_ancestor O (O.parent v))
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (by assumption)

theorem fixed_no_predecessor {v : Fin n} (h : O.parent v = v) :
    ∀ u, ¬ O.rel u v := by
  intro u hu
  exact O.parent_ne_of_pred hu h

theorem ancestor_trans {u v w : Fin n}
    (huv : Ancestor O.forest u v) (hvw : Ancestor O.forest v w) :
    Ancestor O.forest u w := by
  rcases O.ancestor_iff.mp huv with h | rfl
  · rcases O.ancestor_iff.mp hvw with k | rfl
    · exact O.ancestor_of_rel (O.trans h k)
    · exact O.ancestor_of_rel h
  · exact hvw

theorem fixed_ancestors_unique {u v w : Fin n}
    (hu : O.parent u = u) (hv : O.parent v = v)
    (huw : Ancestor O.forest u w) (hvw : Ancestor O.forest v w) : u = v := by
  rcases O.ancestor_iff.mp huw with h | rfl
  · rcases O.ancestor_iff.mp hvw with k | rfl
    · rcases O.predecessors h k with huv | he | hvu
      · exact False.elim (O.fixed_no_predecessor hv u huv)
      · exact he
      · exact False.elim (O.fixed_no_predecessor hu v hvu)
    · exact False.elim (O.fixed_no_predecessor hv u h)
  · rcases O.ancestor_iff.mp hvw with k | he
    · exact False.elim (O.fixed_no_predecessor hu v k)
    · exact he.symm

theorem roots_eq_of_ancestor {u v : Fin n} (h : Ancestor O.forest u v) :
    O.root u = O.root v :=
  O.fixed_ancestors_unique (O.root_fixed u) (O.root_fixed v)
    (O.ancestor_trans (O.root_ancestor u) h) (O.root_ancestor v)

theorem roots_eq_of_graph_walk {G : GraphWidth.Graph n}
    (he : ∀ u v, G.Adj u v → Ancestor O.forest u v ∨ Ancestor O.forest v u)
    {u v : Fin n} (hw : GraphWidth.Walk G.Adj (fun _ => True) u v) :
    O.root u = O.root v := by
  induction hw with
  | refl => rfl
  | @step u z v _ huz _ ih =>
    have hz : O.root u = O.root z := by
      rcases he u z huz with h | h
      · exact O.roots_eq_of_ancestor h
      · exact (O.roots_eq_of_ancestor h).symm
    exact hz.trans ih

/-- A connected nonempty original graph makes the constructed forest one
actual parent tree, without selecting a decomposition or adding vertices. -/
theorem connected_single_root {G : GraphWidth.Graph n}
    (he : ∀ u v, G.Adj u v → Ancestor O.forest u v ∨ Ancestor O.forest v u)
    (hc : ∀ u v, GraphWidth.Walk G.Adj (fun _ => True) u v) (hn : 0 < n) :
    ∃ r : Fin n, O.parent r = r ∧ ∀ v, Ancestor O.forest r v := by
  let z : Fin n := ⟨0,hn⟩
  refine ⟨O.root z, O.root_fixed z, ?_⟩
  intro v
  have h := O.roots_eq_of_graph_walk he (hc z v)
  exact h.symm ▸ O.root_ancestor v

#print axioms root_ancestor
#print axioms connected_single_root
end StackSorting.SameVertexForest.RankedOrder
