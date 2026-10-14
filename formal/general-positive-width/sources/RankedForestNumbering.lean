import RankedForestRoots
import RankedParentTree

/-! Exact parent-preserving topological numbering of a same-vertex ranked
forest with one actual root. The root and its ancestry are explicit inputs;
the numbering and all parent links are constructed. -/
namespace StackSorting.SameVertexForest.RankedOrder
open GraphWidth

variable {n : Nat} (O : RankedOrder n) (r : Fin n)
  (hr : O.parent r = r) (ha : ∀ v, Ancestor O.forest r v)

include hr ha in
theorem parent_ne_of_ne_root {v : Fin n} (hv : v ≠ r) : O.parent v ≠ v := by
  intro hp
  exact hv (O.fixed_ancestors_unique hp hr (.refl v) (ha v))

noncomputable def rootedParent : RankedParent n where
  root := r
  parent := O.parent
  rank := O.rank
  parent_root := hr
  rank_lt _ h := O.parent_rank_lt (O.parent_ne_of_ne_root r hr ha h)

namespace Numbered
variable (N : (O.rootedParent r hr ha).Numbered)

theorem parent_exact (i : Fin n) :
    N.label (N.tree.parent i) = O.parent (N.label i) := N.parent_exact i

theorem ancestor_label {i j : Fin n} (h : FinitePort.Ancestor N.tree i j) :
    Ancestor O.forest (N.label i) (N.label j) := by
  induction h with
  | refl => exact .refl _
  | @step v hv hp ih =>
    have hne : O.parent (N.label v) ≠ N.label v := by
      intro he
      have ht : N.tree.parent v = v := N.label_injective ((N.parent_exact v).trans he)
      have hl := N.tree.parent_lt v hv
      rw [ht] at hl
      exact Nat.lt_irrefl _ hl
    apply Ancestor.step hne
    simpa only [N.parent_exact, rootedParent, RankedOrder.forest] using ih

theorem ancestor_index {u v : Fin n} (h : Ancestor O.forest u v) :
    FinitePort.Ancestor N.tree (N.index u) (N.index v) := by
  induction h with
  | refl => exact .refl _
  | @step v hv hp ih =>
    have hn : (N.index v).val ≠ 0 := by
      intro hz
      have he : v = r := (N.label_index v).symm.trans (N.label_root _ hz)
      subst v
      exact hv hr
    apply FinitePort.Ancestor.step hn
    simpa only [N.parent_index, rootedParent, RankedOrder.forest] using ih

theorem ancestor_iff {i j : Fin n} :
    FinitePort.Ancestor N.tree i j ↔ Ancestor O.forest (N.label i) (N.label j) := by
  constructor
  · exact ancestor_label O r hr ha N
  · intro h
    simpa only [N.index_label] using ancestor_index O r hr ha N h

theorem ancestor_index_iff {u v : Fin n} :
    FinitePort.Ancestor N.tree (N.index u) (N.index v) ↔ Ancestor O.forest u v := by
  rw [ancestor_iff O r hr ha N, N.label_index, N.label_index]

end Numbered

/-- Connected elimination forests have a constructed numbered tree on the
same number of vertices, with a two-sided relabeling preserving every parent. -/
theorem connected_numbered {G : Graph n}
    (he : ∀ u v, G.Adj u v → Ancestor O.forest u v ∨ Ancestor O.forest v u)
    (hc : ∀ u v, Walk G.Adj (fun _ => True) u v) (hn : 0 < n) :
    ∃ (r : Fin n) (hr : O.parent r = r) (ha : ∀ v, Ancestor O.forest r v),
      Nonempty (O.rootedParent r hr ha).Numbered := by
  obtain ⟨r,hr,ha⟩ := O.connected_single_root he hc hn
  exact ⟨r,hr,ha,(O.rootedParent r hr ha).exists_numbered⟩

#print axioms Numbered.ancestor_iff
#print axioms connected_numbered
end StackSorting.SameVertexForest.RankedOrder
