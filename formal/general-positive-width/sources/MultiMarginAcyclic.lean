import MultiMarginSpanning
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested

/-- Standard simple-graph adapter for the actual parent tree. -/
def treeSimple {q : Nat} (U : RootedTree q) : SimpleGraph (Fin q) where
  Adj := TreeAdj U
  symm := ⟨fun _ _ h => treeAdj_symm U h⟩
  loopless := ⟨treeAdj_loopless U⟩

/-- The only edge leaving a rooted subtree is its root's parent edge. -/
theorem subtree_exit_pair {q : Nat} (U : RootedTree q) {x a b : Fin q}
    (ha : Ancestor U x a) (hb : ¬ Ancestor U x b) (he : TreeAdj U a b) :
    a=x ∧ b=U.parent x := by
  rcases he with ⟨hn,hp⟩ | ⟨hn,hp⟩
  · by_cases hx : x=a
    · subst a
      exact ⟨rfl,hp.symm⟩
    · exact (hb (hp ▸ ha.parent_of_ne hx)).elim
  · exact (hb (.step hn (hp.symm ▸ ha))).elim

/-- Every crossing walk uses that precise parent edge. -/
theorem crossing_mem_parent_edge {q : Nat} (U : RootedTree q) (x : Fin q)
    {a b : Fin q} (w : (treeSimple U).Walk a b)
    (ha : Ancestor U x a) (hb : ¬ Ancestor U x b) : s(x,U.parent x) ∈ w.edges := by
  induction w with
  | nil => exact (hb ha).elim
  | @cons a c b he tail ih =>
    by_cases hc : Ancestor U x c
    · have h := ih hc hb
      simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]
      exact Or.inr h
    · obtain ⟨rfl,rfl⟩ := subtree_exit_pair U ha hc he
      simp only [SimpleGraph.Walk.edges_cons,List.mem_cons,true_or]

/-- Genuine standard acyclicity follows from proved parent-edge cuts. -/
theorem treeSimple_acyclic {q : Nat} (U : RootedTree q) : (treeSimple U).IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v he
  have bridge : ∀ x : Fin q, x.val≠0 → (treeSimple U).IsBridge s(x,U.parent x) := by
    intro x hx
    apply SimpleGraph.isBridge_iff_forall_walk_mem_edges.mpr
    intro w
    apply crossing_mem_parent_edge U x w (.refl _)
    intro ha
    have hi := ha.val_le
    have hl := U.parent_lt x hx
    omega
  rcases he with ⟨hu,hp⟩ | ⟨hv,hp⟩
  · simpa only [hp] using bridge u hu
  · have h := bridge v hv
    simpa only [hp,Sym2.eq_swap] using h

namespace Encoding
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (s : Sane D) (ht : 0<t)

def unionSimple : SimpleGraph (Fin n) where
  Adj := Union s ht
  symm := ⟨by
    intro u v h
    exact h.elim (fun h => Or.inl (M_symm s ht h)) (fun h => Or.inr (K_symm s h))⟩
  loopless := ⟨by
    intro v h
    exact (Completion D).loopless v (h.elim (M_completed s ht) (K_completed s))⟩

/-- M∪K has standard graph-theoretic acyclicity on original vertices. -/
theorem union_acyclic : (unionSimple s ht).IsAcyclic := by
  let S := substitution s ht
  let f : unionSimple s ht →g treeSimple S.tree := {
    toFun := fun v => S.index (index s ht v)
    map_rel' := fun {u v} h => (union_numbered s ht u v).mp h }
  have hi : Function.Injective f := by
    intro u v he
    have h := congrArg (fun i => vertex s ht (S.label i)) he
    change vertex s ht (S.label (S.index (index s ht u)))=vertex s ht (S.label (S.index (index s ht v))) at h
    simpa only [S.label_index,vertex_index] using h
  exact SimpleGraph.IsAcyclic.comap f hi (treeSimple_acyclic S.tree)

#print axioms treeSimple_acyclic
#print axioms union_acyclic
end Encoding
end StackSorting.GraphWidth.MultiMargin
