import FiniteTreeCotreeCount
import FiniteSpanningTree

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

/-- A parent-numbered representation of the actual dual complement, including
its two-sided face relabeling. Constructed below from map incidence and Euler. -/
structure ActualCotree {α V F} (I : IncidenceMap α V F) (T : RootedTree V) where
  tree : RootedTree F
  code : FiniteCode (Fin F) F
  edge : ∀ {a b}, CotreeAdj I T a b → TreeAdj tree (code.encode a) (code.encode b)
  edge_back : ∀ {i j}, TreeAdj tree i j → CotreeAdj I T (code.decode i) (code.decode j)

theorem exists_actualCotree {α V F E} (I : IncidenceMap α V F)
    (C : OrbitCount I.reverse E) (T : RootedTree V)
    (hc : CutContinues I)
    (hdual : ∀ a b, Walk (FullDualAdj I) (fun _ => True) a b)
    (hedge : ∀ x, x.val≠0 → ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=T.parent x)
    (heuler : (V-1)+(F-1)=E) (root : Fin F) : Nonempty (ActualCotree I T) := by
  classical
  let S := relabeledSpanningTree (CotreeAdj I T)
    (dual_complement_tree_connected I T hc hdual) root
  let R : FiniteCode (Fin F) F := ⟨S.index,S.label,S.label_index,S.index_label⟩
  let p : Fin (V-1) → α := fun i => Classical.choose (hedge (treeChild i) (treeChild_ne_zero i))
  have hp : ∀ i, I.tail (p i)=treeChild i ∧ I.tail (I.reverse (p i))=T.parent (treeChild i) := by
    intro i
    exact Classical.choose_spec (hedge (treeChild i) (treeChild_ne_zero i))
  have he : ∀ i : Fin (F-1), ∃ d,
      I.face d=S.label (treeChild i) ∧ I.face (I.reverse d)=S.label (S.tree.parent (treeChild i)) ∧
      ¬TreeAdj T (I.tail d) (I.tail (I.reverse d)) := by
    intro i
    exact cotreeAdj_symm I T (S.parent_edge (treeChild i) (treeChild_ne_zero i))
  let q : Fin (F-1) → α := fun i => Classical.choose (he i)
  have hq := fun i => Classical.choose_spec (he i)
  have qt : ∀ i, R.encode (I.face (q i))=treeChild i := by
    intro i
    change S.index (I.face (q i))=treeChild i
    rw [(hq i).1,S.index_label]
  have qh : ∀ i, R.encode (I.face (I.reverse (q i)))=S.tree.parent (treeChild i) := by
    intro i
    change S.index (I.face (I.reverse (q i)))=S.tree.parent (treeChild i)
    rw [(hq i).2.1,S.index_label]
  refine ⟨⟨S.tree,R,?_,?_⟩⟩
  · exact cotree_edge_is_parent_edge I C T S.tree R p q (fun i => (hp i).1)
      (fun i => (hp i).2) qt qh (fun i => (hq i).2.2) heuler
  · exact S.edge (cotreeAdj_symm I T)

noncomputable def actualCotree {α V F E} (I : IncidenceMap α V F)
    (C : OrbitCount I.reverse E) (T : RootedTree V)
    (hc : CutContinues I)
    (hdual : ∀ a b, Walk (FullDualAdj I) (fun _ => True) a b)
    (hedge : ∀ x, x.val≠0 → ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=T.parent x)
    (heuler : (V-1)+(F-1)=E) (root : Fin F) : ActualCotree I T :=
  Classical.choice (exists_actualCotree I C T hc hdual hedge heuler root)

end StackSorting.GraphWidth.UCurve.PlaneGrid
