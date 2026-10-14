import FiniteSpanningTree

/-!
Extension of a prescribed finite rooted tree to a spanning tree. Existing list
positions, vertex labels, inverse indices, and parent links are all preserved.
The original constructor remains unchanged.
-/
namespace StackSorting.GraphWidth
open FinitePort

/-- A nonempty ordered set of vertices with a prescribed actual rooted tree.
Its first entry names the chosen original-graph root. -/
structure PrescribedPrefix {n} (adj : Fin n → Fin n → Prop) (root : Fin n) where
  vertices : List (Fin n)
  nodup : vertices.Nodup
  first : vertices[0]? = some root
  tree : RootedTree vertices.length
  parent_root : ∀ i, i.val = 0 → tree.parent i = i
  parent_edge : ∀ i, i.val ≠ 0 → adj vertices[(tree.parent i).val] vertices[i.val]

namespace PrescribedPrefix

theorem length_pos {n adj root} (P : @PrescribedPrefix n adj root) :
    0 < P.vertices.length := (List.getElem?_eq_some_iff.mp P.first).choose

theorem nonempty {n adj root} (P : @PrescribedPrefix n adj root) : P.vertices ≠ [] := by
  intro h
  have := P.length_pos
  simp [h] at this

/-- Old numeric indices retain their values in the full vertex universe. -/
def embed {n adj root} (P : @PrescribedPrefix n adj root)
    (i : Fin P.vertices.length) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (fin_list_length_le P.nodup)⟩

@[simp] theorem embed_val {n adj root} (P : @PrescribedPrefix n adj root)
    (i : Fin P.vertices.length) : (P.embed i).val = i.val := rfl

theorem embed_injective {n adj root} (P : @PrescribedPrefix n adj root)
    {i j} (h : P.embed i = P.embed j) : i = j :=
  Fin.ext (congrArg (fun v : Fin n => v.val) h)

theorem earlier {n adj root} (P : @PrescribedPrefix n adj root) :
    EarlierNeighbors adj P.vertices := by
  intro i hi hn
  let v : Fin P.vertices.length := ⟨i, hi⟩
  exact ⟨(P.tree.parent v).val, (P.tree.parent v).isLt,
    P.tree.parent_lt v hn, P.parent_edge v hn⟩

/-- Keep the prescribed old parent; only new vertices use the general choice. -/
noncomputable def extendedParent {n adj root} (P : @PrescribedPrefix n adj root)
    (E : RootedEnumeration adj root) (i : Fin n) : Fin n :=
  if hi : i.val < P.vertices.length then P.embed (P.tree.parent ⟨i.val, hi⟩)
  else E.tree.parent i

noncomputable def extendedTree {n adj root} (P : @PrescribedPrefix n adj root)
    (E : RootedEnumeration adj root) : RootedTree n where
  parent := P.extendedParent E
  parent_lt := by
    intro i hi
    simp only [extendedParent]
    split
    · rename_i hold
      exact P.tree.parent_lt ⟨i.val, hold⟩ hi
    · exact E.tree.parent_lt i hi

@[simp] theorem extended_parent_old {n adj root} (P : @PrescribedPrefix n adj root)
    (E : RootedEnumeration adj root) (i : Fin P.vertices.length) :
    (P.extendedTree E).parent (P.embed i) = P.embed (P.tree.parent i) := by
  change P.extendedParent E (P.embed i) = _
  unfold extendedParent
  exact dite_eq_left (show (P.embed i).val < P.vertices.length from i.isLt)

theorem extended_parent_root {n adj root} (P : @PrescribedPrefix n adj root)
    (E : RootedEnumeration adj root) (i : Fin n) (hi : i.val = 0) :
    (P.extendedTree E).parent i = i := by
  simp only [extendedTree, extendedParent]
  split
  · rename_i hold
    rw [P.parent_root ⟨i.val, hold⟩ hi]
    rfl
  · exact E.parent_root i hi

theorem extended_parent_edge {n adj root} (P : @PrescribedPrefix n adj root)
    (E : RootedEnumeration adj root)
    (hlabels : ∀ i, E.label (P.embed i) = P.vertices[i.val])
    (i : Fin n) (hi : i.val ≠ 0) :
    adj (E.label ((P.extendedTree E).parent i)) (E.label i) := by
  simp only [extendedTree, extendedParent]
  split
  · rename_i hold
    let old : Fin P.vertices.length := ⟨i.val, hold⟩
    change adj (E.label (P.embed (P.tree.parent old))) (E.label (P.embed old))
    rw [hlabels, hlabels]
    exact P.parent_edge old hi
  · exact E.parent_edge i hi

noncomputable def extendedSpanningTree {n adj root} (P : @PrescribedPrefix n adj root)
    (E : RootedEnumeration adj root)
    (hlabels : ∀ i, E.label (P.embed i) = P.vertices[i.val]) :
    RelabeledSpanningTree adj root where
  tree := P.extendedTree E
  label := E.label
  index := E.index
  label_index := E.label_index
  index_label := E.index_label
  label_root := E.label_root
  parent_root := P.extended_parent_root E
  parent_edge := P.extended_parent_edge E hlabels

end PrescribedPrefix

/-- Full spanning-tree data plus preservation of every old label and parent.
The inverse-index preservation field explicitly identifies the old vertices. -/
structure PreservingSpanningTree {n adj root} (P : @PrescribedPrefix n adj root) where
  spanning : RelabeledSpanningTree adj root
  labels : ∀ i, spanning.label (P.embed i) = P.vertices[i.val]
  indices : ∀ i, spanning.index P.vertices[i.val] = P.embed i
  parents : ∀ i, spanning.tree.parent (P.embed i) = P.embed (P.tree.parent i)

/-- A connected finite graph admits an extension preserving the entire given
rooted tree, not merely its vertex order. No completed tree is assumed. -/
theorem exists_preserving_spanning_tree {n adj root} (P : @PrescribedPrefix n adj root)
    (connected : ∀ u v, Walk adj (fun _ => True) u v) :
    Nonempty (PreservingSpanningTree P) := by
  obtain ⟨ys, hn, he, hc⟩ := extend_connected_enumeration adj connected P.vertices
    P.nodup P.earlier P.nonempty
  let E : RootedEnumeration adj root := {
    vertices := P.vertices ++ ys
    nodup := hn
    complete := hc
    earlier := he
    first := by
      simpa only [List.getElem?_append_left P.length_pos] using P.first
  }
  have hlabels : ∀ i, E.label (P.embed i) = P.vertices[i.val] := by
    intro i
    exact List.getElem_append_left i.isLt
  refine ⟨⟨P.extendedSpanningTree E hlabels, hlabels, ?_, ?_⟩⟩
  · intro i
    exact (congrArg E.index (hlabels i)).symm.trans (E.index_label (P.embed i))
  · exact P.extended_parent_old E

noncomputable def preservingSpanningTree {n adj root} (P : @PrescribedPrefix n adj root)
    (connected : ∀ u v, Walk adj (fun _ => True) u v) : PreservingSpanningTree P :=
  Classical.choice (exists_preserving_spanning_tree P connected)

namespace PreservingSpanningTree

theorem treeAdj_preserved {n adj root} {P : @PrescribedPrefix n adj root}
    (S : PreservingSpanningTree P) {i j} (h : TreeAdj P.tree i j) :
    TreeAdj S.spanning.tree (P.embed i) (P.embed j) := by
  obtain ⟨hi, hp⟩ | ⟨hj, hp⟩ := h
  · exact .inl ⟨hi, (S.parents i).trans (congrArg P.embed hp)⟩
  · exact .inr ⟨hj, (S.parents j).trans (congrArg P.embed hp)⟩

theorem treeAdj_reflected {n adj root} {P : @PrescribedPrefix n adj root}
    (S : PreservingSpanningTree P) {i j}
    (h : TreeAdj S.spanning.tree (P.embed i) (P.embed j)) : TreeAdj P.tree i j := by
  obtain ⟨hi, hp⟩ | ⟨hj, hp⟩ := h
  · exact .inl ⟨hi, P.embed_injective ((S.parents i).symm.trans hp)⟩
  · exact .inr ⟨hj, P.embed_injective ((S.parents j).symm.trans hp)⟩

theorem ancestor_preserved {n adj root} {P : @PrescribedPrefix n adj root}
    (S : PreservingSpanningTree P) {i j} (h : Ancestor P.tree i j) :
    Ancestor S.spanning.tree (P.embed i) (P.embed j) := by
  induction h with
  | refl => exact .refl _
  | @step v hv _ ih =>
    apply Ancestor.step (T := S.spanning.tree) (v := P.embed v) hv
    simpa only [S.parents] using ih

/-- New vertices introduce no new ancestors of any old vertex. -/
theorem ancestor_reflected {n adj root} {P : @PrescribedPrefix n adj root}
    (S : PreservingSpanningTree P) (i j : Fin P.vertices.length)
    (h : Ancestor S.spanning.tree (P.embed i) (P.embed j)) : Ancestor P.tree i j := by
  by_cases hij : i = j
  · subst j
    exact .refl _
  · have hne : P.embed i ≠ P.embed j := fun hh => hij (P.embed_injective hh)
    have hj : j.val ≠ 0 := h.ne_zero_of_strict hne
    have hp : Ancestor S.spanning.tree (P.embed i) (P.embed (P.tree.parent j)) := by
      simpa only [S.parents] using h.parent_of_ne hne
    exact .step hj (S.ancestor_reflected i (P.tree.parent j) hp)
termination_by j.val
decreasing_by exact P.tree.parent_lt j hj

theorem ancestor_iff {n adj root} {P : @PrescribedPrefix n adj root}
    (S : PreservingSpanningTree P) (i j : Fin P.vertices.length) :
    Ancestor S.spanning.tree (P.embed i) (P.embed j) ↔ Ancestor P.tree i j :=
  ⟨S.ancestor_reflected i j, S.ancestor_preserved⟩

/-- Every prescribed tree path transfers with its vertex predicate intact. -/
theorem walk_preserved {n adj root} {P : @PrescribedPrefix n adj root}
    (S : PreservingSpanningTree P) {Q : Fin n → Prop} {i j}
    (h : Walk (TreeAdj P.tree) (fun k => Q (P.embed k)) i j) :
    Walk (TreeAdj S.spanning.tree) Q (P.embed i) (P.embed j) := by
  induction h with
  | refl hp => exact .refl hp
  | step hp he _ ih => exact .step hp (S.treeAdj_preserved he) ih

end PreservingSpanningTree

/-- Parent iteration records the exact vertex sequence along a root path. -/
def parentIter {n} (T : RootedTree n) : Nat → Fin n → Fin n
  | 0, i => i
  | k + 1, i => parentIter T k (T.parent i)

theorem PreservingSpanningTree.parentIter_preserved {n adj root}
    {P : @PrescribedPrefix n adj root} (S : PreservingSpanningTree P)
    (k : Nat) (i : Fin P.vertices.length) :
    parentIter S.spanning.tree k (P.embed i) = P.embed (parentIter P.tree k i) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [parentIter, S.parents]
    exact ih (P.tree.parent i)

/-- The original graph labels along every old root path are unchanged. -/
theorem PreservingSpanningTree.parentIter_labels {n adj root}
    {P : @PrescribedPrefix n adj root} (S : PreservingSpanningTree P)
    (k : Nat) (i : Fin P.vertices.length) :
    S.spanning.label (parentIter S.spanning.tree k (P.embed i)) =
      P.vertices[(parentIter P.tree k i).val] := by
  rw [S.parentIter_preserved, S.labels]

end StackSorting.GraphWidth
