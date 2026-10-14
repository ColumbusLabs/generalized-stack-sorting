import SubstitutedParentTree

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested.TreeSubstitution
open FinitePort
variable {t : Nat} {T : RootedTree t} (S : TreeSubstitution T)

/-- The actual undirected substituted-parent edges, omitting the root loop. -/
def Adj (u v : S.Node) : Prop :=
  (u≠S.root ∧ S.parent u=v) ∨ (v≠S.root ∧ S.parent v=u)

theorem adj_symm {u v : S.Node} : S.Adj u v → S.Adj v u := Or.symm

theorem label_injective : Function.Injective S.label := by
  intro i j h
  have e := congrArg S.index h
  simpa only [index_label] using e

theorem label_eq_root_iff (i : Fin (Fintype.card S.Node)) : S.label i=S.root ↔ i.val=0 := by
  constructor
  · intro h
    have h' : S.numbered.label i=S.ranked.root := by
      apply S.nodeEquiv.symm.injective
      simpa only [label,ranked,Equiv.symm_apply_apply] using h
    exact (S.numbered.label_eq_root_iff i).mp h'
  · exact S.exact_root i

theorem parent_index (v : S.Node) : S.tree.parent (S.index v)=S.index (S.parent v) := by
  apply S.label_injective
  rw [S.exact_parent,S.label_index,S.label_index]

theorem index_zero_iff (v : S.Node) : (S.index v).val=0 ↔ v=S.root := by
  rw [← S.label_eq_root_iff,S.label_index]

/-- Numbering preserves all and only the concrete substituted parent edges. -/
theorem exact_adjacency (u v : S.Node) :
    TreeAdj S.tree (S.index u) (S.index v) ↔ S.Adj u v := by
  constructor
  · rintro (⟨hu,he⟩ | ⟨hv,he⟩)
    · left
      refine ⟨fun h => hu ((S.index_zero_iff u).mpr h),?_⟩
      have q := congrArg S.label he
      simpa only [S.exact_parent,S.label_index] using q
    · right
      refine ⟨fun h => hv ((S.index_zero_iff v).mpr h),?_⟩
      have q := congrArg S.label he
      simpa only [S.exact_parent,S.label_index] using q
  · rintro (⟨hu,he⟩ | ⟨hv,he⟩)
    · exact Or.inl ⟨fun h => hu ((S.index_zero_iff u).mp h),by rw [S.parent_index,he]⟩
    · exact Or.inr ⟨fun h => hv ((S.index_zero_iff v).mp h),by rw [S.parent_index,he]⟩

/-- Actual walks and their vertex predicates transport through the numbering. -/
theorem walk_index {P : S.Node → Prop} {u v : S.Node}
    (h : Walk S.Adj P u v) :
    Walk (TreeAdj S.tree) (fun i => P (S.label i)) (S.index u) (S.index v) := by
  induction h with
  | refl hu => exact .refl (by simpa only [S.label_index] using hu)
  | step hu huv _ ih =>
    exact .step (by simpa only [S.label_index] using hu) ((S.exact_adjacency _ _).mpr huv) ih

theorem local_adjacency (x : Fin t) {u v : Fin (S.size x)}
    (h : TreeAdj (S.localTree x) u v) : S.Adj ⟨x,u⟩ ⟨x,v⟩ := by
  rcases h with ⟨hu,he⟩ | ⟨hv,he⟩
  · left
    refine ⟨?_,?_⟩
    · intro eq
      have er : (⟨x,u⟩ : S.Node).2.val=S.root.2.val := congrArg (fun a : S.Node => a.2.val) eq
      exact hu er
    · dsimp only [parent]
      split
      · exact congrArg (fun y => (⟨x,y⟩ : S.Node)) he
      · contradiction
  · right
    refine ⟨?_,?_⟩
    · intro eq
      have er : (⟨x,v⟩ : S.Node).2.val=S.root.2.val := congrArg (fun a : S.Node => a.2.val) eq
      exact hv er
    · dsimp only [parent]
      split
      · exact congrArg (fun y => (⟨x,y⟩ : S.Node)) he
      · contradiction

theorem local_walk (x : Fin t) {P : S.Node → Prop} {u v : Fin (S.size x)}
    (h : Walk (TreeAdj (S.localTree x)) (fun y => P ⟨x,y⟩) u v) :
    Walk S.Adj P ⟨x,u⟩ ⟨x,v⟩ := by
  induction h with
  | refl hu => exact .refl hu
  | step hu huv _ ih => exact .step hu (S.local_adjacency x huv) ih

def localRoot (x : Fin t) : S.Node := ⟨x,⟨0,S.positive x⟩⟩

theorem parent_localRoot (x : Fin t) (hx : x.val≠0) :
    S.parent (S.localRoot x)=⟨T.parent x,S.attachment x⟩ := by
  simp [parent,localRoot,hx]

theorem attachment_adjacency (x : Fin t) (hx : x.val≠0) :
    S.Adj (S.localRoot x) ⟨T.parent x,S.attachment x⟩ := by
  left
  refine ⟨?_,S.parent_localRoot x hx⟩
  intro he
  exact hx (congrArg (fun a : S.Node => a.1.val) he)

#print axioms exact_adjacency
#print axioms walk_index
#print axioms attachment_adjacency
end StackSorting.GraphWidth.Nested.TreeSubstitution
