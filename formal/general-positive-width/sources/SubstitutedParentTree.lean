import RankedParentTree
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace StackSorting.GraphWidth.Nested
open FinitePort

/-- Concrete local rooted trees, with one attachment point in each outer
parent's local tree. This is a tree-substitution lemma; later clique lemmas
construct the attachments from actual nested decompositions. -/
structure TreeSubstitution {t : Nat} (T : RootedTree t) where
  outerNonempty : 0<t
  size : Fin t → Nat
  positive : ∀ x, 0<size x
  localTree : ∀ x, RootedTree (size x)
  attachment : ∀ x, Fin (size (T.parent x))

namespace TreeSubstitution
variable {t : Nat} {T : RootedTree t} (S : TreeSubstitution T)

abbrev Node := (x : Fin t) × Fin (S.size x)

def root : S.Node := ⟨⟨0,S.outerNonempty⟩,⟨0,S.positive _⟩⟩

def parent (v : S.Node) : S.Node :=
  if v.2.val ≠ 0 then ⟨v.1,(S.localTree v.1).parent v.2⟩
  else if v.1.val ≠ 0 then ⟨T.parent v.1,S.attachment v.1⟩
  else v

@[simp] theorem parent_root : S.parent S.root=S.root := by simp [parent,root]

def blockBound : Nat := (∑ x, S.size x)+1

theorem index_lt_blockBound (v : S.Node) : v.2.val<S.blockBound := by
  have hs : S.size v.1 ≤ ∑ x, S.size x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hv := v.2.isLt
  simp only [blockBound]
  omega

def rank (v : S.Node) : Nat := v.1.val*S.blockBound+v.2.val

/-- Every nonroot concrete parent step strictly decreases a finite natural rank. -/
theorem rank_parent_lt (v : S.Node) (hv : v≠S.root) :
    S.rank (S.parent v)<S.rank v := by
  classical
  unfold parent
  split_ifs with hy hx
  · have hl := (S.localTree v.1).parent_lt v.2 hy
    simp only [rank]
    omega
  · have hl := T.parent_lt v.1 hx
    have hb : (S.attachment v.1).val<S.blockBound :=
      S.index_lt_blockBound ⟨T.parent v.1,S.attachment v.1⟩
    have hm := Nat.mul_le_mul_right S.blockBound (Nat.succ_le_of_lt hl)
    simp only [Nat.succ_mul] at hm
    simp only [rank]
    omega
  · exfalso
    apply hv
    obtain ⟨x,y⟩ := v
    simp only [ne_eq,not_not] at hy hx
    have he : x=(S.root).1 := Fin.ext hx
    cases he
    have hf : y=(S.root).2 := Fin.ext hy
    cases hf
    rfl

noncomputable def nodeEquiv : S.Node ≃ Fin (Fintype.card S.Node) := Fintype.equivFin _

noncomputable def ranked : RankedParent (Fintype.card S.Node) where
  root := S.nodeEquiv S.root
  parent i := S.nodeEquiv (S.parent (S.nodeEquiv.symm i))
  rank i := S.rank (S.nodeEquiv.symm i)
  parent_root := by simp
  rank_lt := by
    intro i hi
    simp only [Equiv.symm_apply_apply]
    apply S.rank_parent_lt
    intro he
    apply hi
    rw [← S.nodeEquiv.apply_symm_apply i,he]

noncomputable def numbered := S.ranked.numbered
noncomputable def tree : RootedTree (Fintype.card S.Node) := S.numbered.tree
noncomputable def label (i : Fin (Fintype.card S.Node)) : S.Node :=
  S.nodeEquiv.symm (S.numbered.label i)
noncomputable def index (v : S.Node) : Fin (Fintype.card S.Node) :=
  S.numbered.index (S.nodeEquiv v)

@[simp] theorem label_index (v : S.Node) : S.label (S.index v)=v := by
  simp only [label,index,RankedParent.Numbered.label_index,Equiv.symm_apply_apply]
@[simp] theorem index_label (i : Fin (Fintype.card S.Node)) : S.index (S.label i)=i := by
  simp only [label,index,Equiv.apply_symm_apply,RankedParent.Numbered.index_label]

theorem exact_parent (i : Fin (Fintype.card S.Node)) :
    S.label (S.tree.parent i)=S.parent (S.label i) := by
  simp only [label,tree,RankedParent.Numbered.parent_exact,ranked,Equiv.symm_apply_apply]

theorem exact_root (i : Fin (Fintype.card S.Node)) (hi : i.val=0) : S.label i=S.root := by
  simp only [label,S.numbered.label_root i hi,ranked,Equiv.symm_apply_apply]

/-- Substitution retains every local node exactly once. -/
theorem node_count : Fintype.card S.Node=∑ x, S.size x := by
  simp only [Node,Fintype.card_sigma,Fintype.card_fin]

#print axioms rank_parent_lt
#print axioms exact_parent
#print axioms node_count
end TreeSubstitution
end StackSorting.GraphWidth.Nested
