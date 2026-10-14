import MultiMarginSpanning
import SubstitutionAncestry

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- Root-separator semantics over a genuine numbered tree, including the
actual root condition and the allowed-vertex guards of deleted walks. -/
def TreeRootSeparator {q : Nat} (U : RootedTree q) (x y : Fin q) : Prop :=
  ∀ r, r.val=0 → Walk (TreeAdj U) (fun _ => True) y r →
    ¬ Walk (TreeAdj U) (fun z => z≠x) y r

theorem tree_root_ancestor {q : Nat} (U : RootedTree q) (r : Fin q) (hr : r.val=0) (y : Fin q) :
    Ancestor U r y :=
  TreeAncestry.ancestor_of_walk_minimum (tree_connected U r y)
    (fun z _ => by rw [hr]; exact Nat.zero_le _) (.refl _)

/-- Ancestry is recovered from root reachability and vertex deletion; a
binary parent relation is not part of this characterization's input. -/
theorem tree_rootSeparator_iff {q : Nat} (U : RootedTree q) (x y : Fin q) :
    TreeRootSeparator U x y ↔ Ancestor U x y := by
  constructor
  · intro h
    by_contra hn
    let r : Fin q := ⟨0,by have := y.isLt; omega⟩
    have hp : Walk (TreeAdj U) (fun z => z≠x) r y :=
      ancestor_chain_walk (tree_root_ancestor U r rfl y)
        (fun z _ hzy he => hn (he ▸ hzy))
    have hr := hp.reverse (treeAdj_symm U)
    exact h r rfl (hr.mono (fun _ _ => trivial)) hr
  · intro h r hr _ hp
    by_cases he : x=r
    · exact hp.finish he.symm
    · have hout : ¬ Ancestor U x r := by
        intro ha
        have hi := ha.val_le
        exact he (Fin.ext (by omega))
      exact (TreeAncestry.subtree_entry (hp.reverse (treeAdj_symm U)) hout h) rfl

namespace Encoding
variable (s : Sane D) (ht : 0<t)

/-- Actual selected node representatives, one incoming root per original
margin. This particular permitted choice makes component recovery direct. -/
def Representative (v : Fin n) : Prop := ∃ x, v=entry s x

theorem entry_injective : Function.Injective (entry s) := by
  intro x y he
  exact (entry_mem s x).symm.trans ((congrArg (introductionNode D) he).trans (entry_mem s y))

theorem representative_unique (x : Fin t) : ∃! v, Representative s v ∧ Margin D x v := by
  refine ⟨entry s x,⟨⟨x,rfl⟩,entry_mem s x⟩,?_⟩
  rintro v ⟨⟨y,rfl⟩,hv⟩
  have he : y=x := (entry_mem s y).symm.trans hv
  exact congrArg (entry s) he

noncomputable def numberedVertex (v : Fin n) : Fin (Fintype.card (Node s ht)) :=
  (substitution s ht).index (index s ht v)

def UnionAncestor (u v : Fin n) : Prop :=
  Ancestor (substitution s ht).tree (numberedVertex s ht u) (numberedVertex s ht v)

theorem numbered_entry (x : Fin t) :
    numberedVertex s ht (entry s x)=(substitution s ht).index ((substitution s ht).localRoot x) := by
  unfold numberedVertex
  rw [← vertex_localRoot s ht x,index_vertex]

/-- Recovered components are exactly the original introduction components. -/
theorem component_exact (x : Fin t) (v : Fin n) :
    UnionAncestor s ht (entry s x) v ↔ IntroductionComponent D x v := by
  unfold UnionAncestor
  rw [numbered_entry]
  exact ((substitution s ht).outer_ancestor_iff x (index s ht v)).symm

def RecoveredMargin (x v : Fin n) : Prop := Walk (M s ht) (fun _ => True) x v

theorem margin_exact (x : Fin t) (v : Fin n) :
    RecoveredMargin s ht (entry s x) v ↔ Margin D x v := by
  rw [RecoveredMargin,M_component_exact,entry_mem s x]
  exact eq_comm

/-- Parent comes from a selected crossing edge directed toward the root,
followed by membership in the parent's M-component. No parent atom is supplied. -/
def RecoveredParent (child parent : Fin n) : Prop :=
  ∃ w, K s child w ∧ UnionAncestor s ht w child ∧ RecoveredMargin s ht parent w

theorem unionAncestor_outer {u v} (h : UnionAncestor s ht u v) :
    Ancestor T (introductionNode D u) (introductionNode D v) := by
  have ho := (substitution s ht).ancestor_outer h
  simpa only [numberedVertex,TreeSubstitution.label_index,index] using ho

/-- The actual bridge's upper endpoint lies above its lower endpoint. -/
theorem bridge_ancestor (x : Fin t) (hx : x.val≠0) :
    UnionAncestor s ht (bridge s x hx).1 (bridge s x hx).2 := by
  let S := substitution s ht
  have he : numberedVertex s ht (bridge s x hx).2=S.index (S.localRoot x) := by
    have he' : entry s x=(bridge s x hx).2 := by simp [entry,hx]
    rw [← he',numbered_entry]
  have hp : numberedVertex s ht (bridge s x hx).1=S.index ⟨T.parent x,S.attachment x⟩ := by
    unfold numberedVertex
    rw [← vertex_attachment s ht x hx,index_vertex]
  change Ancestor S.tree _ _
  rw [he,hp]
  have hn : (S.index (S.localRoot x)).val≠0 := by
    intro hz
    have heq := (S.index_zero_iff _).mp hz
    exact hx (congrArg (fun a : S.Node => a.1.val) heq)
  apply Ancestor.step hn
  rw [S.parent_index,S.parent_localRoot x hx]
  exact .refl _

theorem parent_exact (x y : Fin t) :
    RecoveredParent s ht (entry s x) (entry s y) ↔ x.val≠0 ∧ T.parent x=y := by
  constructor
  · rintro ⟨w,⟨z,hz,h⟩,ha,hm⟩
    have hyw := (margin_exact s ht y w).mp hm
    have hb := bridge_spec s z hz
    rcases h with ⟨hx,hw⟩ | ⟨hw,hx⟩
    · have hyz : y=z := hyw.symm.trans (hw.symm ▸ hb.2.1)
      have hxz : x=T.parent z := (entry_mem s x).symm.trans (hx.symm ▸ hb.1)
      have ho := unionAncestor_outer s ht ha
      rw [hyw,entry_mem s x,hyz,hxz] at ho
      have hi := ho.val_le
      have hl := T.parent_lt z hz
      omega
    · have hxz : x=z := (entry_mem s x).symm.trans (hx.symm ▸ hb.2.1)
      have hyp : y=T.parent z := hyw.symm.trans (hw.symm ▸ hb.1)
      exact ⟨hxz.symm ▸ hz,by rw [hxz,hyp]⟩
  · rintro ⟨hx,rfl⟩
    refine ⟨(bridge s x hx).1,⟨x,hx,Or.inr ⟨rfl,?_⟩⟩,?_,?_⟩
    · simp [entry,hx]
    · have h := bridge_ancestor s ht x hx
      simpa [entry,hx] using h
    · exact (margin_exact s ht _ _).mpr (bridge_spec s x hx).1

/-- Only original G adjacency occurs in the reconstructed boundary formula. -/
def RecoveredBag (x v : Fin n) : Prop :=
  RecoveredMargin s ht x v ∨ (¬ UnionAncestor s ht x v ∧
    ∃ u, UnionAncestor s ht x u ∧ G.Adj v u)

theorem bag_exact (x : Fin t) (v : Fin n) :
    RecoveredBag s ht (entry s x) v ↔ v ∈ D.bag x := by
  unfold RecoveredBag
  simp only [margin_exact,component_exact]
  exact (bag_boundary_exact s x v).symm

#print axioms tree_rootSeparator_iff
#print axioms representative_unique
#print axioms component_exact
#print axioms parent_exact
#print axioms bag_exact
end Encoding
end StackSorting.GraphWidth.MultiMargin
