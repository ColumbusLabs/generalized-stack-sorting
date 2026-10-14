import SaneSingletonNormalization
import SubstitutedParentTree
import FiniteIndexTreeAdapter

namespace StackSorting.GraphWidth.MarginalA2.RootedLocal
open FinitePort SameVertexForest ConnectedConeNormalization
variable {n : Nat} {G : Graph n}

/-- Exactly one artificial empty root plus one node per actual margin vertex. -/
abbrev Node (n : Nat) := Option (Fin n)

noncomputable def parent (O : RankedOrder n) : Node n → Node n
  | none => none
  | some v => if O.parent v=v then none else some (O.parent v)

def rank (O : RankedOrder n) : Node n → Nat
  | none => 0 | some v => O.rank v+1

theorem rank_parent_lt (O : RankedOrder n) (v : Node n) (hv : v≠none) :
    rank O (parent O v)<rank O v := by
  classical
  cases v with
  | none => exact (hv rfl).elim
  | some v =>
    simp only [parent]
    split_ifs with h
    · simp [rank]
    · simpa only [rank,Nat.add_lt_add_iff_right] using O.parent_rank_lt h

noncomputable def nodeEquiv (n : Nat) : Node n ≃ Fin (Fintype.card (Node n)) := Fintype.equivFin _

noncomputable def ranked (O : RankedOrder n) : RankedParent (Fintype.card (Node n)) where
  root := nodeEquiv n none
  parent i := nodeEquiv n (parent O ((nodeEquiv n).symm i))
  rank i := rank O ((nodeEquiv n).symm i)
  parent_root := by simp [parent]
  rank_lt := by
    intro i hi
    simp only [Equiv.symm_apply_apply]
    apply rank_parent_lt
    intro he
    apply hi
    rw [←(nodeEquiv n).apply_symm_apply i,he]

noncomputable def numbered (O : RankedOrder n) := (ranked O).numbered
noncomputable def tree (O : RankedOrder n) : RootedTree (Fintype.card (Node n)) := (numbered O).tree
noncomputable def label (O : RankedOrder n) (i : Fin (Fintype.card (Node n))) : Node n :=
  (nodeEquiv n).symm ((numbered O).label i)
noncomputable def index (O : RankedOrder n) (v : Node n) : Fin (Fintype.card (Node n)) :=
  (numbered O).index (nodeEquiv n v)

@[simp] theorem label_index (O : RankedOrder n) (v : Node n) : label O (index O v)=v := by
  simp only [label,index,RankedParent.Numbered.label_index,Equiv.symm_apply_apply]
@[simp] theorem index_label (O : RankedOrder n) (i : Fin (Fintype.card (Node n))) : index O (label O i)=i := by
  simp only [label,index,Equiv.apply_symm_apply,RankedParent.Numbered.index_label]

theorem label_injective (O : RankedOrder n) : Function.Injective (label O) := by
  intro i j h
  have hi := congrArg (index O) h
  simpa only [index_label] using hi

theorem exact_parent (O : RankedOrder n) (i : Fin (Fintype.card (Node n))) :
    label O ((tree O).parent i)=parent O (label O i) := by
  simp only [label,tree,RankedParent.Numbered.parent_exact,ranked,Equiv.symm_apply_apply]

theorem exact_root (O : RankedOrder n) (i : Fin (Fintype.card (Node n))) (hi : i.val=0) :
    label O i=none := by
  simp only [label,(numbered O).label_root i hi,ranked,Equiv.symm_apply_apply]

theorem parent_index (O : RankedOrder n) (v : Node n) :
    (tree O).parent (index O v)=index O (parent O v) := by
  apply label_injective O
  rw [exact_parent,label_index,label_index]

theorem some_index_nonzero (O : RankedOrder n) (v : Fin n) : (index O (some v)).val≠0 := by
  intro h
  have he := exact_root O _ h
  rw [label_index] at he
  cases he

theorem old_edge (O : RankedOrder n) {u v : Fin n} (h : ParentAdj O u v) :
    TreeAdj (tree O) (index O (some u)) (index O (some v)) := by
  classical
  rcases h with ⟨hn,hp⟩ | ⟨hn,hp⟩
  · refine Or.inl ⟨some_index_nonzero O u,?_⟩
    rw [parent_index]
    simp only [parent]
    rw [ite_eq_right hn,hp]
  · refine Or.inr ⟨some_index_nonzero O v,?_⟩
    rw [parent_index]
    simp only [parent]
    rw [ite_eq_right hn,hp]

noncomputable def bag (F : ForestDecomposition G) (i : Fin (Fintype.card (Node n))) : List (Fin n) :=
  match label F.order i with | none => [] | some v => (F.bag v).toList

/-- Rooting adds no vertex occurrence and no new bag content. The original
forest running paths are retained verbatim inside the enlarged tree. -/
noncomputable def decomposition (F : ForestDecomposition G) : Decomposition G (tree F.order) where
  bag := bag F
  nodup i := by
    cases h : label F.order i with
    | none => simp [bag,h]
    | some v => simpa only [bag,h] using (F.bag v).nodup_toList
  vertex u := by
    obtain ⟨v,hv⟩ := F.vertex u
    exact ⟨index F.order (some v),by simpa [bag] using hv⟩
  edge := by
    intro u v huv
    obtain ⟨w,hu,hv⟩ := F.edge huv
    exact ⟨index F.order (some w),by simpa [bag] using hu,by simpa [bag] using hv⟩
  running := by
    intro u i j hi hj
    cases li : label F.order i with
    | none => simp [bag,li] at hi
    | some v => cases lj : label F.order j with
      | none => simp [bag,lj] at hj
      | some w =>
        have hv : u∈F.bag v := by simpa [bag,li] using hi
        have hw : u∈F.bag w := by simpa [bag,lj] using hj
        have h := IndexTreeAdapter.map_guarded (B := TreeAdj (tree F.order))
          (P := fun z => u∈F.bag z) (Q := fun z => u∈bag F z)
          (fun z => index F.order (some z)) (fun _ _ h => old_edge F.order h)
          (fun z hz => by simpa [bag] using hz) (F.running hv hw)
        have hli : index F.order (some v)=i := by rw [←li,index_label]
        have hlj : index F.order (some w)=j := by rw [←lj,index_label]
        simpa only [hli,hlj] using h

theorem decomposition_bound (F : ForestDecomposition G) {b : Nat}
    (hb : ∀ v, (F.bag v).card≤b) : (decomposition F).BagBound b := by
  intro i
  change (bag F i).length≤b
  cases h : label F.order i with
  | none => simp [bag,h]
  | some v => simpa [bag,h] using hb v

theorem node_count (n : Nat) : Fintype.card (Node n)=n+1 := by simp [Node]

theorem empty_root_bag (F : ForestDecomposition G) : (decomposition F).bag (index F.order none)=[] := by
  simp [decomposition,bag]

theorem original_node_bag (F : ForestDecomposition G) (v : Fin n) :
    (decomposition F).bag (index F.order (some v))=(F.bag v).toList := by
  simp [decomposition,bag]

#print axioms rank_parent_lt
#print axioms exact_parent
#print axioms decomposition
#print axioms decomposition_bound
#print axioms node_count
end StackSorting.GraphWidth.MarginalA2.RootedLocal
