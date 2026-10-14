import IntroductionForestOrder
import FiniteEarlierColoring

namespace StackSorting.GraphWidth
open FinitePort
attribute [local instance] Classical.propDecidable
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- Two distinct original vertices share an actual bag. This is the genuine
completion of the supplied decomposition, not merely original adjacency. -/
def BagConflict (D : Decomposition G T) (u v : Fin n) : Prop :=
  u≠v ∧ ∃ x, u∈D.bag x ∧ v∈D.bag x

theorem introductionRank_injective (D : Decomposition G T) :
    Function.Injective (introductionRank D) := by
  intro u v h
  apply Fin.ext
  have hm := congrArg (fun z => z % n) h
  simpa [introductionRank,Nat.add_mod,Nat.mod_eq_of_lt u.isLt,
    Nat.mod_eq_of_lt v.isLt] using hm

/-- Every earlier conflicting vertex already occurs in the new vertex's
introduction bag, including conflicts induced by adhesion clique completion. -/
theorem earlier_bagConflict_mem (D : Decomposition G T) {u v : Fin n}
    (hr : introductionRank D u < introductionRank D v) (hc : BagConflict D u v) :
    u∈D.bag (introductionNode D v) := by
  obtain ⟨x,hux,hvx⟩ := hc.2
  have hu := introduction_ancestor D hux
  have hv := introduction_ancestor D hvx
  have huv : Ancestor T (introductionNode D u) (introductionNode D v) := by
    rcases TreeAncestry.comparable hu hv with h | h
    · exact h
    · by_cases he : introductionNode D u=introductionNode D v
      · exact he ▸ Ancestor.refl _
      · have rev := introductionEarlier_rank_lt D (u:=v) (v:=u) ⟨h,Or.inl (Ne.symm he)⟩
        omega
  exact TreeAncestry.walk_convex (T:=T) (P:=fun a => u∈D.bag a)
    (D.running (introduction_spec D u).1 hux) huv hv

theorem earlier_bagConflict_card_lt (D : Decomposition G T) {W : Nat}
    (hb : D.BagBound W) (v : Fin n) :
    (Finset.univ.filter (fun u => introductionRank D u < introductionRank D v ∧
      BagConflict D u v)).card < W := by
  classical
  let S := Finset.univ.filter (fun u => introductionRank D u < introductionRank D v ∧
    BagConflict D u v)
  have hv : v∉S := by simp [S]
  have hsub : insert v S ⊆ (D.bag (introductionNode D v)).toFinset := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact List.mem_toFinset.mpr (introduction_spec D _).1
    · have h := (Finset.mem_filter.mp hu).2
      exact List.mem_toFinset.mpr (earlier_bagConflict_mem D h.1 h.2)
  have hcard := (Finset.card_le_card hsub).trans
    ((List.toFinset_card_le _).trans (hb (introductionNode D v)))
  rw [Finset.card_insert_of_notMem hv] at hcard
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self S.card) hcard

/-- An actual fixed finite coloring separates every supplied bag. Empty
original graphs and zero palettes are handled by the finite greedy theorem. -/
theorem exists_bag_coloring (D : Decomposition G T) {W : Nat} (hb : D.BagBound W) :
    ∃ color : Fin n → Fin W, ∀ x u v, u∈D.bag x → v∈D.bag x →
      u≠v → color u≠color v := by
  obtain ⟨f,hf⟩ := FiniteEarlierColoring.exists_coloring (introductionRank D)
    (introductionRank_injective D) (BagConflict D)
    (fun _ _ h => ⟨h.1.symm,by obtain ⟨x,hu,hv⟩ := h.2; exact ⟨x,hv,hu⟩⟩)
    (fun _ h => h.1 rfl) W (earlier_bagConflict_card_lt D hb)
  exact ⟨f,fun x u v hu hv hne => hf u v ⟨hne,x,hu,hv⟩⟩

/-- Any family of actual bag subsets inherits the same color separation.
The future contracted-adhesion application must supply this containment. -/
theorem exists_inherited_adhesion_coloring (D : Decomposition G T) {W : Nat}
    (hb : D.BagBound W) {A : Type} (adhesion : A → Fin n → Prop)
    (contained : ∀ a, ∃ x, ∀ v, adhesion a v → v∈D.bag x) :
    ∃ color : Fin n → Fin W, ∀ a u v, adhesion a u → adhesion a v →
      u≠v → color u≠color v := by
  obtain ⟨color,hc⟩ := exists_bag_coloring D hb
  refine ⟨color,?_⟩
  intro a u v hu hv hne
  obtain ⟨x,hx⟩ := contained a
  exact hc x u v (hx u hu) (hx v hv) hne

#print axioms exists_bag_coloring
#print axioms exists_inherited_adhesion_coloring
end StackSorting.GraphWidth
