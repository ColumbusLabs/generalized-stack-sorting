import ReplacementInsertedAppendix

namespace FiniteFlow.Hypergraph.ReplacementFrame
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}

/-- Construct an actual width-(2k+1) decomposition of every bridge part whose
both boundary identifiers are inserted. Its old vertices are proved to lie in
the old removed-edge appendix union. All inserted boundary vertices appear in
every bag, so both endpoint conditions follow from the construction. -/
noncomputable def insertedInteriorBagPath
    (R : ReplacementFrame old inserted s t removed) (k : Nat)
    (K P : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (old_to_source : ∀ x ∈ R.oldVertices, Nonempty (HWalk old x s))
    (part_support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ K)
    (f g : F)
    (part_region : ∀ x ∈ P, BridgeRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.cut (.inr f)) (.cut (.inr g)) x)
    (D : BagPath (appendixVertices old s t removed) (k+1)) (hD : D.Covers old) :
    {Q : BagPath P (2*k+2) // Q.Covers (ReplacementIncidence old inserted removed) ∧
      ∀ q, q ≤ Q.last → ∀ x ∈ P, ∀ h, inserted x h → x ∈ Q.bag q} := by
  classical
  let W := appendixVertices old s t removed
  have old_part : ∀ x ∈ P, x ∈ R.oldVertices → x ∈ W := by
    intro x hx hxo
    exact (mem_appendixVertices old s t removed x).mpr
      (R.inserted_bridge_old_support x (old_to_source x hxo) f g (part_region x hx))
  have split : (W ∩ P) ∪ (K ∩ P) = P := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).2
      · exact (Finset.mem_inter.mp hx).2
    · intro x hx
      rcases part_support x hx with hxo | hxk
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨old_part x hx hxo,hx⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxk,hx⟩)
  let Q := D.replacementInterior P K small
  have hK : ∀ x h, inserted x h → x ∈ K :=
    fun x h hx => (K_exact x).mp (R.new_support x h hx)
  have hQ := D.replacementInterior_covers P K small removed hD hK
  refine ⟨Q.recast split,Q.recast_covers split hQ,?_⟩
  intro q _ x hx h hxh
  exact D.replacementInterior_boundary P K small q
    (Finset.mem_inter.mpr ⟨hK x h hxh,hx⟩)

end FiniteFlow.Hypergraph.ReplacementFrame
