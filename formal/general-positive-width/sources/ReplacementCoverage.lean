import ReplacementBagSurgery

namespace FiniteFlow.Hypergraph.BagPath
variable {V E F : Type*} [DecidableEq V]
variable {A : Finset V} {k : Nat}

/-- Interior surgery covers entire replacement hyperedges after restriction.
The inserted support assumption is on K itself; the part membership is derived
from the actual new region rather than postulated for the whole inserted edge. -/
theorem replacementInterior_covers (D : BagPath A (k+1)) (part K : Finset V)
    (small : K.card ≤ k+1) {old : V → E → Prop} {inserted : V → F → Prop}
    (removed : E) (hD : D.Covers old) (hK : ∀ x f, inserted x f → x ∈ K) :
    (D.replacementInterior part K small).Covers
      (ReplacementIncidence old inserted removed) := by
  intro e
  cases e with
  | inl e =>
    exact (D.restrict part).augment_covers (K ∩ part) (D.restrict_covers part hD) e.val
  | inr f =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    intro x hx hxf
    have hp : x ∈ part := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).2
      · exact (Finset.mem_inter.mp hx).2
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hK x f hxf,hp⟩)

/-- Appendix surgery covers full old and inserted hyperedges. The old-origin
condition is a vertex-level support condition to be supplied by component
classification, not a pathwidth or decomposition-existence assumption. -/
theorem replacementAppendix_covers (D : BagPath A (k+1)) (K : Finset V)
    (small : K.card ≤ k+1) (seam : ∀ x ∈ K ∩ A, x ∈ D.bag 0)
    {old : V → E → Prop} {inserted : V → F → Prop} (removed : E)
    (hD : D.Covers old) (hK : ∀ x f, inserted x f → x ∈ K)
    (old_origin : ∀ x ∈ K ∪ A, ∀ e, old x e → x ∈ A) :
    (D.replacementAppendix K small seam).Covers
      (ReplacementIncidence old inserted removed) := by
  intro e
  cases e with
  | inl e =>
    obtain ⟨i, hi, he⟩ := hD e.val
    refine ⟨1+i, by change 1+i ≤ 0+1+D.last; omega, ?_⟩
    intro x hx hxe
    change x ∈ if 1+i ≤ 0 then _ else D.bag (1+i-0-1)
    rw [ite_eq_right (by omega),show 1+i-0-1=i by omega]
    exact he x (old_origin x hx e.val hxe) hxe
  | inr f =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    intro x _ hxf
    rw [replacementAppendix_first]
    exact hK x f hxf

end FiniteFlow.Hypergraph.BagPath
