import BagPathConcatenation

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [DecidableEq V]

/-- Replacement deletes one old identifier and tags all inserted identifiers.
Parallel old/new edges with identical incidence sets remain distinct. -/
def ReplacementIncidence (old : V → E → Prop) (inserted : V → F → Prop)
    (removed : E) : V → ({e : E // e ≠ removed} ⊕ F) → Prop
  | x, .inl e => old x e.val
  | x, .inr f => inserted x f

namespace BagPath
variable {A K : Finset V} {w k : Nat}

/-- The actual replacement incidence relation is covered after adding every
inserted vertex to every old bag. This proves whole-hyperedge coverage. -/
theorem replacement_augment_covers (D : BagPath A w)
    {old : V → E → Prop} {inserted : V → F → Prop} (removed : E)
    (hD : D.Covers old) (hK : ∀ x f, inserted x f → x ∈ K) :
    (D.augment K).Covers (ReplacementIncidence old inserted removed) := by
  intro e
  cases e with
  | inl e =>
    obtain ⟨i, hi, he⟩ := hD e.val
    refine ⟨i, hi, ?_⟩
    intro x hx hxe
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (he x hx hxe)
    · exact Finset.mem_union_right _ hx
  | inr f =>
    exact ⟨0, Nat.zero_le _, fun x _ hxf => Finset.mem_union_right _ (hK x f hxf)⟩

/-- Interior replacement blocks have bags of size at most 2k+2, obtained by
restriction followed by actual insertion of K vertices in every bag. -/
def replacementInterior (D : BagPath A (k+1)) (part K : Finset V)
    (small : K.card ≤ k+1) : BagPath ((A ∩ part) ∪ (K ∩ part)) (2*k+2) :=
  (D.restrict part).augmentThin k (K ∩ part)
    ((Finset.card_le_card Finset.inter_subset_left).trans small)

/-- Prepending a small replacement bag preserves the k+1 bound when all overlap
vertices are in the first old bag. This is the appendix operation of Lemma 5.8. -/
def replacementAppendix (D : BagPath A (k+1)) (K : Finset V)
    (small : K.card ≤ k+1)
    (seam : ∀ x ∈ K ∩ A, x ∈ D.bag 0) : BagPath (K ∪ A) (k+1) :=
  ((single K).weaken small).concat D (by
    intro x hx
    exact ⟨(Finset.mem_inter.mp hx).1,seam x hx⟩)

theorem replacementAppendix_first (D : BagPath A (k+1)) (K : Finset V)
    (small : K.card ≤ k+1) (seam) :
    (D.replacementAppendix K small seam).bag 0 = K := by
  exact concat_first _ _ _

/-- Endpoint control for all interior bridge pieces is obtained by construction. -/
theorem replacementInterior_boundary (D : BagPath A (k+1)) (part K : Finset V)
    (small : K.card ≤ k+1) (i : Nat) :
    K ∩ part ⊆ (D.replacementInterior part K small).bag i :=
  Finset.subset_union_right

end BagPath
end FiniteFlow.Hypergraph
