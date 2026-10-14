import BagPathRestriction
import BagPathConcatenation

namespace FiniteFlow.Hypergraph.BagPath
variable {V E : Type*} [DecidableEq V] {A B C : Finset V} {w : Nat}

/-- Three actual pieces with disjoint exterior cores and endpoint-compatible
middle overlaps assemble without increasing the bag bound. -/
def triple (D : BagPath A w) (M : BagPath B w) (R : BagPath C w)
    (outer_disjoint : ∀ x, x ∈ A → x ∈ C → False)
    (left_seam : ∀ x ∈ A ∩ B, x ∈ D.bag D.last ∧ x ∈ M.bag 0)
    (right_seam : ∀ x ∈ B ∩ C, x ∈ M.bag M.last ∧ x ∈ R.bag 0) :
    BagPath ((A ∪ B) ∪ C) w :=
  (D.concat M left_seam).concat R (by
    intro x hx
    obtain ⟨hxAB,hxC⟩ := Finset.mem_inter.mp hx
    have hxB : x ∈ B := (Finset.mem_union.mp hxAB).elim
      (fun hxA => (outer_disjoint x hxA hxC).elim) id
    obtain ⟨hM,hR⟩ := right_seam x (Finset.mem_inter.mpr ⟨hxB,hxC⟩)
    exact ⟨by simpa only [concat_last] using hM,hR⟩)

@[simp] theorem triple_first (D : BagPath A w) (M : BagPath B w) (R : BagPath C w)
    (outer_disjoint) (left_seam) (right_seam) :
    (D.triple M R outer_disjoint left_seam right_seam).bag 0 = D.bag 0 := by
  simp only [triple,concat_first]

@[simp] theorem triple_last (D : BagPath A w) (M : BagPath B w) (R : BagPath C w)
    (outer_disjoint) (left_seam) (right_seam) :
    (D.triple M R outer_disjoint left_seam right_seam).bag
      (D.triple M R outer_disjoint left_seam right_seam).last = R.bag R.last := by
  simp only [triple,concat_last]

/-- Every whole edge is localized to one of the three pieces; overlapping
middle separators preserve that localization under both concatenations. -/
theorem triple_covers (D : BagPath A w) (M : BagPath B w) (R : BagPath C w)
    (outer_disjoint) (left_seam) (right_seam) {inc : V → E → Prop}
    (hD : D.Covers inc) (hM : M.Covers inc) (hR : R.Covers inc)
    (localized : ∀ e,
      (∀ x ∈ (A ∪ B) ∪ C, inc x e → x ∈ A) ∨
      (∀ x ∈ (A ∪ B) ∪ C, inc x e → x ∈ B) ∨
      (∀ x ∈ (A ∪ B) ∪ C, inc x e → x ∈ C)) :
    (D.triple M R outer_disjoint left_seam right_seam).Covers inc := by
  have hDM : (D.concat M left_seam).Covers inc := by
    apply D.concat_covers M left_seam hD hM
    intro e
    rcases localized e with h | h | h
    · exact Or.inl (fun x hx hxe => h x (Finset.mem_union_left _ hx) hxe)
    · exact Or.inr (fun x hx hxe => h x (Finset.mem_union_left _ hx) hxe)
    · apply Or.inr
      intro x hx hxe
      have hxC := h x (Finset.mem_union_left _ hx) hxe
      exact (Finset.mem_union.mp hx).elim
        (fun hxA => (outer_disjoint x hxA hxC).elim) id
  apply (D.concat M left_seam).concat_covers R _ hDM hR
  intro e
  rcases localized e with h | h | h
  · exact Or.inl (fun x hx hxe => Finset.mem_union_left _ (h x hx hxe))
  · exact Or.inl (fun x hx hxe => Finset.mem_union_right _ (h x hx hxe))
  · exact Or.inr h

end FiniteFlow.Hypergraph.BagPath
