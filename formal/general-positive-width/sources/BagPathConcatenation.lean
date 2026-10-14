import HypergraphBagPath

namespace FiniteFlow.Hypergraph.BagPath
variable {V E : Type*} [DecidableEq V]
variable {A B : Finset V} {w : Nat}

/-- Concatenation uses every old bag in its original order. The shared vertices
must occur at the adjoining endpoints; that condition is proved from the actual
cutedge-component structure when this operation is applied to a network. -/
def concat (D : BagPath A w) (F : BagPath B w)
    (seam : ∀ x ∈ A ∩ B, x ∈ D.bag D.last ∧ x ∈ F.bag 0) : BagPath (A ∪ B) w where
  last := D.last + 1 + F.last
  bag := fun i => if i ≤ D.last then D.bag i else F.bag (i-D.last-1)
  inside := by
    intro i hi x hx
    by_cases h : i ≤ D.last
    · simp only [ite_eq_left h] at hx
      exact Finset.mem_union_left _ (D.inside i h hx)
    · simp only [ite_eq_right h] at hx
      exact Finset.mem_union_right _ (F.inside _ (by omega) hx)
  bounded := by
    intro i hi
    by_cases h : i ≤ D.last
    · simp only [ite_eq_left h]
      exact D.bounded i h
    · simp only [ite_eq_right h]
      exact F.bounded _ (by omega)
  vertex := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, hxi⟩ := D.vertex x hx
      exact ⟨i, by omega, by simpa only [ite_eq_left hi] using hxi⟩
    · obtain ⟨i, hi, hxi⟩ := F.vertex x hx
      refine ⟨D.last+1+i, by omega, ?_⟩
      have h : ¬ D.last+1+i ≤ D.last := by omega
      simpa only [ite_eq_right h, show D.last+1+i-D.last-1=i by omega] using hxi
  interval := by
    intro i j k hij hjk hk x hxi hxk
    by_cases hleft : k ≤ D.last
    · have hi : i ≤ D.last := by omega
      have hj : j ≤ D.last := by omega
      simp only [ite_eq_left hi] at hxi
      simp only [ite_eq_left hleft] at hxk
      simp only [ite_eq_left hj]
      exact D.interval i j k hij hjk hleft x hxi hxk
    · by_cases hright : i ≤ D.last
      · simp only [ite_eq_left hright] at hxi
        simp only [ite_eq_right hleft] at hxk
        have hxA := D.inside i hright hxi
        have hxB := F.inside (k-D.last-1) (by omega) hxk
        obtain ⟨hl, hr⟩ := seam x (Finset.mem_inter.mpr ⟨hxA,hxB⟩)
        by_cases hj : j ≤ D.last
        · simp only [ite_eq_left hj]
          exact D.interval i j D.last hij hj le_rfl x hxi hl
        · simp only [ite_eq_right hj]
          exact F.interval 0 (j-D.last-1) (k-D.last-1)
            (Nat.zero_le _) (by omega) (by omega) x hr hxk
      · have hj : ¬ j ≤ D.last := by omega
        simp only [ite_eq_right hright] at hxi
        simp only [ite_eq_right hleft] at hxk
        simp only [ite_eq_right hj]
        exact F.interval (i-D.last-1) (j-D.last-1) (k-D.last-1)
          (by omega) (by omega) (by omega) x hxi hxk

theorem concat_first (D : BagPath A w) (F : BagPath B w) (seam) :
    (D.concat F seam).bag 0 = D.bag 0 := by simp [concat]

theorem concat_last (D : BagPath A w) (F : BagPath B w) (seam) :
    (D.concat F seam).bag (D.concat F seam).last = F.bag F.last := by
  change (if D.last+1+F.last ≤ D.last then D.bag (D.last+1+F.last)
    else F.bag (D.last+1+F.last-D.last-1)) = F.bag F.last
  rw [ite_eq_right (by omega)]
  congr 1
  omega

/-- Entire hyperedges must be localized to one side. Pairwise edge coverage
would not suffice for this hypergraph operation. -/
theorem concat_covers (D : BagPath A w) (F : BagPath B w) (seam)
    {inc : V → E → Prop} (hD : D.Covers inc) (hF : F.Covers inc)
    (localized : ∀ e, (∀ x ∈ A ∪ B, inc x e → x ∈ A) ∨
      (∀ x ∈ A ∪ B, inc x e → x ∈ B)) : (D.concat F seam).Covers inc := by
  intro e
  rcases localized e with h | h
  · obtain ⟨i, hi, he⟩ := hD e
    refine ⟨i, by change i ≤ D.last+1+F.last; omega, ?_⟩
    intro x hx hxe
    change x ∈ if i ≤ D.last then D.bag i else _
    rw [ite_eq_left hi]
    exact he x (h x hx hxe) hxe
  · obtain ⟨i, hi, he⟩ := hF e
    refine ⟨D.last+1+i, by change D.last+1+i ≤ D.last+1+F.last; omega, ?_⟩
    intro x hx hxe
    change x ∈ if D.last+1+i ≤ D.last then _ else F.bag (D.last+1+i-D.last-1)
    rw [ite_eq_right (by omega),show D.last+1+i-D.last-1=i by omega]
    exact he x (h x hx hxe) hxe

end FiniteFlow.Hypergraph.BagPath
