import MonotoneElimination

/-! The exact one-loss argument for simultaneous coordinate-zero restrictions.
This is proved for arbitrary unchanged monotone constraints. Applying it to
literal completion still requires the supplied-stack order bridge and exact
old-coordinate/clause constraints; neither is hidden in these definitions. -/
namespace StackSorting.MonotoneElimination
open List

def smallerCount (U : List Nat) (v : Nat) : Nat :=
  (U.filter (fun w => decide (w < v))).length

def ZeroRestriction (i : Nat) : Eligibility :=
  fun U v => v = i → smallerCount U v = 0

def WithZeros (base : Eligibility) (selected : List Nat) : Eligibility :=
  fun U v => base U v ∧ ∀ i ∈ selected, ZeroRestriction i U v

/-- There is only one possible second-smallest token in a finite set. -/
theorem smallerCount_one_unique {U : List Nat} {a b : Nat}
    (ha : a ∈ U) (hb : b ∈ U)
    (hca : smallerCount U a = 1) (hcb : smallerCount U b = 1) : a = b := by
  have cannot_lt : ∀ {x y : Nat}, x ∈ U → y ∈ U →
      smallerCount U x = 1 → smallerCount U y = 1 → ¬ x < y := by
    intro x y hx _ hcx hcy hxy
    have hn : U.filter (fun w => decide (w < x)) ≠ [] := by
      intro he
      simp [smallerCount, he] at hcx
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hn
    have hw' := List.mem_filter.mp hw
    have hwx : w < x := by simpa using hw'.2
    have hsub : [w, x] ⊆ U.filter (fun z => decide (z < y)) := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_filter.mpr ⟨hw'.1, by simp; omega⟩
      · have he : z = x := by simpa using hz
        subst z
        exact List.mem_filter.mpr ⟨hx, by simp [hxy]⟩
    have hnd : ([w, x] : List Nat).Nodup := by simp; omega
    have hlen := hnd.length_le_of_subset hsub
    have hsmall : (U.filter (fun z => decide (z < y))).length = 1 := hcy
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have hab := cannot_lt ha hb hca hcb
  have hba := cannot_lt hb ha hcb hca
  omega

theorem smallerCount_mono {U V : List Nat} {v : Nat}
    (hn : V.Nodup) (hsub : V ⊆ U) : smallerCount V v ≤ smallerCount U v := by
  have hnf : (V.filter (fun w => decide (w < v))).Nodup := hn.filter _
  exact hnf.length_le_of_subset (fun _ h =>
    List.mem_filter.mpr ⟨hsub (List.mem_filter.mp h).1, (List.mem_filter.mp h).2⟩)

/-- The obstruction lemma specialized to lowering selected upper bounds from
one to zero. It derives the simultaneous criterion from separate singleton
criteria, for every finite residual subset, without assuming intersection. -/
theorem everySubset_withZeros
    (base : Eligibility) (U selected : List Nat) (hne : selected ≠ [])
    (hbound : ∀ V, V.Nodup → V ⊆ U →
      ∀ v ∈ selected, base V v → smallerCount V v ≤ 1)
    (hsingle : ∀ i ∈ selected, EverySubset (WithZeros base [i]) U) :
    EverySubset (WithZeros base selected) U := by
  apply everySubset_simultaneous base ZeroRestriction U selected hne
  · intro V hn hsub a ha hbase i hi hloss b hb hbbase j hj hbloss
    have hai : a = i := by
      apply Classical.byContradiction
      intro hne
      exact hloss (fun he => (hne he).elim)
    have hbj : b = j := by
      apply Classical.byContradiction
      intro hne
      exact hbloss (fun he => (hne he).elim)
    have hac : smallerCount V a ≠ 0 := by
      intro he
      exact hloss (fun _ => he)
    have hbc : smallerCount V b ≠ 0 := by
      intro he
      exact hbloss (fun _ => he)
    have hal := hbound V hn hsub a (hai.symm ▸ hi) hbase
    have hbl := hbound V hn hsub b (hbj.symm ▸ hj) hbbase
    exact smallerCount_one_unique ha hb (by omega) (by omega)
  · intro i hi V hn hsub hvne
    obtain ⟨v, hv, hb, hz⟩ := hsingle i hi V hn hsub hvne
    exact ⟨v, hv, hb, hz i (by simp)⟩

#print axioms smallerCount_one_unique
#print axioms everySubset_withZeros
end StackSorting.MonotoneElimination
