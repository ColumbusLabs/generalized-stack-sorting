import UnequalThreshold
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Card

/-! The exact factorial cardinality of the already-characterized finite
physical-capacity bases. Elements are actual permutations, counted once. -/
namespace StackSorting.Generalized.Unequal
open Finset

/-- The generated basis consists of a fixed leading maximum and every
permutation of the smaller labels. This is a literal finite enumeration. -/
def finiteGeneratedBasis (H : ℕ) : Finset (List ℕ) :=
  (List.range H).permutations.toFinset.map
    ⟨fun tail => H :: tail, by intro a b h; simpa using h⟩

@[simp] theorem mem_finiteGeneratedBasis (H : ℕ) (p : List ℕ) :
    p ∈ finiteGeneratedBasis H ↔ ∃ tail, tail.Perm (List.range H) ∧ p = H :: tail := by
  simp [finiteGeneratedBasis, eq_comm]
  rfl

theorem leading_maximum_perm_iff (H : ℕ) (tail : List ℕ) :
    (H :: tail).Perm (List.range (H+1)) ↔ tail.Perm (List.range H) := by
  have hr : (H :: List.range H).Perm (List.range (H+1)) := by
    rw [List.range_succ]
    simpa using (List.perm_append_comm (l₁ := [H]) (l₂ := List.range H))
  constructor
  · intro h
    exact (List.perm_cons H).mp (h.trans hr.symm)
  · intro h
    exact (h.cons H).trans hr

theorem finiteGeneratedBasis_exact {r s H : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ max r s + 1) (p : List ℕ) :
    p ∈ finiteGeneratedBasis H ↔ MinimalForbiddenH r s H (H+1) p := by
  rw [finite_basis_gen hr hs hH, mem_finiteGeneratedBasis]
  constructor
  · rintro ⟨tail, ht, rfl⟩
    exact ⟨(leading_maximum_perm_iff H tail).mpr ht, rfl, tail, rfl⟩
  · rintro ⟨hp, _, tail, rfl⟩
    exact ⟨tail, (leading_maximum_perm_iff H tail).mp hp, rfl⟩

theorem finiteGeneratedBasis_card (H : ℕ) : (finiteGeneratedBasis H).card = H.factorial := by
  rw [finiteGeneratedBasis, Finset.card_map,
    List.toFinset_card_of_nodup (List.nodup_permutations _ (List.nodup_range (n := H))),
    List.length_permutations, List.length_range]

/-- Sorting uses the proved involutive inverse orientation. -/
def finiteSortableBasis (H : ℕ) : Finset (List ℕ) :=
  (finiteGeneratedBasis H).image inv

theorem finiteSortableBasis_exact {r s H : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ max r s + 1) (p : List ℕ) :
    p ∈ finiteSortableBasis H ↔ SortMinimalH r s H (H+1) p := by
  simp only [finiteSortableBasis, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ((finiteGeneratedBasis_exact hr hs hH q).mp hq).toSort
  · intro hp
    refine ⟨inv p, (finiteGeneratedBasis_exact hr hs hH _).mpr hp.toGen, ?_⟩
    exact inv_inv hp.1

theorem finiteSortableBasis_card (H : ℕ) : (finiteSortableBasis H).card = H.factorial := by
  rw [finiteSortableBasis, Finset.card_image_iff.mpr, finiteGeneratedBasis_card]
  intro p hp q hq h
  obtain ⟨tp, htp, rfl⟩ := (mem_finiteGeneratedBasis H p).mp hp
  obtain ⟨tq, htq, rfl⟩ := (mem_finiteGeneratedBasis H q).mp hq
  have hpp := (leading_maximum_perm_iff H tp).mpr htp
  have hqq := (leading_maximum_perm_iff H tq).mpr htq
  have hh := congrArg inv h
  simpa only [inv_inv hpp, inv_inv hqq] using hh

/-- There are no basis elements of other lengths in the finite regime. -/
theorem finiteGeneratedBasis_all_sizes {r s H : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ max r s + 1) (p : List ℕ) :
    (∃ n, MinimalForbiddenH r s H n p) ↔ p ∈ finiteGeneratedBasis H := by
  constructor
  · rintro ⟨n, hp⟩
    have hn := ((finite_basis_gen hr hs hH).mp hp).2.1
    subst n
    exact (finiteGeneratedBasis_exact hr hs hH p).mpr hp
  · intro hp
    exact ⟨H+1, (finiteGeneratedBasis_exact hr hs hH p).mp hp⟩

theorem finiteSortableBasis_all_sizes {r s H : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ max r s + 1) (p : List ℕ) :
    (∃ n, SortMinimalH r s H n p) ↔ p ∈ finiteSortableBasis H := by
  constructor
  · rintro ⟨n, hp⟩
    have hn := ((finite_basis_sort hr hs hH).mp hp).2.1
    subst n
    exact (finiteSortableBasis_exact hr hs hH p).mpr hp
  · intro hp
    exact ⟨H+1, (finiteSortableBasis_exact hr hs hH p).mp hp⟩

#print axioms finiteGeneratedBasis_exact
#print axioms finiteGeneratedBasis_card
#print axioms finiteSortableBasis_exact
#print axioms finiteSortableBasis_card
#print axioms finiteGeneratedBasis_all_sizes
#print axioms finiteSortableBasis_all_sizes
end StackSorting.Generalized.Unequal
