import GeneralizedGeneratedDisplacement

/-! Genuine zero-based ordinary permutation inversion and its exact orientation
bridge in the existing symbol-oblivious literal generalized stack semantics. -/
namespace StackSorting.Generalized
open List

/-- For a permutation, value v in the inverse is the position of v in the
original. The total definition is used as a permutation only under range-Perm. -/
def inversePermutation (p : List Nat) : List Nat := (List.range p.length).map p.idxOf

@[simp] theorem inversePermutation_length (p : List Nat) : (inversePermutation p).length = p.length := by
  simp [inversePermutation]

theorem map_idxOf_self {p : List Nat} (hn : p.Nodup) : p.map p.idxOf = List.range p.length := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hi' : i < p.length := by simpa using hi
  simpa only [List.getElem_map, List.getElem_range] using hn.idxOf_getElem i hi'

theorem inversePermutation_perm {n : Nat} {p : List Nat} (hp : p.Perm (List.range n)) :
    (inversePermutation p).Perm (List.range n) := by
  have hn := hp.nodup_iff.mpr List.nodup_range
  have hlen : p.length = n := by simpa using hp.length_eq
  have h := hp.map p.idxOf
  rw [map_idxOf_self hn, hlen] at h
  simpa only [inversePermutation, hlen] using h.symm

theorem inversePermutation_getElem {p : List Nat} {i : Nat} (hi : i < p.length) :
    (inversePermutation p)[i]'(by simpa using hi) = p.idxOf i := by
  simp [inversePermutation]

/-- Inverse lookup at the original value returns its exact original index. -/
theorem inversePermutation_getElem_value {n i : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) (hi : i < p.length) :
    ∃ hv : p[i] < (inversePermutation p).length, (inversePermutation p)[p[i]]'hv = i := by
  have hn := hp.nodup_iff.mpr List.nodup_range
  have hlen : p.length = n := by simpa using hp.length_eq
  have hv : p[i] < p.length := by
    rw [hlen]
    exact List.mem_range.mp (hp.mem_iff.mp (List.getElem_mem hi))
  refine ⟨by simpa using hv, ?_⟩
  rw [inversePermutation_getElem hv]
  exact hn.idxOf_getElem i hi

/-- The inverse's index of i is the original value at index i. -/
theorem inversePermutation_idxOf {n i : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) (hi : i < p.length) :
    (inversePermutation p).idxOf i = p[i] := by
  have hn := (inversePermutation_perm hp).nodup_iff.mpr List.nodup_range
  obtain ⟨hv, he⟩ := inversePermutation_getElem_value hp hi
  have h := hn.idxOf_getElem p[i] hv
  rw [he] at h
  exact h

theorem inversePermutation_involutive {n : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) : inversePermutation (inversePermutation p) = p := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [inversePermutation_getElem (by simpa using hj)]
  exact inversePermutation_idxOf hp hj

/-- Exact sortable-input/generated-output orientation equivalence. Widths and
physical slot bounds are unchanged; the proof uses only established Run.map
and proved permutation inversion identities. -/
theorem sortable_iff_inverse_generated {r s n : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) :
    Run r s [] p (List.range n) [] ↔
      Run r s [] (List.range n) (inversePermutation p) [] := by
  have hn := hp.nodup_iff.mpr List.nodup_range
  have hlen : p.length = n := by simpa using hp.length_eq
  have hinv := inversePermutation_perm hp
  have hni := hinv.nodup_iff.mpr List.nodup_range
  constructor
  · intro h
    have hm := h.map p.idxOf
    have hout : (List.range n).map p.idxOf = inversePermutation p := by simp [inversePermutation, hlen]
    simpa only [List.map_nil, map_idxOf_self hn, hlen, hout] using hm
  · intro h
    have hm := h.map (inversePermutation p).idxOf
    have hinput : (List.range n).map (inversePermutation p).idxOf = p := by
      have he : (List.range n).map (inversePermutation p).idxOf = inversePermutation (inversePermutation p) := by
        simp [inversePermutation, hlen]
      exact he.trans (inversePermutation_involutive hp)
    simpa only [List.map_nil, hinput, map_idxOf_self hni, inversePermutation_length, hlen] using hm

/-- Pure pointwise displacement translation. Generated-output excess of the
inverse becomes sortable-input delay of the original, with zero-based indices. -/
theorem inverse_displacement_iff {n D : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) :
    (∀ i (hi : i < (inversePermutation p).length), (inversePermutation p)[i] ≤ i+D) ↔
      (∀ i (hi : i < p.length), i ≤ p[i]+D) := by
  constructor
  · intro h i hi
    obtain ⟨hv, he⟩ := inversePermutation_getElem_value hp hi
    simpa only [he] using h p[i] hv
  · intro h i hi
    have hinv := inversePermutation_perm hp
    obtain ⟨hv, he⟩ := inversePermutation_getElem_value hinv hi
    have h := h (inversePermutation p)[i] (by simpa only [inversePermutation_length] using hv)
    have hval : p[(inversePermutation p)[i]]'(by simpa only [inversePermutation_length] using hv) = i := by
      simpa only [inversePermutation_involutive hp] using he
    simpa only [hval] using h

#print axioms map_idxOf_self
#print axioms inversePermutation_perm
#print axioms inversePermutation_involutive
#print axioms sortable_iff_inverse_generated
#print axioms inverse_displacement_iff
end StackSorting.Generalized
