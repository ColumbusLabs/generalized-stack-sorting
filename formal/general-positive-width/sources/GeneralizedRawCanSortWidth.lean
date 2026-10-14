import GeneralizedSortableBasisWidth

/-! Explicit +1 relabelling and raw-semantic wrapper for the existing named
CanSort predicate, whose increasing output is range' 1 input.length. -/
namespace StackSorting.Generalized
open List

theorem canSort_iff_run (r s : Nat) (input : List Nat) :
    CanSort r s input ↔ Run r s [] input (List.range' 1 input.length) [] := by
  exact (run_relational_iff r s [] input (List.range' 1 input.length) []).symm

theorem range_map_succ (n : Nat) : (List.range n).map Nat.succ = List.range' 1 n := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [Nat.add_comm]

theorem range'_one_map_pred (n : Nat) : (List.range' 1 n).map Nat.pred = List.range n := by
  rw [← range_map_succ, List.map_map]
  simp [Function.comp_def]

/-- This is the explicit bridge between the older one-based named raw model
and the new zero-based relational theorems. It does not identify them by fiat. -/
theorem canSort_map_succ_iff (r s : Nat) (p : List Nat) :
    CanSort r s (p.map Nat.succ) ↔ Run r s [] p (List.range p.length) [] := by
  rw [canSort_iff_run]
  constructor
  · intro h
    have hm := h.map Nat.pred
    simpa [List.map_map, Function.comp_def, range'_one_map_pred] using hm
  · intro h
    have hm := h.map Nat.succ
    simpa [range_map_succ] using hm

/-- Standardized one-based deletion commutes with the explicit +1 relabelling. -/
theorem deleteWord_map_succ (v : Nat) (p : List Nat) :
    deleteWord (v+1) (p.map Nat.succ) = (deleteWord v p).map Nat.succ := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons, deleteWord_cons, Nat.succ_eq_add_one, Nat.add_left_inj]
    by_cases he : a = v
    · simp [he, ih]
    · simp [he, deleteRank_succ_succ, ih]

/-- One-based labels and one-based positions in the published sortable formula.
The list index i is zero-based, so its physical position is i+1. -/
def oneBasedSortableWidth (input : List Nat) : Nat :=
  1 + ((List.range input.length).map (fun i => i+1-input[i]!)).foldr Nat.max 0

theorem oneBasedSortableWidth_map_succ (p : List Nat) :
    oneBasedSortableWidth (p.map Nat.succ) = sortableDisplacementWidth p := by
  unfold oneBasedSortableWidth sortableDisplacementWidth
  simp only [List.length_map]
  congr 1
  apply congrArg (fun xs : List Nat => xs.foldr Nat.max 0)
  apply List.map_congr_left
  intro i hi
  have hlt := List.mem_range.mp hi
  rw [getElem!_pos p i hlt, getElem!_pos (p.map Nat.succ) i (by simpa using hlt), List.getElem_map]
  omega

theorem CanSort_minimal_map_succ_width_le {r s n : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ CanSort r s (p.map Nat.succ))
    (hdelete : ∀ v ∈ List.range n, CanSort r s (deleteWord (v+1) (p.map Nat.succ))) :
    oneBasedSortableWidth (p.map Nat.succ) ≤ 2 * max r s + 1 := by
  have hlen : p.length = n := by simpa using hp.length_eq
  have hno : ¬ Run r s [] p (List.range n) [] := fun h =>
    hreject ((canSort_map_succ_iff r s p).mpr (by simpa [hlen] using h))
  have hdel : ∀ v ∈ List.range n,
      Run r s [] (deleteWord v p) (List.range (n-1)) [] := by
    intro v hv
    have hc := hdelete v hv
    rw [deleteWord_map_succ] at hc
    have hh := (canSort_map_succ_iff r s (deleteWord v p)).mp hc
    have hd : (deleteWord v p).length = n-1 := by
      simpa using (deleteWord_permutation hp (List.mem_range.mp hv)).length_eq
    simpa [hd] using hh
  rw [oneBasedSortableWidth_map_succ]
  exact oneDeletionMinimal_sortable_width_le hp hr hs hno hdel

/-- Every ordinary one-based permutation is exactly its predecessor-labelled
zero-based permutation shifted back by one. -/
theorem oneBased_permutation_zeroBased {n : Nat} {input : List Nat}
    (hp : input.Perm (List.range' 1 n)) :
    (input.map Nat.pred).Perm (List.range n) ∧ (input.map Nat.pred).map Nat.succ = input := by
  constructor
  · simpa only [range'_one_map_pred] using hp.map Nat.pred
  · rw [List.map_map]
    have hmap : input.map (Nat.succ ∘ Nat.pred) = input.map id := by
      apply List.map_congr_left
      intro a ha
      have hpos := (List.mem_range'_1.mp (hp.mem_iff.mp ha)).1
      simp only [Function.comp_apply, id_eq]
      exact Nat.succ_pred_eq_of_pos (by omega)
    simpa using hmap

/-- Global width bound in the existing named raw CanSort model. All premises
are ordinary one-based permutation membership, rejection, and sorting of each
standardized one-value deletion. No zero-based Run premise is left to the caller. -/
theorem CanSort_oneDeletionMinimal_width_le {r s n : Nat} {input : List Nat}
    (hp : input.Perm (List.range' 1 n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ CanSort r s input)
    (hdelete : ∀ v ∈ input, CanSort r s (deleteWord v input)) :
    oneBasedSortableWidth input ≤ 2 * max r s + 1 := by
  obtain ⟨hz, he⟩ := oneBased_permutation_zeroBased hp
  have hno : ¬ CanSort r s ((input.map Nat.pred).map Nat.succ) := by simpa only [he] using hreject
  have hdel : ∀ v ∈ List.range n,
      CanSort r s (deleteWord (v+1) ((input.map Nat.pred).map Nat.succ)) := by
    intro v hv
    have hm : v+1 ∈ input := by
      rw [← he]
      exact List.mem_map.mpr ⟨v, hz.mem_iff.mpr hv, rfl⟩
    simpa only [he] using hdelete (v+1) hm
  simpa only [he] using CanSort_minimal_map_succ_width_le hz hr hs hno hdel

/-- The named-model (3,3) global basis width-seven theorem. -/
theorem CanSort_three_three_oneDeletionMinimal_width_le_seven {n : Nat} {input : List Nat}
    (hp : input.Perm (List.range' 1 n))
    (hreject : ¬ CanSort 3 3 input)
    (hdelete : ∀ v ∈ input, CanSort 3 3 (deleteWord v input)) :
    oneBasedSortableWidth input ≤ 7 := by
  simpa using CanSort_oneDeletionMinimal_width_le hp (by decide : 0 < 3)
    (by decide : 0 < 3) hreject hdelete

#print axioms canSort_map_succ_iff
#print axioms deleteWord_map_succ
#print axioms oneBasedSortableWidth_map_succ
#print axioms CanSort_oneDeletionMinimal_width_le
#print axioms CanSort_three_three_oneDeletionMinimal_width_le_seven
end StackSorting.Generalized
