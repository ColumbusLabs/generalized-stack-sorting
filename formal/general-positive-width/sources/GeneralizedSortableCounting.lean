import GeneralizedActualCounting
import GeneralizedRawCanSortWidth

/-!
# Distinct sortable-input counts in the literal generalized machine

Permutation inversion gives a duplicate-free finite list of sortable inputs.
The list membership theorem is proved against the original relational Run;
the explicitly shifted list is proved against the named one-based CanSort.
No history multiplicity, capacity bound, or finite-length cutoff is introduced.
-/
namespace StackSorting.Generalized.ActualCounting

/-- Zero-based sortable inputs, enumerated exactly once by inversion. -/
def sortableInputs (r s n : Nat) : List (List Nat) :=
  (generatedOutputs r s n).map inversePermutation

theorem generatedOutput_permutation {r s n : Nat} (hr : 0 < r) (hs : 0 < s)
    {p : List Nat} (hp : p ∈ generatedOutputs r s n) :
    p.Perm (List.range n) := by
  have run := (mem_generatedOutputs_iff hr hs p).mp hp
  simpa using run.supply.symm

theorem sortableInputs_nodup {r s : Nat} (hr : 0 < r) (hs : 0 < s) (n : Nat) :
    (sortableInputs r s n).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := generatedOutputs_nodup r s n)
  intro a b ha hb hne he
  apply hne
  have hi := congrArg inversePermutation he
  simpa only [inversePermutation_involutive (generatedOutput_permutation hr hs ha),
    inversePermutation_involutive (generatedOutput_permutation hr hs hb)] using hi

/-- Exact all-length semantic endpoint: the listed objects are the distinct
permutations sorted by the original unrestricted-height machine. -/
theorem mem_sortableInputs_iff {r s n : Nat} (hr : 0 < r) (hs : 0 < s)
    (input : List Nat) :
    input ∈ sortableInputs r s n ↔
      input.Perm (List.range n) ∧ Run r s [] input (List.range n) [] := by
  constructor
  · intro hm
    obtain ⟨output, ho, rfl⟩ := List.mem_map.mp hm
    have hp := generatedOutput_permutation hr hs ho
    refine ⟨inversePermutation_perm hp, ?_⟩
    apply (sortable_iff_inverse_generated (inversePermutation_perm hp)).mpr
    simpa only [inversePermutation_involutive hp] using
      (mem_generatedOutputs_iff hr hs output).mp ho
  · rintro ⟨hp, run⟩
    apply List.mem_map.mpr
    refine ⟨inversePermutation input, ?_, inversePermutation_involutive hp⟩
    exact (mem_generatedOutputs_iff hr hs _).mpr
      ((sortable_iff_inverse_generated hp).mp run)

/-- Named CanSort uses one-based labels, so this relabeling is explicit. -/
def oneBasedSortableInputs (r s n : Nat) : List (List Nat) :=
  (sortableInputs r s n).map (List.map Nat.succ)

theorem oneBasedSortableInputs_nodup {r s : Nat} (hr : 0 < r) (hs : 0 < s)
    (n : Nat) : (oneBasedSortableInputs r s n).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := sortableInputs_nodup hr hs n)
  intro a b _ _ hne he
  apply hne
  have hi := congrArg (List.map Nat.pred) he
  simpa [List.map_map, Function.comp_def] using hi

/-- Exact membership in the duplicate-free list for the unchanged named
raw-operation CanSort model, including its actual sorted output range' 1 n. -/
theorem mem_oneBasedSortableInputs_iff {r s n : Nat} (hr : 0 < r) (hs : 0 < s)
    (input : List Nat) :
    input ∈ oneBasedSortableInputs r s n ↔
      input.Perm (List.range' 1 n) ∧ CanSort r s input := by
  constructor
  · intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨perm, run⟩ := (mem_sortableInputs_iff hr hs p).mp hp
    have hlen : p.length = n := by simpa using perm.length_eq
    refine ⟨?_, (canSort_map_succ_iff r s p).mpr (by simpa [hlen] using run)⟩
    simpa only [range_map_succ] using perm.map Nat.succ
  · rintro ⟨perm, sort⟩
    obtain ⟨hp, he⟩ := oneBased_permutation_zeroBased perm
    have hlen : (input.map Nat.pred).length = n := by simpa using hp.length_eq
    have hsort : CanSort r s ((input.map Nat.pred).map Nat.succ) := by
      simpa only [he] using sort
    have run := (canSort_map_succ_iff r s (input.map Nat.pred)).mp hsort
    exact List.mem_map.mpr ⟨input.map Nat.pred,
      (mem_sortableInputs_iff hr hs _).mpr ⟨hp, by simpa [hlen] using run⟩, he⟩

/-- Each entry counts one input permutation, never a sorting witness. -/
def sortableCount (r s n : Nat) : Nat := (oneBasedSortableInputs r s n).length

/-- Inversion preserves cardinality for all widths and all lengths. Semantic
membership and duplicate-freeness above require positive widths. -/
theorem sortableCount_eq_generatedCount (r s n : Nat) :
    sortableCount r s n = generatedCount r s n := by
  simp [sortableCount, oneBasedSortableInputs, sortableInputs, generatedCount]

def threeThreeSortableCounts : Nat → Nat := sortableCount 3 3

theorem threeThreeSortableCounts_eq (n : Nat) :
    threeThreeSortableCounts n = threeThreeCounts n :=
  sortableCount_eq_generatedCount 3 3 n

theorem threeThreeSortableCounts_zero : threeThreeSortableCounts 0 = 1 := by
  rw [threeThreeSortableCounts_eq, threeThreeCounts_zero]

#print axioms sortableInputs_nodup
#print axioms mem_sortableInputs_iff
#print axioms oneBasedSortableInputs_nodup
#print axioms mem_oneBasedSortableInputs_iff
#print axioms sortableCount_eq_generatedCount
#print axioms threeThreeSortableCounts_eq
#print axioms threeThreeSortableCounts_zero
end StackSorting.Generalized.ActualCounting
