import GrammarPermutations
import CompleteSeries

namespace StackSorting.FirstReturn
open StackSorting

/-- The mathematical class is defined through the original physical machine. -/
abbrev SortableInput (n : Nat) :=
  {input : List Nat // Labelled.CanSort [] input (List.range' 1 n)}

noncomputable instance sortableInputFintype (n : Nat) : Fintype (SortableInput n) :=
  Fintype.subtype (Labelled.sortableInputs n).toFinset (by
    intro input
    simpa only [List.mem_toFinset] using Labelled.mem_sortableInputs n input)

/-- The Fintype cardinality agrees with the proved duplicate-free enumeration. -/
theorem sortable_card_eq_list (n : Nat) :
    Fintype.card (SortableInput n) = (Labelled.sortableInputs n).length := by
  rw [Fintype.card_of_subtype (Labelled.sortableInputs n).toFinset (by
    intro input
    simpa only [List.mem_toFinset] using Labelled.mem_sortableInputs n input)]
  rw [List.card_toFinset, List.dedup_eq_self.mpr (Labelled.sortableInputs_nodup n)]

def pathToSortable (n : Nat) (p : PathSlice n) : SortableInput n :=
  ⟨permutation p.val.val, by simpa [p.val.property] using permutation_sound p.val.val p.property⟩

theorem pathToSortable_bijective (n : Nat) : Function.Bijective (pathToSortable n) := by
  constructor
  · intro p q h
    apply Subtype.ext
    apply Subtype.ext
    apply permutation_injective _ _ p.property q.property
    · exact p.val.property.trans q.val.property.symm
    · exact congrArg Subtype.val h
  · intro input
    obtain ⟨p, hp, hw, he⟩ := permutation_surjective n input.val input.property
    exact ⟨⟨⟨p, hw⟩, hp⟩, Subtype.ext he⟩

noncomputable def grammarSortableEquiv (n : Nat) : PathSlice n ≃ SortableInput n :=
  Equiv.ofBijective (pathToSortable n) (pathToSortable_bijective n)

theorem pathCount_eq_sortable_card (n : Nat) :
    pathCount n = Fintype.card (SortableInput n) := Fintype.card_congr (grammarSortableEquiv n)

/-- The generating function counts distinct sortable permutations, via their
original-machine definition, not arbitrary operation histories. -/
noncomputable def sortingSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Fintype.card (SortableInput n) : ℤ)

theorem sortingSeries_eq_pathSeries : sortingSeries = pathSeries := by
  apply PowerSeries.ext
  intro n
  simp [sortingSeries, pathSeries, pathCount_eq_sortable_card]

#print axioms pathToSortable_bijective
#print axioms pathCount_eq_sortable_card
#print axioms sortingSeries_eq_pathSeries
end StackSorting.FirstReturn
