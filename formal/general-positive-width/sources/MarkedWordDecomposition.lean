import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace StackSorting.Simon

variable {A : Type*}

/-- Cutting immediately after every marked letter produces blocks whose
interiors avoid the mark, followed by an unmarked suffix. Empty interiors are
allowed, but each completed block retains its actual marked terminal letter. -/
theorem exists_marked_decomposition (P : A → Prop) (w : List A) :
    ∃ blocks : List (List A × A), ∃ rest : List A,
      w = (blocks.flatMap fun z => z.1 ++ [z.2]) ++ rest ∧
      (∀ z ∈ blocks, P z.2 ∧ ∀ a ∈ z.1, ¬ P a) ∧
      (∀ a ∈ rest, ¬ P a) := by
  classical
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons a w ih =>
    obtain ⟨blocks, rest, hw, hb, hr⟩ := ih
    by_cases ha : P a
    · refine ⟨([], a) :: blocks, rest, ?_, ?_, hr⟩
      · simp [hw]
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨ha, by simp⟩
        · exact hb z hz
    · cases blocks with
      | nil =>
        refine ⟨[], a :: rest, ?_, by simp, ?_⟩
        · simpa using congrArg (List.cons a) hw
        · intro b hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact ha
          · exact hr b hmem
      | cons z blocks =>
        refine ⟨(a :: z.1, z.2) :: blocks, rest, ?_, ?_, hr⟩
        · simpa using congrArg (List.cons a) hw
        · intro t ht
          simp only [List.mem_cons] at ht
          rcases ht with rfl | ht
          · refine ⟨(hb z (by simp)).1, ?_⟩
            intro b hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact ha
            · exact (hb z (by simp)).2 b hmem
          · exact hb t (by simp [ht])

/-- Every block interior is a sublist of the original word, in particular all
its letter images belong to the original finite image support. -/
theorem block_member_of_decomposition
    (blocks : List (List A × A)) (rest : List A)
    {z : List A × A} (hz : z ∈ blocks) {a : A} (ha : a ∈ z.1) :
    a ∈ (blocks.flatMap fun z => z.1 ++ [z.2]) ++ rest := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨z, hz, List.mem_append_left _ ha⟩

#print axioms exists_marked_decomposition
end StackSorting.Simon
