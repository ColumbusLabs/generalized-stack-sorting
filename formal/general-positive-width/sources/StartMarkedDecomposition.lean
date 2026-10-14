import MarkedWordDecomposition

namespace StackSorting.Simon
variable {A : Type*}

/-- Decompose before each marked letter. The pre and every block interior
avoid the mark; terminal letters are not deleted or identified. -/
theorem exists_start_marked_decomposition (P : A → Prop) (w : List A) :
    ∃ pre : List A, ∃ blocks : List (A × List A),
      w = pre ++ blocks.flatMap (fun z => z.1 :: z.2) ∧
      (∀ a ∈ pre, ¬ P a) ∧
      (∀ z ∈ blocks, P z.1 ∧ ∀ a ∈ z.2, ¬ P a) := by
  classical
  induction w with
  | nil => exact ⟨[],[],rfl,by simp,by simp⟩
  | cons a w ih =>
    obtain ⟨pre,blocks,hw,hp,hb⟩ := ih
    by_cases ha : P a
    · refine ⟨[],(a,pre) :: blocks,?_,by simp,?_⟩
      · simp [hw]
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨ha,hp⟩
        · exact hb z hz
    · refine ⟨a :: pre,blocks,?_,?_,hb⟩
      · simp [hw]
      · intro b hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact ha
        · exact hp b hmem
end StackSorting.Simon
