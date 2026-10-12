import GeneralizedUnaryBoundary
import GeneralizedTerminalClauseRecurrence
import GeneralizedORunCompletionCounting

/-! The two actual-output counting reductions needed by unary deletion,
with preservation of the unary valid-state domain. No arbitrary O erasure or
clause-intersection assumption is introduced. -/
namespace StackSorting.Generalized.Decorated
namespace UnarySuffix
open Coordinates ExceptionalSuffix

theorem threeLetters_zeroFace (m : Nat) (J : List Nat) : ThreeLetters (zeroFace m J) := by
  intro factor hm
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hm
  by_cases hj : index ∈ J
  · simp [hj]
  · simp [hj]

/-- Every nonempty zero face is literally a sublanguage of its terminal
clause, so coordinate validity descends without another machine theorem. -/
theorem terminal_face_valid {pre : State} {m : Nat}
    (hv : Valid (pre ++ [.C m])) (J : List Nat)
    (hne : J ≠ []) (hsub : J ⊆ List.range m) : Valid (pre ++ zeroFace m J) := by
  intro digits hd
  obtain ⟨before, block, hb, hblock, rfl⟩ := (denotes_append pre (zeroFace m J) digits).mp hd
  have hf : FaceDigits J (List.range m) block := (denotes_faceOn _ _ _).mp hblock
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil J hne
  have hc : (Factor.C m).denotes block :=
    ⟨by simpa using hf.length, hf.binary, hf.exists_zero (hsub hj) hj⟩
  exact hv _ ((denotes_append pre [.C m] _).mpr
    ⟨before, block, hb, (denotes_single _ _).mpr hc, rfl⟩)

/-- The normalized one-run target is still a valid unary state. -/
theorem one_run_reduced_domain {pre : State} {q : Nat} {last : Factor}
    (hp : ThreeLetters pre) (hl : last = .Z ∨ last = .B)
    (hv : Valid (pre ++ .Z :: (List.replicate q .O ++ [last]))) :
    ThreeLetters (pre ++ List.replicate (q+1) .Z ++ [last]) ∧
      Valid (pre ++ List.replicate (q+1) .Z ++ [last]) := by
  constructor
  · exact threeLetters_append (threeLetters_append hp (threeLetters_replicate _ (Or.inl rfl)))
      (threeLetters_single (by rcases hl with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)))
  · apply ORunCount.valid_source_target pre [last] q
    simpa only [ORunCount.source, List.append_assoc, List.cons_append] using hv

/-- This is the single O-run count replacement at the exact introduced target
shape. Its source and target have identical total held height. -/
theorem one_run_completion_count (pre : State) (q : Nat) (last : Factor) (n : Nat) :
    completionCount (pre ++ .Z :: (List.replicate q .O ++ [last])) n =
      completionCount (pre ++ List.replicate (q+1) .Z ++ [last]) n := by
  simpa only [ORunCount.source, ORunCount.target, List.append_assoc, List.cons_append] using
    ORunCount.completionCount_eq pre [last] q n

/-- Every term of the exact clause valuation re-enters the same unary valid
state domain, including all boundary sizes. -/
theorem terminal_clause_reduced_domain {pre : State} {m : Nat}
    (hp : ThreeLetters pre) (hv : Valid (pre ++ [.C m])) (J : List Nat)
    (hne : J ≠ []) (hsub : J ⊆ List.range m) :
    ThreeLetters (pre ++ zeroFace m J) ∧ Valid (pre ++ zeroFace m J) :=
  ⟨threeLetters_append hp (threeLetters_zeroFace m J), terminal_face_valid hv J hne hsub⟩

#print axioms terminal_face_valid
#print axioms one_run_completion_count
#print axioms terminal_clause_reduced_domain
end UnarySuffix
end StackSorting.Generalized.Decorated
