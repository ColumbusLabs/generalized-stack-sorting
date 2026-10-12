import GeneralizedTerminalClauseIntersection
import GeneralizedCompletionCounting
import FiniteInclusionExclusion

/-! Signed finite inclusion-exclusion for actual distinct completion outputs.
No realizing initial order, digit witness, schedule, or history is counted. -/
namespace StackSorting.Generalized.Decorated
open ActualCounting StackSorting.FiniteInclusionExclusion

/-- The actual cardinality definition is exactly an indicator sum over a
common duplicate-free finite output ambient of the stated total supply. -/
theorem completionCount_eq_countIn (state : State) (n h : Nat) (hh : height state = h) :
    (completionCount state n : Int) =
      countIn (unique (words (List.range' 1 (h+n)) (h+n))) (Completion state n) := by
  classical
  rw [countIn_eq_filter_length]
  simp only [completionCount, completionOutputs, hh]

theorem terminal_clause_height {P : State} (hu : Unary P) (m : Nat) :
    height (P ++ [.C m]) = P.length+m := by
  rw [height_append, unary_height hu]
  simp [height, Factor.height]

theorem terminal_face_height {P : State} (hu : Unary P) (m : Nat) (J : List Nat) :
    height (P ++ zeroFace m J) = P.length+m := by
  rw [height_append, unary_height hu, height_zeroFace]

/-- Actual terminal-clause valuation in every ordinary Z/B/T prefix, at every
future input length. `nonemptySubsets (range m)` is the literal finite family
of nonempty index subsets, with sign (-1)^(cardinality+1). -/
theorem completion_terminal_clause_valuation {P : State} (hu : Unary P) (m n : Nat) :
    (completionCount (P ++ [.C m]) n : Int) =
      ((nonemptySubsets (List.range m)).map (fun J =>
        (-1 : Int) ^ (J.length+1) * (completionCount (P ++ zeroFace m J) n : Int))).sum := by
  let ambient := unique (words (List.range' 1 (P.length+m+n)) (P.length+m+n))
  calc
    (completionCount (P ++ [.C m]) n : Int) =
        countIn ambient (Completion (P ++ [.C m]) n) :=
      completionCount_eq_countIn _ _ _ (terminal_clause_height hu m)
    _ = countIn ambient (fun output => ∃ j ∈ List.range m,
        Completion (P ++ zeroFace m [j]) n output) := by
      apply countIn_congr
      intro output
      simpa using completion_clause_iff_singleton_face P [] m n output
    _ = valuation (List.range m) (fun J => countIn ambient (fun output =>
        ∀ j ∈ J, Completion (P ++ zeroFace m [j]) n output)) :=
      countIn_union ambient (List.range m) (fun j output => Completion (P ++ zeroFace m [j]) n output)
    _ = valuation (List.range m) (fun J => (completionCount (P ++ zeroFace m J) n : Int)) := by
      apply valuation_congr
      intro J hne hsub
      rw [completionCount_eq_countIn _ _ _ (terminal_face_height hu m J)]
      apply countIn_congr
      intro output
      exact completion_terminal_faces_intersection hu m n J hne hsub output
    _ = ((nonemptySubsets (List.range m)).map (fun J =>
        (-1 : Int) ^ (J.length+1) * (completionCount (P ++ zeroFace m J) n : Int))).sum := by
      rw [valuation_eq_signed_sum]
      simp only [sign_eq_power]

/-- The formal completion-series identity, stated coefficientwise over Int. -/
theorem completion_terminal_clause_coefficients {P : State} (hu : Unary P) (m : Nat) :
    (fun n => (completionCount (P ++ [.C m]) n : Int)) =
      (fun n => ((nonemptySubsets (List.range m)).map (fun J =>
        (-1 : Int) ^ (J.length+1) * (completionCount (P ++ zeroFace m J) n : Int))).sum) := by
  funext n
  exact completion_terminal_clause_valuation hu m n

#check completion_terminal_clause_valuation
#print axioms completion_terminal_clause_valuation
end StackSorting.Generalized.Decorated
