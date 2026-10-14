import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs8 : List Coefficients.F := [8, 8, 3, 10, 14, 1, 5, 10, 3, 4, 1, 3, 11, 3, 2, 11, 9, 1, 7, 8, 11, 15, 2, 0, 5, 2, 6, 11, 1, 2, 6, 5, 15, 12, 6, 6, 9, 3, 3, 9, 3, 2, 14, 1, 13, 3, 2, 9, 6, 13, 6, 13, 5, 4, 9, 8, 1, 6, 7, 7, 13, 15, 5, 16, 7, 6, 10, 15, 6, 1, 0, 0, 10, 4, 0, 7, 6, 12, 9, 10, 11, 8, 16, 9, 10, 14, 4, 14, 6, 11, 6, 6, 10, 2, 7, 6, 3, 4, 14, 12, 5, 10, 9, 13, 14, 4, 5, 10, 8, 15, 15, 2, 8, 4, 7, 9, 12, 13, 16, 14, 16, 2, 16, 6, 15, 8, 6, 3, 8, 13, 5, 9, 12, 9, 6, 4, 2, 2, 8, 9, 7, 8, 1, 5, 5, 15, 10, 2, 16, 13, 15, 1, 3, 2, 0, 16, 9, 15, 9, 8, 0, 4, 2, 8, 7, 3, 2, 4, 3, 3, 9, 0, 16, 3, 5, 11]

theorem coefficient_step_8 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs8)
      (Coefficients.neg remCoeffs9)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs8) := by
  decide +kernel

theorem certified_frobenius_step_8 : specialized ∣ rem8^17 - rem9 := by
  refine ⟨Coefficients.eval quotientCoeffs8, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_8
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs8, eval_remCoeffs9, sub_eq_add_neg] using h

#print axioms coefficient_step_8
#print axioms certified_frobenius_step_8
end
end StackSorting.DegreeTwelve
