import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs10 : List Coefficients.F := [10, 7, 14, 12, 3, 10, 3, 16, 13, 14, 1, 4, 12, 10, 1, 14, 10, 11, 15, 11, 6, 10, 11, 9, 5, 1, 13, 7, 14, 1, 3, 9, 14, 12, 5, 5, 7, 0, 10, 8, 15, 13, 14, 10, 16, 10, 9, 5, 6, 3, 13, 9, 3, 9, 12, 6, 14, 12, 16, 10, 12, 9, 0, 0, 10, 13, 2, 6, 1, 14, 14, 2, 10, 14, 6, 6, 13, 13, 7, 6, 16, 10, 7, 2, 15, 13, 14, 11, 10, 6, 1, 16, 1, 1, 14, 8, 2, 12, 16, 7, 0, 0, 15, 5, 1, 5, 9, 3, 15, 11, 15, 8, 15, 2, 7, 12, 6, 8, 0, 0, 14, 5, 0, 6, 5, 7, 1, 9, 7, 5, 15, 10, 2, 10, 1, 12, 6, 6, 7, 10, 4, 7, 3, 15, 15, 11, 13, 6, 14, 5, 11, 3, 9, 6, 0, 14, 10, 11, 10, 7, 0, 12, 6, 7, 4, 9, 6, 12, 9, 9, 10, 0, 14, 9, 15, 16]

theorem coefficient_step_10 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs10)
      (Coefficients.neg remCoeffs11)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs10) := by
  decide +kernel

theorem certified_frobenius_step_10 : specialized ∣ rem10^17 - rem11 := by
  refine ⟨Coefficients.eval quotientCoeffs10, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_10
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs10, eval_remCoeffs11, sub_eq_add_neg] using h

#print axioms coefficient_step_10
#print axioms certified_frobenius_step_10
end
end StackSorting.DegreeTwelve
