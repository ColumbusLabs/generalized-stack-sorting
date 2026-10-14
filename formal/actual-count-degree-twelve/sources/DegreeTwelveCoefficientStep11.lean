import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs11 : List Coefficients.F := [8, 8, 4, 6, 8, 2, 9, 13, 11, 1, 3, 15, 6, 6, 6, 10, 4, 6, 6, 9, 7, 11, 7, 15, 2, 5, 6, 12, 9, 0, 14, 4, 15, 15, 13, 14, 3, 13, 14, 16, 5, 9, 11, 12, 3, 11, 12, 2, 11, 11, 1, 8, 11, 8, 8, 5, 3, 12, 6, 1, 15, 7, 0, 7, 7, 6, 1, 13, 12, 0, 1, 7, 0, 5, 6, 3, 13, 13, 14, 8, 4, 9, 11, 16, 11, 0, 5, 9, 8, 6, 8, 5, 16, 3, 3, 4, 14, 13, 9, 12, 12, 10, 9, 0, 0, 7, 6, 5, 4, 15, 1, 2, 1, 1, 15, 10, 9, 1, 2, 2, 16, 3, 11, 3, 12, 10, 6, 12, 4, 1, 12, 14, 0, 0, 5, 0, 9, 8, 9, 12, 5, 10, 16, 3, 9, 12, 1, 10, 9, 4, 15, 0, 8, 13, 0, 3, 15, 8, 10, 15, 0, 16, 8, 15, 11, 12, 8, 16, 12, 12, 2, 0, 13, 12, 3, 10]

theorem coefficient_step_11 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs11)
      (Coefficients.neg remCoeffs12)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs11) := by
  decide +kernel

theorem certified_frobenius_step_11 : specialized ∣ rem11^17 - rem12 := by
  refine ⟨Coefficients.eval quotientCoeffs11, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_11
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs11, eval_remCoeffs12, sub_eq_add_neg] using h

#print axioms coefficient_step_11
#print axioms certified_frobenius_step_11
end
end StackSorting.DegreeTwelve
