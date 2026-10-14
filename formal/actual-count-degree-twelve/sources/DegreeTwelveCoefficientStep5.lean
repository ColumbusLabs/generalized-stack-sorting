import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs5 : List Coefficients.F := [6, 8, 3, 8, 5, 9, 9, 9, 10, 15, 12, 16, 12, 16, 8, 16, 7, 3, 14, 7, 16, 9, 15, 2, 7, 0, 4, 4, 1, 0, 5, 15, 3, 13, 14, 12, 16, 14, 10, 3, 16, 10, 9, 2, 8, 5, 11, 13, 8, 8, 14, 3, 10, 2, 9, 10, 6, 1, 7, 13, 9, 8, 6, 5, 12, 5, 8, 0, 14, 13, 0, 14, 11, 12, 7, 16, 10, 10, 1, 2, 7, 11, 12, 11, 4, 12, 16, 2, 12, 13, 8, 10, 3, 1, 4, 6, 15, 11, 5, 4, 2, 6, 10, 16, 4, 9, 1, 2, 9, 10, 7, 7, 11, 10, 10, 2, 0, 2, 7, 13, 3, 12, 7, 10, 5, 4, 16, 3, 16, 1, 5, 9, 6, 15, 11, 5, 2, 1, 3, 1, 9, 3, 6, 11, 1, 11, 2, 9, 9, 10, 6, 10, 11, 4, 0, 2, 14, 12, 11, 4, 0, 2, 1, 4, 12, 10, 1, 2, 10, 10, 13, 0, 8, 10, 11, 14]

theorem coefficient_step_5 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs5)
      (Coefficients.neg remCoeffs6)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs5) := by
  decide +kernel

theorem certified_frobenius_step_5 : specialized ∣ rem5^17 - rem6 := by
  refine ⟨Coefficients.eval quotientCoeffs5, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_5
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs5, eval_remCoeffs6, sub_eq_add_neg] using h

#print axioms coefficient_step_5
#print axioms certified_frobenius_step_5
end
end StackSorting.DegreeTwelve
