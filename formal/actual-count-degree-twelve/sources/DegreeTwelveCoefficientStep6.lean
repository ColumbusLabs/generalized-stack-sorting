import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs6 : List Coefficients.F := [5, 11, 9, 6, 11, 4, 9, 6, 1, 9, 8, 16, 15, 15, 11, 7, 6, 12, 12, 10, 16, 4, 2, 7, 9, 14, 7, 3, 15, 9, 1, 5, 13, 7, 11, 9, 14, 11, 2, 8, 12, 5, 13, 2, 11, 0, 13, 2, 4, 4, 14, 6, 2, 3, 15, 0, 0, 15, 1, 8, 15, 15, 0, 14, 12, 14, 16, 15, 10, 7, 9, 6, 1, 6, 10, 8, 9, 9, 9, 16, 15, 9, 2, 13, 9, 16, 6, 7, 10, 7, 0, 5, 4, 5, 8, 13, 6, 0, 10, 10, 14, 11, 16, 13, 0, 6, 4, 12, 4, 15, 15, 2, 9, 5, 14, 7, 16, 10, 8, 16, 9, 6, 14, 8, 4, 16, 14, 4, 3, 15, 7, 3, 14, 9, 10, 1, 9, 2, 9, 2, 1, 4, 7, 5, 8, 8, 16, 3, 14, 6, 1, 16, 1, 13, 0, 11, 7, 6, 13, 8, 0, 4, 2, 8, 7, 3, 2, 4, 3, 3, 9, 0, 16, 3, 5, 11]

theorem coefficient_step_6 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs6)
      (Coefficients.neg remCoeffs7)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs6) := by
  decide +kernel

theorem certified_frobenius_step_6 : specialized ∣ rem6^17 - rem7 := by
  refine ⟨Coefficients.eval quotientCoeffs6, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_6
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs6, eval_remCoeffs7, sub_eq_add_neg] using h

#print axioms coefficient_step_6
#print axioms certified_frobenius_step_6
end
end StackSorting.DegreeTwelve
