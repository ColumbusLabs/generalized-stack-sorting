import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs9 : List Coefficients.F := [11, 14, 8, 12, 4, 12, 6, 7, 1, 11, 4, 0, 7, 0, 7, 7, 10, 14, 10, 5, 14, 14, 5, 6, 16, 6, 10, 0, 14, 0, 15, 12, 10, 14, 10, 4, 15, 4, 2, 6, 2, 9, 12, 16, 8, 4, 11, 7, 8, 7, 11, 16, 5, 14, 9, 5, 7, 6, 14, 2, 5, 10, 10, 6, 7, 15, 1, 11, 5, 8, 14, 16, 10, 11, 11, 14, 7, 16, 9, 7, 0, 13, 6, 12, 1, 3, 8, 14, 12, 3, 0, 7, 14, 1, 13, 14, 6, 11, 8, 2, 14, 11, 11, 0, 1, 15, 4, 16, 1, 15, 2, 11, 0, 4, 16, 8, 15, 15, 14, 11, 3, 12, 5, 11, 1, 3, 16, 9, 2, 12, 6, 15, 11, 0, 10, 9, 5, 8, 6, 16, 6, 5, 15, 3, 0, 16, 0, 7, 15, 8, 6, 6, 14, 14, 0, 1, 4, 1, 15, 15, 0, 16, 8, 15, 11, 12, 8, 16, 12, 12, 2, 0, 13, 12, 3, 10]

theorem coefficient_step_9 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs9)
      (Coefficients.neg remCoeffs10)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs9) := by
  decide +kernel

theorem certified_frobenius_step_9 : specialized ∣ rem9^17 - rem10 := by
  refine ⟨Coefficients.eval quotientCoeffs9, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_9
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs9, eval_remCoeffs10, sub_eq_add_neg] using h

#print axioms coefficient_step_9
#print axioms certified_frobenius_step_9
end
end StackSorting.DegreeTwelve
