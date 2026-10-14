import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs7 : List Coefficients.F := [9, 10, 8, 12, 16, 9, 3, 14, 2, 7, 8, 11, 13, 9, 4, 14, 2, 10, 2, 10, 4, 11, 13, 14, 16, 0, 3, 7, 6, 14, 3, 8, 15, 8, 4, 11, 2, 11, 6, 13, 3, 1, 4, 12, 8, 1, 16, 14, 3, 6, 16, 11, 3, 4, 12, 9, 16, 0, 12, 6, 3, 3, 15, 3, 0, 14, 15, 3, 12, 3, 13, 4, 2, 7, 9, 12, 2, 16, 1, 9, 10, 7, 11, 13, 8, 5, 8, 7, 14, 4, 10, 6, 5, 12, 13, 8, 2, 15, 15, 2, 3, 13, 2, 13, 13, 9, 11, 8, 0, 3, 10, 0, 3, 6, 0, 16, 14, 16, 4, 2, 1, 3, 5, 11, 8, 3, 11, 1, 11, 7, 14, 10, 0, 9, 12, 5, 14, 16, 5, 4, 5, 7, 10, 6, 7, 10, 14, 5, 14, 11, 2, 13, 12, 14, 0, 13, 9, 15, 11, 13, 0, 15, 16, 13, 5, 7, 16, 15, 7, 7, 4, 0, 9, 7, 6, 3]

theorem coefficient_step_7 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs7)
      (Coefficients.neg remCoeffs8)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs7) := by
  decide +kernel

theorem certified_frobenius_step_7 : specialized ∣ rem7^17 - rem8 := by
  refine ⟨Coefficients.eval quotientCoeffs7, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_7
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs7, eval_remCoeffs8, sub_eq_add_neg] using h

#print axioms coefficient_step_7
#print axioms certified_frobenius_step_7
end
end StackSorting.DegreeTwelve
