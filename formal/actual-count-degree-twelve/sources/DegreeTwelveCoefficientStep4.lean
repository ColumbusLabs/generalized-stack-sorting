import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs4 : List Coefficients.F := [2, 9, 8, 6, 4, 4, 1, 5, 4, 10, 7, 2, 11, 1, 6, 5, 5, 14, 11, 6, 14, 13, 7, 7, 14, 8, 5, 14, 2, 11, 8, 9, 12, 2, 5, 12, 14, 12, 14, 6, 7, 3, 0, 6, 0, 1, 1, 1, 8, 4, 14, 7, 13, 14, 0, 9, 3, 15, 4, 3, 7, 1, 6, 7, 4, 5, 10, 10, 7, 8, 14, 13, 12, 4, 7, 11, 10, 9, 5, 2, 9, 12, 13, 15, 1, 2, 7, 3, 2, 5, 12, 5, 11, 1, 3, 14, 13, 5, 7, 16, 1, 7, 0, 8, 14, 3, 6, 4, 3, 9, 4, 5, 6, 7, 4, 0, 0, 2, 15, 1, 4, 0, 16, 12, 15, 13, 10, 9, 4, 2, 16, 0, 15, 16, 11, 10, 8, 10, 15, 11, 1, 0, 7, 8, 9, 16, 1, 16, 0, 6, 8, 10, 3, 8, 0, 16, 16, 4, 1, 6, 0, 3, 10, 6, 1, 15, 10, 3, 15, 15, 11, 0, 12, 15, 8, 4]

theorem coefficient_step_4 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs4)
      (Coefficients.neg remCoeffs5)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs4) := by
  decide +kernel

theorem certified_frobenius_step_4 : specialized ∣ rem4^17 - rem5 := by
  refine ⟨Coefficients.eval quotientCoeffs4, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_4
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs4, eval_remCoeffs5, sub_eq_add_neg] using h

#print axioms coefficient_step_4
#print axioms certified_frobenius_step_4
end
end StackSorting.DegreeTwelve
