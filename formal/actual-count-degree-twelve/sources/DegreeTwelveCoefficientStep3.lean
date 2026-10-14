import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs3 : List Coefficients.F := [4, 10, 9, 11, 9, 0, 2, 16, 9, 2, 4, 13, 8, 13, 3, 8, 8, 3, 15, 5, 15, 4, 0, 12, 2, 2, 5, 5, 9, 4, 8, 9, 11, 16, 10, 1, 11, 5, 1, 7, 9, 11, 1, 9, 7, 13, 16, 3, 7, 13, 10, 8, 15, 4, 4, 0, 14, 0, 7, 0, 9, 3, 0, 2, 13, 6, 2, 3, 1, 14, 14, 1, 16, 12, 0, 3, 10, 4, 1, 3, 3, 6, 5, 15, 8, 11, 10, 16, 12, 13, 1, 7, 10, 8, 2, 7, 3, 5, 9, 4, 10, 16, 15, 12, 9, 1, 3, 9, 10, 10, 11, 2, 15, 4, 3, 13, 10, 15, 5, 11, 3, 5, 13, 9, 6, 2, 16, 11, 3, 13, 15, 4, 1, 7, 12, 9, 12, 12, 2, 15, 11, 1, 8, 13, 14, 14, 11, 1, 16, 2, 6, 11, 6, 10, 0, 15, 8, 2, 10, 14, 0, 7, 12, 14, 8, 1, 12, 7, 1, 1, 3, 0, 11, 1, 13, 15]

theorem coefficient_step_3 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs3)
      (Coefficients.neg remCoeffs4)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs3) := by
  decide +kernel

theorem certified_frobenius_step_3 : specialized ∣ rem3^17 - rem4 := by
  refine ⟨Coefficients.eval quotientCoeffs3, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_3
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs3, eval_remCoeffs4, sub_eq_add_neg] using h

#print axioms coefficient_step_3
#print axioms certified_frobenius_step_3
end
end StackSorting.DegreeTwelve
