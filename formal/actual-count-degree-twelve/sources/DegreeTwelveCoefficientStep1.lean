import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs1 : List Coefficients.F := [1, 5, 13, 6, 12, 5, 9, 3, 12, 3, 0, 8, 13, 7, 12, 2, 6, 13, 2, 8, 1, 12, 11, 8, 0, 5, 14, 0, 11, 14, 1, 12, 5, 4, 4, 9, 2, 15, 14, 7, 10, 1, 14, 6, 14, 2, 14, 1, 12, 4, 4, 15, 8, 8, 15, 6, 15, 6, 5, 8, 1, 9, 2, 11, 10, 6, 16, 9, 13, 7, 9, 9, 2, 14, 6, 14, 13, 6, 10, 5, 5, 2, 5, 7, 4, 3, 7, 6, 10, 16, 7, 1, 16, 11, 6, 16, 15, 3, 3, 12, 1, 6, 8, 5, 16, 6, 11, 9, 5, 3, 15, 14, 7, 12, 2, 7, 5, 4, 3, 8, 4, 2, 15, 5, 1, 15, 10, 2, 9, 1, 4, 5, 11, 10, 5, 7, 14, 4, 5, 1, 14, 12, 9, 10, 5, 2, 10, 8, 7, 15, 8, 11, 15, 14, 0, 12, 10, 11, 0, 16, 0, 8, 4, 16, 14, 6, 4, 8, 6, 6, 1, 0, 15, 6, 10, 5]

theorem coefficient_step_1 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs1)
      (Coefficients.neg remCoeffs2)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs1) := by
  decide +kernel

theorem certified_frobenius_step_1 : specialized ∣ rem1^17 - rem2 := by
  refine ⟨Coefficients.eval quotientCoeffs1, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_1
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs1, eval_remCoeffs2, sub_eq_add_neg] using h

#print axioms coefficient_step_1
#print axioms certified_frobenius_step_1
end
end StackSorting.DegreeTwelve
