import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs2 : List Coefficients.F := [6, 12, 2, 8, 2, 5, 12, 3, 2, 9, 3, 14, 11, 5, 8, 8, 1, 15, 8, 6, 15, 16, 12, 5, 9, 8, 12, 5, 3, 13, 4, 14, 6, 16, 3, 2, 9, 14, 9, 2, 3, 4, 10, 9, 14, 1, 14, 11, 12, 12, 16, 6, 10, 15, 9, 10, 6, 12, 6, 10, 13, 5, 7, 14, 3, 12, 4, 0, 4, 10, 14, 13, 11, 13, 6, 8, 9, 11, 2, 0, 5, 15, 14, 6, 14, 6, 0, 13, 6, 1, 15, 0, 12, 6, 12, 6, 6, 6, 6, 4, 6, 12, 7, 0, 13, 3, 8, 7, 9, 13, 7, 15, 10, 13, 7, 1, 15, 16, 11, 7, 12, 1, 0, 4, 13, 4, 13, 5, 1, 15, 3, 6, 13, 0, 2, 6, 4, 16, 16, 4, 5, 11, 3, 6, 12, 4, 7, 1, 5, 5, 7, 4, 3, 4, 0, 16, 0, 0, 12, 13, 0, 15, 16, 13, 5, 7, 16, 15, 7, 7, 4, 0, 9, 7, 6, 3]

theorem coefficient_step_2 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs2)
      (Coefficients.neg remCoeffs3)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs2) := by
  decide +kernel

theorem certified_frobenius_step_2 : specialized ∣ rem2^17 - rem3 := by
  refine ⟨Coefficients.eval quotientCoeffs2, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_2
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs2, eval_remCoeffs3, sub_eq_add_neg] using h

#print axioms coefficient_step_2
#print axioms certified_frobenius_step_2
end
end StackSorting.DegreeTwelve
