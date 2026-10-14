import DegreeTwelveCoefficientData
namespace StackSorting.DegreeTwelve
open Polynomial Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Explicit division quotient; its identity is checked by kernel reduction. -/
def quotientCoeffs0 : List Coefficients.F := [15, 0, 4, 5, 14, 7]

theorem coefficient_step_0 :
    Coefficients.pad 220 (Coefficients.add (Coefficients.frobenius remCoeffs0)
      (Coefficients.neg remCoeffs1)) =
    Coefficients.pad 220 (Coefficients.mul fCoeffs quotientCoeffs0) := by
  decide +kernel

theorem certified_frobenius_step_0 : specialized ∣ rem0^17 - rem1 := by
  refine ⟨Coefficients.eval quotientCoeffs0, ?_⟩
  have h := Coefficients.equality_of_padded_equality coefficient_step_0
  simpa only [Coefficients.eval_add, Coefficients.eval_neg,
    Coefficients.eval_frobenius, Coefficients.eval_mul,
    eval_fCoeffs, eval_remCoeffs0, eval_remCoeffs1, sub_eq_add_neg] using h

#print axioms coefficient_step_0
#print axioms certified_frobenius_step_0
end
end StackSorting.DegreeTwelve
