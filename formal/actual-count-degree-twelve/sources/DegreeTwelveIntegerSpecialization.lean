import DegreeTwelveSpecialization
import DegreeTwelveData
namespace StackSorting.DegreeTwelve
open Polynomial
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
/-- Integer specialization at x=3 of the unchanged 69-term polynomial. -/
def integerSpecialized : ℤ[X] := (679104) + (-831456) * X^1 + (4187772) * X^2 + (-5567184) * X^3 + (13985156) * X^4 + (-21282008) * X^5 + (33018519) * X^6 + (-43278848) * X^7 + (41675021) * X^8 + (-34660260) * X^9 + (18377847) * X^10 + (-3974508) * X^11 + (78732) * X^12

theorem integerSpecialized_degree : integerSpecialized.natDegree = 12 := by
  unfold integerSpecialized
  compute_degree!

theorem integerSpecialized_coeff_zero : integerSpecialized.coeff 0 = 679104 := by
  norm_num [integerSpecialized, coeff_add, coeff_mul_X_pow, coeff_X]

theorem integerSpecialized_coeff_eight : integerSpecialized.coeff 8 = 41675021 := by
  norm_num [integerSpecialized, coeff_add, coeff_mul_X_pow, coeff_X]

theorem integerSpecialized_leadingCoeff : integerSpecialized.leadingCoeff = 78732 := by
  rw [leadingCoeff, integerSpecialized_degree]
  norm_num [integerSpecialized, coeff_add, coeff_mul_X_pow, coeff_X]

theorem integerSpecialized_primitive : integerSpecialized.IsPrimitive := by
  apply primitive_of_coprime_coefficients integerSpecialized 0 8
  rw [integerSpecialized_coeff_zero, integerSpecialized_coeff_eight]
  refine ⟨-10227595, 166661, ?_⟩
  norm_num

theorem integerSpecialized_mod_seventeen :
    integerSpecialized.map (Int.castRingHom (ZMod 17)) = specialized := by
  unfold integerSpecialized specialized
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_X, Polynomial.map_ofNat, Polynomial.map_neg]
  reduce_mod_char
  ring

theorem integerSpecialized_leading_nonzero :
    (Int.castRingHom (ZMod 17)) integerSpecialized.leadingCoeff ≠ 0 := by
  rw [integerSpecialized_leadingCoeff]
  decide +kernel

#print axioms integerSpecialized_degree
#print axioms integerSpecialized_primitive
#print axioms integerSpecialized_mod_seventeen
#print axioms integerSpecialized_leading_nonzero
end
end StackSorting.DegreeTwelve
