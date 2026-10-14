import DegreeTwelveIntegerSpecialization
import DegreeTwelveFiniteIrreducible
import Mathlib.FieldTheory.RatFunc.Basic
namespace StackSorting.DegreeTwelve
open Polynomial
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def scalarCoeff0 : ℚ[X] := (-8100) + (-11016) * X^1 + (80028) * X^2

def scalarCoeff1 : ℚ[X] := (51444) + (18252) * X^1 + (-467820) * X^2 + (121212) * X^3

def scalarCoeff2 : ℚ[X] := (-140841) + (94788) * X^1 + (1068822) * X^2 + (-349236) * X^3 + (47583) * X^4

def scalarCoeff3 : ℚ[X] := (216756) + (-381312) * X^1 + (-1228464) * X^2 + (-13248) * X^3 + (67968) * X^4 + (5220) * X^5

def scalarCoeff4 : ℚ[X] := (-204775) + (609666) * X^1 + (816316) * X^2 + (1059340) * X^3 + (-434593) * X^4 + (48094) * X^5 + (-100) * X^6

def scalarCoeff5 : ℚ[X] := (121420) + (-545072) * X^1 + (-514200) * X^2 + (-1441424) * X^3 + (235008) * X^4 + (9376) * X^5 + (3380) * X^6

def scalarCoeff6 : ℚ[X] := (-44079) + (295164) * X^1 + (515321) * X^2 + (797680) * X^3 + (524094) * X^4 + (-195284) * X^5 + (15095) * X^6

def scalarCoeff7 : ℚ[X] := (8956) + (-97068) * X^1 + (-430040) * X^2 + (-240468) * X^3 + (-671588) * X^4 + (77436) * X^5 + (4044) * X^6

def scalarCoeff8 : ℚ[X] := (-781) + (18086) * X^1 + (205778) * X^2 + (136788) * X^3 + (251778) * X^4 + (155040) * X^5 + (-30168) * X^6

def scalarCoeff9 : ℚ[X] := (-1488) * X^1 + (-50844) * X^2 + (-100632) * X^3 + (-23076) * X^4 + (-123804) * X^5 + (648) * X^6

def scalarCoeff10 : ℚ[X] := (5103) * X^2 + (33984) * X^3 + (8604) * X^4 + (20520) * X^5 + (16092) * X^6

def scalarCoeff11 : ℚ[X] := (-3996) * X^3 + (-6912) * X^4 + (1944) * X^5 + (-5184) * X^6

def scalarCoeff12 : ℚ[X] := (972) * X^4

/-- The literal scalar polynomial, as a polynomial in Y over ℚ[x]. -/
def scalarPolynomial : (ℚ[X])[X] := C scalarCoeff0 + C scalarCoeff1 * X^1 + C scalarCoeff2 * X^2 + C scalarCoeff3 * X^3 + C scalarCoeff4 * X^4 + C scalarCoeff5 * X^5 + C scalarCoeff6 * X^6 + C scalarCoeff7 * X^7 + C scalarCoeff8 * X^8 + C scalarCoeff9 * X^9 + C scalarCoeff10 * X^10 + C scalarCoeff11 * X^11 + C scalarCoeff12 * X^12

theorem scalarPolynomial_coeff_0 : scalarPolynomial.coeff 0 = scalarCoeff0 := by
  simp [scalarPolynomial]

theorem scalarPolynomial_coeff_12 : scalarPolynomial.coeff 12 = scalarCoeff12 := by
  simp [scalarPolynomial]

theorem scalarPolynomial_degree : scalarPolynomial.natDegree = 12 := by
  unfold scalarPolynomial
  compute_degree!
  unfold scalarCoeff12
  exact mul_ne_zero (by norm_num) (pow_ne_zero 4 X_ne_zero)

theorem scalarPolynomial_leadingCoeff : scalarPolynomial.leadingCoeff = scalarCoeff12 := by
  rw [leadingCoeff, scalarPolynomial_degree, scalarPolynomial_coeff_12]

theorem scalarPolynomial_coeff_coprime : IsCoprime scalarCoeff0 scalarCoeff12 := by
  refine ⟨C (38267/10546875 : ℚ)*X^3 - C (7331/5062500 : ℚ)*X^2 + C (17/101250 : ℚ)*X - C (1/8100 : ℚ),
    C (60881861/379687500 : ℚ) - C (9451949/31640625 : ℚ)*X, ?_⟩
  apply Polynomial.funext
  intro r
  simp only [scalarCoeff0, scalarCoeff12, eval_add, eval_mul, eval_sub, eval_C, eval_pow, eval_X, eval_neg, eval_ofNat, eval_one]
  ring

theorem scalarPolynomial_primitive : scalarPolynomial.IsPrimitive := by
  apply primitive_of_coprime_coefficients scalarPolynomial 0 12
  rw [scalarPolynomial_coeff_0, scalarPolynomial_coeff_12]
  exact scalarPolynomial_coeff_coprime

theorem scalarPolynomial_specialization :
    scalarPolynomial.map (evalRingHom (3 : ℚ)) =
      integerSpecialized.map (Int.castRingHom ℚ) := by
  norm_num [scalarPolynomial, integerSpecialized, C_ofNat,
scalarCoeff0, scalarCoeff1, scalarCoeff2, scalarCoeff3, scalarCoeff4, scalarCoeff5, scalarCoeff6, scalarCoeff7, scalarCoeff8, scalarCoeff9, scalarCoeff10, scalarCoeff11, scalarCoeff12]

theorem scalarPolynomial_leading_nonzero :
    (evalRingHom (3 : ℚ)) scalarPolynomial.leadingCoeff ≠ 0 := by
  rw [scalarPolynomial_leadingCoeff]
  norm_num [scalarCoeff12]

theorem integerSpecialized_irreducible : Irreducible integerSpecialized := by
  apply primitive_irreducible_of_specialization (Int.castRingHom (ZMod 17))
    integerSpecialized integerSpecialized_primitive integerSpecialized_leading_nonzero
  rw [integerSpecialized_mod_seventeen]
  exact specialized_irreducible

theorem rationalSpecialized_irreducible :
    Irreducible (integerSpecialized.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    integerSpecialized_primitive).mp
    integerSpecialized_irreducible

theorem scalarPolynomial_irreducible : Irreducible scalarPolynomial := by
  apply primitive_irreducible_of_specialization (evalRingHom (3 : ℚ))
    scalarPolynomial scalarPolynomial_primitive scalarPolynomial_leading_nonzero
  rw [scalarPolynomial_specialization]
  exact rationalSpecialized_irreducible

/-- Irreducibility of the exact scalar polynomial over the rational-function field ℚ(x). -/
theorem scalarPolynomial_ratFunc_irreducible :
    Irreducible (scalarPolynomial.map (algebraMap ℚ[X] (RatFunc ℚ))) :=
  scalarPolynomial_primitive.irreducible_iff_irreducible_map_fraction_map.mp
    scalarPolynomial_irreducible

#print axioms integerSpecialized_irreducible
#print axioms rationalSpecialized_irreducible
#print axioms scalarPolynomial_irreducible
#print axioms scalarPolynomial_ratFunc_irreducible
end
end StackSorting.DegreeTwelve
