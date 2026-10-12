import Horner0Node139
import Horner0Reexpression
import Horner0RightProduct
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem coefficient_difference0 :
    BiPoly.zeroCheck (BiPoly.add h0p139 (BiPoly.neg rightPoly0))=true := by
  decide +kernel

theorem divisible0 (x y : FPS) : homogeneous0 x y=scalarPolynomialRing x y*quotient0 x y := by
  calc
    homogeneous0 x y = h0e139.eval (mapEnv x y) := homogeneous_horner0 (mapEnv x y)
    _ = BiPoly.eval h0p139 x y := by
      have h := homogeneous_poly_eval h0e139 x y
      rw [h0n139] at h
      exact h.symm
    _ = BiPoly.eval rightPoly0 x y :=
      BiPoly.eval_eq_of_zeroDifference h0p139 rightPoly0 coefficient_difference0 x y
    _ = scalarPolynomialRing x y*quotient0 x y := by
      rw [←rightPoly0_arithmetic, BiPoly.eval_mul, scalarQPoly_eval, quotientPoly0_eval]

#print axioms divisible0
end StackSorting.RationalLift
