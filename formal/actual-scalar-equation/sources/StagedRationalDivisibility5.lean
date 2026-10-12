import Horner5Node426
import Horner5Reexpression
import Horner5RightProduct
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem coefficient_difference5 :
    BiPoly.zeroCheck (BiPoly.add h5p426 (BiPoly.neg rightPoly5))=true := by
  decide +kernel

theorem divisible5 (x y : FPS) : homogeneous5 x y=scalarPolynomialRing x y*quotient5 x y := by
  calc
    homogeneous5 x y = h5e426.eval (mapEnv x y) := homogeneous_horner5 (mapEnv x y)
    _ = BiPoly.eval h5p426 x y := by
      have h := homogeneous_poly_eval h5e426 x y
      rw [h5n426] at h
      exact h.symm
    _ = BiPoly.eval rightPoly5 x y :=
      BiPoly.eval_eq_of_zeroDifference h5p426 rightPoly5 coefficient_difference5 x y
    _ = scalarPolynomialRing x y*quotient5 x y := by
      rw [←rightPoly5_arithmetic, BiPoly.eval_mul, scalarQPoly_eval, quotientPoly5_eval]

#print axioms divisible5
end StackSorting.RationalLift
