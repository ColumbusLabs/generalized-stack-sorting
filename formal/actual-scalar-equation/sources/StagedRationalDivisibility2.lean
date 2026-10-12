import Horner2Node106
import Horner2Reexpression
import Horner2RightProduct
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem coefficient_difference2 :
    BiPoly.zeroCheck (BiPoly.add h2p106 (BiPoly.neg rightPoly2))=true := by
  decide +kernel

theorem divisible2 (x y : FPS) : homogeneous2 x y=scalarPolynomialRing x y*quotient2 x y := by
  calc
    homogeneous2 x y = h2e106.eval (mapEnv x y) := homogeneous_horner2 (mapEnv x y)
    _ = BiPoly.eval h2p106 x y := by
      have h := homogeneous_poly_eval h2e106 x y
      rw [h2n106] at h
      exact h.symm
    _ = BiPoly.eval rightPoly2 x y :=
      BiPoly.eval_eq_of_zeroDifference h2p106 rightPoly2 coefficient_difference2 x y
    _ = scalarPolynomialRing x y*quotient2 x y := by
      rw [←rightPoly2_arithmetic, BiPoly.eval_mul, scalarQPoly_eval, quotientPoly2_eval]

#print axioms divisible2
end StackSorting.RationalLift
