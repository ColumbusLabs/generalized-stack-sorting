import Horner4Node265
import Horner4Reexpression
import Horner4RightProduct
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem coefficient_difference4 :
    BiPoly.zeroCheck (BiPoly.add h4p265 (BiPoly.neg rightPoly4))=true := by
  decide +kernel

theorem divisible4 (x y : FPS) : homogeneous4 x y=scalarPolynomialRing x y*quotient4 x y := by
  calc
    homogeneous4 x y = h4e265.eval (mapEnv x y) := homogeneous_horner4 (mapEnv x y)
    _ = BiPoly.eval h4p265 x y := by
      have h := homogeneous_poly_eval h4e265 x y
      rw [h4n265] at h
      exact h.symm
    _ = BiPoly.eval rightPoly4 x y :=
      BiPoly.eval_eq_of_zeroDifference h4p265 rightPoly4 coefficient_difference4 x y
    _ = scalarPolynomialRing x y*quotient4 x y := by
      rw [←rightPoly4_arithmetic, BiPoly.eval_mul, scalarQPoly_eval, quotientPoly4_eval]

#print axioms divisible4
end StackSorting.RationalLift
