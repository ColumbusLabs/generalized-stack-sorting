import Horner3Node047
import Horner3Reexpression
import Horner3RightProduct
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem coefficient_difference3 :
    BiPoly.zeroCheck (BiPoly.add h3p47 (BiPoly.neg rightPoly3))=true := by
  decide +kernel

theorem divisible3 (x y : FPS) : homogeneous3 x y=scalarPolynomialRing x y*quotient3 x y := by
  calc
    homogeneous3 x y = h3e47.eval (mapEnv x y) := homogeneous_horner3 (mapEnv x y)
    _ = BiPoly.eval h3p47 x y := by
      have h := homogeneous_poly_eval h3e47 x y
      rw [h3n47] at h
      exact h.symm
    _ = BiPoly.eval rightPoly3 x y :=
      BiPoly.eval_eq_of_zeroDifference h3p47 rightPoly3 coefficient_difference3 x y
    _ = scalarPolynomialRing x y*quotient3 x y := by
      rw [←rightPoly3_arithmetic, BiPoly.eval_mul, scalarQPoly_eval, quotientPoly3_eval]

#print axioms divisible3
end StackSorting.RationalLift
