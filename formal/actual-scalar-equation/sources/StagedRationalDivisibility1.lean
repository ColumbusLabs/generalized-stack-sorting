import Horner1Node132
import Horner1Reexpression
import Horner1RightProduct
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem coefficient_difference1 :
    BiPoly.zeroCheck (BiPoly.add h1p132 (BiPoly.neg rightPoly1))=true := by
  decide +kernel

theorem divisible1 (x y : FPS) : homogeneous1 x y=scalarPolynomialRing x y*quotient1 x y := by
  calc
    homogeneous1 x y = h1e132.eval (mapEnv x y) := homogeneous_horner1 (mapEnv x y)
    _ = BiPoly.eval h1p132 x y := by
      have h := homogeneous_poly_eval h1e132 x y
      rw [h1n132] at h
      exact h.symm
    _ = BiPoly.eval rightPoly1 x y :=
      BiPoly.eval_eq_of_zeroDifference h1p132 rightPoly1 coefficient_difference1 x y
    _ = scalarPolynomialRing x y*quotient1 x y := by
      rw [←rightPoly1_arithmetic, BiPoly.eval_mul, scalarQPoly_eval, quotientPoly1_eval]

#print axioms divisible1
end StackSorting.RationalLift
