import RationalDivisibility5
import ChangedPolynomials
import RationalRegularity_a
import RationalRegularity_t
import RationalRegularity_u
import RationalRegularity_i
import RationalRegularity_q
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar StackSorting.FPSDivision
set_option maxRecDepth 10000
set_option maxHeartbeats 30000000
theorem homogeneous_factor5 : homogeneous5 X G =
    ((aD X G)^2 * (tD X G)^2 * (uD X G)^3 * (iD X G)^1 * (qD X G)^1) * changedP5 lifted_a lifted_t lifted_u lifted_i lifted_q X G := by
  simp only [homogeneous5, homogeneousExpr5, mapEnv, changedP5, changedP5Expr, IExpr.eval, polyArgs]
  rw [← lifted_a_cross, ← lifted_t_cross, ← lifted_u_cross, ← lifted_i_cross, ← lifted_q_cross]
  grind

theorem map_constraint5 : changedP5 lifted_a lifted_t lifted_u lifted_i lifted_q X G = 0 := by
  have h := divisible5 X G
  rw [formal_G_equation_ring] at h
  rw [homogeneous_factor5] at h
  have hc : Cancellable ((aD X G)^2 * (tD X G)^2 * (uD X G)^3 * (iD X G)^1 * (qD X G)^1) := by
    exact cancellable_mul (cancellable_mul (cancellable_mul (cancellable_mul (cancellable_pow aD_cancellable 2) (cancellable_pow tD_cancellable 2)) (cancellable_pow uD_cancellable 3)) (cancellable_pow iD_cancellable 1)) (cancellable_pow qD_cancellable 1)
  apply cancellable_zero hc
  simpa only [StackSorting.CauchyRing.FPS_zero_mul] using h

#print axioms map_constraint5
end StackSorting.RationalLift
