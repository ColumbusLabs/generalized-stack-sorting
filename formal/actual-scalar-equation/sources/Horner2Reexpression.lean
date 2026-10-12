import Horner2Expressions
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem homogeneous_horner2 (v : Nat → FPS) :
    homogeneousExpr2.eval v=h2e106.eval v := by
  dsimp [homogeneousExpr2, IExpr.eval, h2e0, h2e1, h2e2, h2e3, h2e4, h2e5, h2e6, h2e7, h2e8, h2e9, h2e10, h2e11, h2e12, h2e13, h2e14, h2e15, h2e16, h2e17, h2e18, h2e19, h2e20, h2e21, h2e22, h2e23, h2e24, h2e25, h2e26, h2e27, h2e28, h2e29, h2e30, h2e31, h2e32, h2e33, h2e34, h2e35, h2e36, h2e37, h2e38, h2e39, h2e40, h2e41, h2e42, h2e43, h2e44, h2e45, h2e46, h2e47, h2e48, h2e49, h2e50, h2e51, h2e52, h2e53, h2e54, h2e55, h2e56, h2e57, h2e58, h2e59, h2e60, h2e61, h2e62, h2e63, h2e64, h2e65, h2e66, h2e67, h2e68, h2e69, h2e70, h2e71, h2e72, h2e73, h2e74, h2e75, h2e76, h2e77, h2e78, h2e79, h2e80, h2e81, h2e82, h2e83, h2e84, h2e85, h2e86, h2e87, h2e88, h2e89, h2e90, h2e91, h2e92, h2e93, h2e94, h2e95, h2e96, h2e97, h2e98, h2e99, h2e100, h2e101, h2e102, h2e103, h2e104, h2e105, h2e106]
  grind

#print axioms homogeneous_horner2
end StackSorting.RationalLift
