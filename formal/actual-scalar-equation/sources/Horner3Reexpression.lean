import Horner3Expressions
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem homogeneous_horner3 (v : Nat → FPS) :
    homogeneousExpr3.eval v=h3e47.eval v := by
  dsimp [homogeneousExpr3, IExpr.eval, h3e0, h3e1, h3e2, h3e3, h3e4, h3e5, h3e6, h3e7, h3e8, h3e9, h3e10, h3e11, h3e12, h3e13, h3e14, h3e15, h3e16, h3e17, h3e18, h3e19, h3e20, h3e21, h3e22, h3e23, h3e24, h3e25, h3e26, h3e27, h3e28, h3e29, h3e30, h3e31, h3e32, h3e33, h3e34, h3e35, h3e36, h3e37, h3e38, h3e39, h3e40, h3e41, h3e42, h3e43, h3e44, h3e45, h3e46, h3e47]
  grind

#print axioms homogeneous_horner3
end StackSorting.RationalLift
