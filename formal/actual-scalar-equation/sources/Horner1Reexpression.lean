import Horner1Expressions
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem homogeneous_horner1 (v : Nat → FPS) :
    homogeneousExpr1.eval v=h1e132.eval v := by
  dsimp [homogeneousExpr1, IExpr.eval, h1e0, h1e1, h1e2, h1e3, h1e4, h1e5, h1e6, h1e7, h1e8, h1e9, h1e10, h1e11, h1e12, h1e13, h1e14, h1e15, h1e16, h1e17, h1e18, h1e19, h1e20, h1e21, h1e22, h1e23, h1e24, h1e25, h1e26, h1e27, h1e28, h1e29, h1e30, h1e31, h1e32, h1e33, h1e34, h1e35, h1e36, h1e37, h1e38, h1e39, h1e40, h1e41, h1e42, h1e43, h1e44, h1e45, h1e46, h1e47, h1e48, h1e49, h1e50, h1e51, h1e52, h1e53, h1e54, h1e55, h1e56, h1e57, h1e58, h1e59, h1e60, h1e61, h1e62, h1e63, h1e64, h1e65, h1e66, h1e67, h1e68, h1e69, h1e70, h1e71, h1e72, h1e73, h1e74, h1e75, h1e76, h1e77, h1e78, h1e79, h1e80, h1e81, h1e82, h1e83, h1e84, h1e85, h1e86, h1e87, h1e88, h1e89, h1e90, h1e91, h1e92, h1e93, h1e94, h1e95, h1e96, h1e97, h1e98, h1e99, h1e100, h1e101, h1e102, h1e103, h1e104, h1e105, h1e106, h1e107, h1e108, h1e109, h1e110, h1e111, h1e112, h1e113, h1e114, h1e115, h1e116, h1e117, h1e118, h1e119, h1e120, h1e121, h1e122, h1e123, h1e124, h1e125, h1e126, h1e127, h1e128, h1e129, h1e130, h1e131, h1e132]
  grind

#print axioms homogeneous_horner1
end StackSorting.RationalLift
