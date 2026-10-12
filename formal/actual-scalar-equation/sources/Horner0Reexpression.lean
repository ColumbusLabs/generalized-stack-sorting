import Horner0Expressions
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem homogeneous_horner0 (v : Nat → FPS) :
    homogeneousExpr0.eval v=h0e139.eval v := by
  dsimp [homogeneousExpr0, IExpr.eval, h0e0, h0e1, h0e2, h0e3, h0e4, h0e5, h0e6, h0e7, h0e8, h0e9, h0e10, h0e11, h0e12, h0e13, h0e14, h0e15, h0e16, h0e17, h0e18, h0e19, h0e20, h0e21, h0e22, h0e23, h0e24, h0e25, h0e26, h0e27, h0e28, h0e29, h0e30, h0e31, h0e32, h0e33, h0e34, h0e35, h0e36, h0e37, h0e38, h0e39, h0e40, h0e41, h0e42, h0e43, h0e44, h0e45, h0e46, h0e47, h0e48, h0e49, h0e50, h0e51, h0e52, h0e53, h0e54, h0e55, h0e56, h0e57, h0e58, h0e59, h0e60, h0e61, h0e62, h0e63, h0e64, h0e65, h0e66, h0e67, h0e68, h0e69, h0e70, h0e71, h0e72, h0e73, h0e74, h0e75, h0e76, h0e77, h0e78, h0e79, h0e80, h0e81, h0e82, h0e83, h0e84, h0e85, h0e86, h0e87, h0e88, h0e89, h0e90, h0e91, h0e92, h0e93, h0e94, h0e95, h0e96, h0e97, h0e98, h0e99, h0e100, h0e101, h0e102, h0e103, h0e104, h0e105, h0e106, h0e107, h0e108, h0e109, h0e110, h0e111, h0e112, h0e113, h0e114, h0e115, h0e116, h0e117, h0e118, h0e119, h0e120, h0e121, h0e122, h0e123, h0e124, h0e125, h0e126, h0e127, h0e128, h0e129, h0e130, h0e131, h0e132, h0e133, h0e134, h0e135, h0e136, h0e137, h0e138, h0e139]
  grind

#print axioms homogeneous_horner0
end StackSorting.RationalLift
