import Horner4Expressions
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

theorem homogeneous_horner4 (v : Nat → FPS) :
    homogeneousExpr4.eval v=h4e265.eval v := by
  dsimp [homogeneousExpr4, IExpr.eval, h4e0, h4e1, h4e2, h4e3, h4e4, h4e5, h4e6, h4e7, h4e8, h4e9, h4e10, h4e11, h4e12, h4e13, h4e14, h4e15, h4e16, h4e17, h4e18, h4e19, h4e20, h4e21, h4e22, h4e23, h4e24, h4e25, h4e26, h4e27, h4e28, h4e29, h4e30, h4e31, h4e32, h4e33, h4e34, h4e35, h4e36, h4e37, h4e38, h4e39, h4e40, h4e41, h4e42, h4e43, h4e44, h4e45, h4e46, h4e47, h4e48, h4e49, h4e50, h4e51, h4e52, h4e53, h4e54, h4e55, h4e56, h4e57, h4e58, h4e59, h4e60, h4e61, h4e62, h4e63, h4e64, h4e65, h4e66, h4e67, h4e68, h4e69, h4e70, h4e71, h4e72, h4e73, h4e74, h4e75, h4e76, h4e77, h4e78, h4e79, h4e80, h4e81, h4e82, h4e83, h4e84, h4e85, h4e86, h4e87, h4e88, h4e89, h4e90, h4e91, h4e92, h4e93, h4e94, h4e95, h4e96, h4e97, h4e98, h4e99, h4e100, h4e101, h4e102, h4e103, h4e104, h4e105, h4e106, h4e107, h4e108, h4e109, h4e110, h4e111, h4e112, h4e113, h4e114, h4e115, h4e116, h4e117, h4e118, h4e119, h4e120, h4e121, h4e122, h4e123, h4e124, h4e125, h4e126, h4e127, h4e128, h4e129, h4e130, h4e131, h4e132, h4e133, h4e134, h4e135, h4e136, h4e137, h4e138, h4e139, h4e140, h4e141, h4e142, h4e143, h4e144, h4e145, h4e146, h4e147, h4e148, h4e149, h4e150, h4e151, h4e152, h4e153, h4e154, h4e155, h4e156, h4e157, h4e158, h4e159, h4e160, h4e161, h4e162, h4e163, h4e164, h4e165, h4e166, h4e167, h4e168, h4e169, h4e170, h4e171, h4e172, h4e173, h4e174, h4e175, h4e176, h4e177, h4e178, h4e179, h4e180, h4e181, h4e182, h4e183, h4e184, h4e185, h4e186, h4e187, h4e188, h4e189, h4e190, h4e191, h4e192, h4e193, h4e194, h4e195, h4e196, h4e197, h4e198, h4e199, h4e200, h4e201, h4e202, h4e203, h4e204, h4e205, h4e206, h4e207, h4e208, h4e209, h4e210, h4e211, h4e212, h4e213, h4e214, h4e215, h4e216, h4e217, h4e218, h4e219, h4e220, h4e221, h4e222, h4e223, h4e224, h4e225, h4e226, h4e227, h4e228, h4e229, h4e230, h4e231, h4e232, h4e233, h4e234, h4e235, h4e236, h4e237, h4e238, h4e239, h4e240, h4e241, h4e242, h4e243, h4e244, h4e245, h4e246, h4e247, h4e248, h4e249, h4e250, h4e251, h4e252, h4e253, h4e254, h4e255, h4e256, h4e257, h4e258, h4e259, h4e260, h4e261, h4e262, h4e263, h4e264, h4e265]
  grind

#print axioms homogeneous_horner4
end StackSorting.RationalLift
