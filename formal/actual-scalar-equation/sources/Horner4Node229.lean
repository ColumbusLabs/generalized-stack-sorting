import Horner4Base
import Horner4Node228
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p229 : BiPoly.Poly := [[(Int.negSucc 3778090703), (Int.negSucc 5958034703), (Int.ofNat 29337355728), (Int.negSucc 19601230319)], [(Int.ofNat 18450245712), (Int.ofNat 35178547728), (Int.negSucc 139618797647), (Int.ofNat 91357700784), (Int.negSucc 5367696575)], [(Int.negSucc 42560407695), (Int.negSucc 55783626399), (Int.ofNat 229570083376), (Int.negSucc 132165177775), (Int.ofNat 911887216), (Int.ofNat 27241280)], [(Int.ofNat 59354943256), (Int.ofNat 7665225280), (Int.negSucc 99308446943), (Int.ofNat 2409840), (Int.ofNat 33274326712), (Int.negSucc 988458143)], [(Int.negSucc 52143931463), (Int.ofNat 48924460088), (Int.negSucc 95496890727), (Int.ofNat 146560778952), (Int.negSucc 46188798271), (Int.negSucc 1655618575)], [(Int.ofNat 28038416840), (Int.negSucc 35936402247), (Int.ofNat 93814084120), (Int.negSucc 90583837695), (Int.ofNat 1648681664), (Int.ofNat 3019057320)], [(Int.negSucc 8599525655), (Int.ofNat 1733529040), (Int.negSucc 11389754599), (Int.negSucc 4544911463), (Int.ofNat 22072740520), (Int.ofNat 727922160)], [(Int.ofNat 1299870256), (Int.ofNat 6189916648), (Int.negSucc 10162181887), (Int.ofNat 13378097064), (Int.negSucc 8707896911), (Int.negSucc 1997805167)], [(Int.negSucc 61520543), (Int.negSucc 2328366983), (Int.ofNat 3710104056), (Int.negSucc 2477432783), (Int.ofNat 586098432), (Int.ofNat 571117824)], [(Int.ofNat 0), (Int.ofNat 294359616), (Int.negSucc 478847663), (Int.ofNat 184488048)]]

theorem h4n229_arithmetic : BiPoly.mul h4p7 h4p228=h4p229 := by
  decide +kernel

theorem h4n229 : h4e229.toBi mapPolyEnv=h4p229 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e228.toBi mapPolyEnv)=h4p229
  rw [h4n7, h4n228]
  exact h4n229_arithmetic

#print axioms h4n229_arithmetic
end StackSorting.RationalLift
