import Horner1Base
import Horner1Node024
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p123 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 2361306690), (Int.ofNat 6085078380), (Int.negSucc 12250768949)], [(Int.ofNat 0), (Int.negSucc 11531403569), (Int.negSucc 33517995899), (Int.ofNat 53743752630), (Int.negSucc 3354810359)], [(Int.ofNat 0), (Int.ofNat 26600254810), (Int.ofNat 61465021310), (Int.negSucc 82016280799), (Int.ofNat 586955310), (Int.ofNat 17025800)], [(Int.ofNat 0), (Int.negSucc 37096839534), (Int.negSucc 41887605334), (Int.ofNat 20180174005), (Int.ofNat 20178667855), (Int.negSucc 617786339)], [(Int.ofNat 0), (Int.ofNat 32589957165), (Int.ofNat 2012169610), (Int.ofNat 61697726315), (Int.negSucc 29902760529), (Int.negSucc 1034761609)], [(Int.ofNat 0), (Int.negSucc 17524010524), (Int.ofNat 4936240880), (Int.negSucc 53697561694), (Int.ofNat 2917336865), (Int.ofNat 1886910825)], [(Int.ofNat 0), (Int.ofNat 5374703535), (Int.ofNat 4291247885), (Int.ofNat 11409844510), (Int.ofNat 14250414175), (Int.ofNat 454951350)], [(Int.ofNat 0), (Int.negSucc 812418909), (Int.negSucc 4681116814), (Int.ofNat 1670246865), (Int.negSucc 6691063799), (Int.negSucc 1248628229)], [(Int.ofNat 0), (Int.ofNat 38450340), (Int.ofNat 1493679705), (Int.negSucc 825135329), (Int.ofNat 723260160), (Int.ofNat 356948640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 183974759), (Int.ofNat 115305030)]]

theorem h1n123_arithmetic : BiPoly.mul h1p122 h1p24=h1p123 := by
  decide +kernel

theorem h1n123 : h1e123.toBi mapPolyEnv=h1p123 := by
  change BiPoly.mul (h1e122.toBi mapPolyEnv) (h1e24.toBi mapPolyEnv)=h1p123
  rw [h1n122, h1n24]
  exact h1n123_arithmetic

#print axioms h1n123_arithmetic
end StackSorting.RationalLift
