import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p36 : BiPoly.Poly := [[(Int.ofNat 6452136000), (Int.ofNat 19257536160), (Int.negSucc 23103701279)], [(Int.negSucc 28073960639), (Int.negSucc 76643424287), (Int.ofNat 100515714048), (Int.negSucc 10409285375)], [(Int.ofNat 49588249680), (Int.ofNat 132367925736), (Int.negSucc 128976888239), (Int.ofNat 3881302200), (Int.negSucc 1105423487)], [(Int.negSucc 45408699359), (Int.negSucc 130662799919), (Int.ofNat 3762027648), (Int.ofNat 62081479152), (Int.negSucc 3991019759)], [(Int.ofNat 22709925600), (Int.ofNat 79226169648), (Int.ofNat 127236810120), (Int.negSucc 80782900583), (Int.ofNat 3467111064)], [(Int.negSucc 5889764639), (Int.negSucc 28491538991), (Int.negSucc 117002744639), (Int.ofNat 1062216672), (Int.ofNat 12890026848)], [(Int.ofNat 622113360), (Int.ofNat 5301382248), (Int.ofNat 44107338792), (Int.ofNat 46025111808), (Int.negSucc 10594183967)], [(Int.ofNat 0), (Int.negSucc 355250591), (Int.negSucc 6618783599), (Int.negSucc 25109289215), (Int.negSucc 3494900591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 151917552), (Int.ofNat 4168887984), (Int.ofNat 4448498112)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 52335071), (Int.negSucc 874717919)]]

theorem h2n36_arithmetic : BiPoly.mul h2p21 h2p35=h2p36 := by
  decide +kernel

theorem h2n36 : h2e36.toBi mapPolyEnv=h2p36 := by
  change BiPoly.mul (h2e21.toBi mapPolyEnv) (h2e35.toBi mapPolyEnv)=h2p36
  rw [h2n21, h2n35]
  exact h2n36_arithmetic

#print axioms h2n36_arithmetic
end StackSorting.RationalLift
