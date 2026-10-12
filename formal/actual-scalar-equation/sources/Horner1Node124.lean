import Horner1Node121
import Horner1Node123
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p124 : BiPoly.Poly := [[(Int.ofNat 3226068000), (Int.ofNat 11990074770), (Int.negSucc 5466772259), (Int.negSucc 12250768949)], [(Int.negSucc 14036980319), (Int.negSucc 49853115713), (Int.ofNat 16739861124), (Int.ofNat 48539109942), (Int.negSucc 3354810359)], [(Int.ofNat 24794124840), (Int.ofNat 92784217678), (Int.negSucc 3023422809), (Int.negSucc 80075629699), (Int.ofNat 34243566), (Int.ofNat 17025800)], [(Int.negSucc 22704349679), (Int.negSucc 102428239494), (Int.negSucc 40006591510), (Int.ofNat 51220913581), (Int.ofNat 18183157975), (Int.negSucc 617786339)], [(Int.ofNat 11354962800), (Int.ofNat 72203041989), (Int.ofNat 65630574670), (Int.ofNat 21306276023), (Int.negSucc 28169204997), (Int.negSucc 1034761609)], [(Int.negSucc 2944882319), (Int.negSucc 31769780020), (Int.negSucc 53565131439), (Int.negSucc 53166453358), (Int.ofNat 9362350289), (Int.ofNat 1886910825)], [(Int.ofNat 311056680), (Int.ofNat 8025394659), (Int.ofNat 26344917281), (Int.ofNat 34422400414), (Int.ofNat 8953322191), (Int.ofNat 454951350)], [(Int.ofNat 0), (Int.negSucc 990044205), (Int.negSucc 7990508614), (Int.negSucc 10884397742), (Int.negSucc 8438514095), (Int.negSucc 1248628229)], [(Int.ofNat 0), (Int.ofNat 38450340), (Int.ofNat 1569638481), (Int.ofNat 1259308662), (Int.ofNat 2947509216), (Int.ofNat 356948640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 183974759), (Int.ofNat 89137494), (Int.negSucc 437358959)]]

theorem h1n124_arithmetic : BiPoly.add h1p121 h1p123=h1p124 := by
  decide +kernel

theorem h1n124 : h1e124.toBi mapPolyEnv=h1p124 := by
  change BiPoly.add (h1e121.toBi mapPolyEnv) (h1e123.toBi mapPolyEnv)=h1p124
  rw [h1n121, h1n123]
  exact h1n124_arithmetic

#print axioms h1n124_arithmetic
end StackSorting.RationalLift
