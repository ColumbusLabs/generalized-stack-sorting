import Horner2Base
import Horner2Node074
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p75 : BiPoly.Poly := [[(Int.negSucc 944522675), (Int.negSucc 9990212759), (Int.negSucc 14571943235), (Int.ofNat 39202460640)], [(Int.ofNat 4612561428), (Int.ofNat 50307689784), (Int.ofNat 85760085828), (Int.negSucc 170638084271), (Int.ofNat 10735393152)], [(Int.negSucc 10640101923), (Int.negSucc 109706823915), (Int.negSucc 163881555871), (Int.ofNat 262217316436), (Int.negSucc 1885067311), (Int.negSucc 54482559)], [(Int.ofNat 14838735814), (Int.ofNat 135464928646), (Int.ofNat 125968267470), (Int.negSucc 72648023957), (Int.negSucc 64324622599), (Int.ofNat 1976916288)], [(Int.negSucc 13035982865), (Int.negSucc 105092730771), (Int.negSucc 31118033277), (Int.negSucc 185471619995), (Int.ofNat 96102738340), (Int.ofNat 3311237152)], [(Int.ofNat 7009604210), (Int.ofNat 54102337328), (Int.ofNat 5683053862), (Int.ofNat 170665262678), (Int.negSucc 10090242297), (Int.negSucc 6038114639)], [(Int.negSucc 2149881413), (Int.negSucc 18915550465), (Int.negSucc 18295931035), (Int.negSucc 42211668101), (Int.negSucc 45783305899), (Int.negSucc 1455844319)], [(Int.ofNat 324967564), (Int.ofNat 4472187238), (Int.ofNat 14311475062), (Int.negSucc 2668364447), (Int.ofNat 21910855452), (Int.ofNat 3995610336)], [(Int.negSucc 15380135), (Int.negSucc 720512969), (Int.negSucc 4449720923), (Int.ofNat 2351128992), (Int.negSucc 2457211967), (Int.negSucc 1142235647)], [(Int.ofNat 0), (Int.ofNat 73589904), (Int.ofNat 542597220), (Int.negSucc 368976095)]]

theorem h2n75_arithmetic : BiPoly.mul h2p5 h2p74=h2p75 := by
  decide +kernel

theorem h2n75 : h2e75.toBi mapPolyEnv=h2p75 := by
  change BiPoly.mul (h2e5.toBi mapPolyEnv) (h2e74.toBi mapPolyEnv)=h2p75
  rw [h2n5, h2n74]
  exact h2n75_arithmetic

#print axioms h2n75_arithmetic
end StackSorting.RationalLift
