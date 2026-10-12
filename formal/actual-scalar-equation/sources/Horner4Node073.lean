import Horner4Node070
import Horner4Node072
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p73 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 19356408000), (Int.ofNat 40771200312), (Int.negSucc 113123668175), (Int.ofNat 88205536440)], [(Int.ofNat 0), (Int.negSucc 84221881919), (Int.negSucc 146904167159), (Int.ofNat 542876712624), (Int.negSucc 418182875063), (Int.ofNat 24154634592)], [(Int.ofNat 0), (Int.ofNat 148764749040), (Int.ofNat 205581942576), (Int.negSucc 829478818151), (Int.ofNat 602161128360), (Int.negSucc 7542348695), (Int.negSucc 122585759)], [(Int.ofNat 0), (Int.negSucc 136226098079), (Int.negSucc 124891155107), (Int.ofNat 312876841356), (Int.ofNat 40947184620), (Int.negSucc 157259467835), (Int.ofNat 4448061648)], [(Int.ofNat 0), (Int.ofNat 68129776800), (Int.ofNat 3030817356), (Int.ofNat 367222809168), (Int.negSucc 686572331219), (Int.ofNat 225701209008), (Int.ofNat 7450283592)], [(Int.ofNat 0), (Int.negSucc 17669293919), (Int.ofNat 40698258804), (Int.negSucc 386549168255), (Int.ofNat 389809094220), (Int.ofNat 17665255116), (Int.negSucc 13585757939)], [(Int.ofNat 0), (Int.ofNat 1866340080), (Int.negSucc 22793718707), (Int.ofNat 101425031604), (Int.ofNat 55924454952), (Int.negSucc 134385533963), (Int.negSucc 3275649719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4783664376), (Int.ofNat 13847690268), (Int.negSucc 87353645075), (Int.ofNat 37690957584), (Int.ofNat 8990123256)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 276842447), (Int.negSucc 10298741219), (Int.ofNat 18447638328), (Int.ofNat 8138021184), (Int.negSucc 2570030207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1324618272), (Int.negSucc 987201431), (Int.negSucc 2624153759)]]

theorem h4n73_arithmetic : BiPoly.add h4p70 h4p72=h4p73 := by
  decide +kernel

theorem h4n73 : h4e73.toBi mapPolyEnv=h4p73 := by
  change BiPoly.add (h4e70.toBi mapPolyEnv) (h4e72.toBi mapPolyEnv)=h4p73
  rw [h4n70, h4n72]
  exact h4n73_arithmetic

#print axioms h4n73_arithmetic
end StackSorting.RationalLift
