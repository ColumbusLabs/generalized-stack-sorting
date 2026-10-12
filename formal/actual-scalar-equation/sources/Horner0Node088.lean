import Horner0Base
import Horner0Node087
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p88 : BiPoly.Poly := [[(Int.ofNat 11334272112), (Int.ofNat 51876920448), (Int.negSucc 386938511), (Int.negSucc 117607381919)], [(Int.negSucc 55350737135), (Int.negSucc 271587854591), (Int.negSucc 63802748015), (Int.ofNat 499836935520), (Int.negSucc 32206179455)], [(Int.ofNat 127681223088), (Int.ofNat 550394548464), (Int.ofNat 196386056736), (Int.negSucc 784538910191), (Int.ofNat 5716494816), (Int.ofNat 163447680)], [(Int.negSucc 178064829767), (Int.negSucc 557190165143), (Int.negSucc 305256175991), (Int.ofNat 290587276152), (Int.ofNat 190749836976), (Int.negSucc 5930748863)], [(Int.ofNat 156431794392), (Int.ofNat 322522002912), (Int.ofNat 315465914568), (Int.ofNat 448764922080), (Int.negSucc 292033356815), (Int.negSucc 9933711455)], [(Int.negSucc 84115250519), (Int.negSucc 144536544815), (Int.negSucc 210360383687), (Int.negSucc 501493375319), (Int.ofNat 37063605864), (Int.ofNat 18114343920)], [(Int.ofNat 25798576968), (Int.ofNat 72195143784), (Int.ofNat 95963233344), (Int.ofNat 177936495336), (Int.ofNat 138987742560), (Int.ofNat 4367532960)], [(Int.negSucc 3899610767), (Int.negSucc 30268582247), (Int.negSucc 36921536471), (Int.negSucc 16082736335), (Int.negSucc 70227627983), (Int.negSucc 11986831007)], [(Int.ofNat 184561632), (Int.ofNat 7538785848), (Int.ofNat 10378675584), (Int.negSucc 4449650399), (Int.ofNat 8656651008), (Int.ofNat 3426706944)], [(Int.ofNat 0), (Int.negSucc 883078847), (Int.negSucc 1212693551), (Int.ofNat 1106928288)]]

theorem h0n88_arithmetic : BiPoly.mul h0p8 h0p87=h0p88 := by
  decide +kernel

theorem h0n88 : h0e88.toBi mapPolyEnv=h0p88 := by
  change BiPoly.mul (h0e8.toBi mapPolyEnv) (h0e87.toBi mapPolyEnv)=h0p88
  rw [h0n8, h0n87]
  exact h0n88_arithmetic

#print axioms h0n88_arithmetic
end StackSorting.RationalLift
