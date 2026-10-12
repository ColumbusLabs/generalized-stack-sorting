import Horner1Node022
import Horner1Node025
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p26 : BiPoly.Poly := [[(Int.ofNat 25808544000), (Int.ofNat 88364416752), (Int.negSucc 63206428895), (Int.negSucc 58803690959)], [(Int.negSucc 112295842559), (Int.negSucc 361924434287), (Int.ofNat 241176475872), (Int.ofNat 216332871120), (Int.negSucc 16103089727)], [(Int.ofNat 198352998720), (Int.ofNat 657152926032), (Int.negSucc 220875450671), (Int.negSucc 378152939039), (Int.negSucc 1604308463), (Int.ofNat 81723840)], [(Int.negSucc 181634797439), (Int.negSucc 700716029447), (Int.negSucc 186012395015), (Int.ofNat 345190751832), (Int.ofNat 80893526664), (Int.negSucc 2965374431)], [(Int.ofNat 90839702400), (Int.ofNat 473336472984), (Int.ofNat 518605654608), (Int.negSucc 26982516023), (Int.negSucc 129664806287), (Int.negSucc 4966855727)], [(Int.negSucc 23559058559), (Int.negSucc 198081406487), (Int.negSucc 444317022335), (Int.negSucc 253499429447), (Int.ofNat 65563324344), (Int.ofNat 9057171960)], [(Int.ofNat 2488453440), (Int.ofNat 47004105960), (Int.ofNat 197027345016), (Int.ofNat 238867700880), (Int.ofNat 26025252168), (Int.ofNat 2183766480)], [(Int.ofNat 0), (Int.negSucc 5320613135), (Int.negSucc 48944495111), (Int.negSucc 92419971911), (Int.negSucc 46096708607), (Int.negSucc 5993415503)], [(Int.ofNat 0), (Int.ofNat 184561632), (Int.ofNat 7777332792), (Int.ofNat 12714902352), (Int.ofNat 21265641216), (Int.ofNat 1713353472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 883078847), (Int.ofNat 344123856), (Int.negSucc 3498871679)]]

theorem h1n26_arithmetic : BiPoly.add h1p22 h1p25=h1p26 := by
  decide +kernel

theorem h1n26 : h1e26.toBi mapPolyEnv=h1p26 := by
  change BiPoly.add (h1e22.toBi mapPolyEnv) (h1e25.toBi mapPolyEnv)=h1p26
  rw [h1n22, h1n25]
  exact h1n26_arithmetic

#print axioms h1n26_arithmetic
end StackSorting.RationalLift
