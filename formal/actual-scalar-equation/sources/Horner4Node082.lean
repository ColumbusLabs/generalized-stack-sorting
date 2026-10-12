import Horner4Node077
import Horner4Node081
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p82 : BiPoly.Poly := [[(Int.negSucc 12904271999), (Int.negSucc 27180800207), (Int.ofNat 86750050896), (Int.negSucc 29595314735), (Int.negSucc 58803690959)], [(Int.ofNat 56147921280), (Int.ofNat 97936111440), (Int.negSucc 417268545551), (Int.ofNat 117902203056), (Int.ofNat 241866922896), (Int.negSucc 16103089727)], [(Int.negSucc 99176499359), (Int.negSucc 137054628383), (Int.ofNat 680667101856), (Int.negSucc 106408649951), (Int.negSucc 388649915375), (Int.ofNat 2899109328), (Int.ofNat 81723840)], [(Int.ofNat 90817398720), (Int.ofNat 83260770072), (Int.negSucc 386649390671), (Int.negSucc 228358628687), (Int.ofNat 201704480448), (Int.ofNat 93892231272), (Int.negSucc 2965374431)], [(Int.negSucc 45419851199), (Int.negSucc 2020544903), (Int.negSucc 88383411719), (Int.ofNat 467373301608), (Int.ofNat 145681613640), (Int.negSucc 148500106271), (Int.negSucc 4966855727)], [(Int.ofNat 11779529280), (Int.negSucc 27132172535), (Int.ofNat 173584194984), (Int.negSucc 236178773255), (Int.negSucc 269525132879), (Int.ofNat 23060388912), (Int.ofNat 9057171960)], [(Int.negSucc 1244226719), (Int.ofNat 15195812472), (Int.negSucc 41818110767), (Int.negSucc 16684980119), (Int.ofNat 144357609624), (Int.ofNat 70585754520), (Int.ofNat 2183766480)], [(Int.ofNat 0), (Int.negSucc 3189109583), (Int.negSucc 13131404279), (Int.ofNat 35766402672), (Int.negSucc 17110120103), (Int.negSucc 38110521743), (Int.negSucc 5993415503)], [(Int.ofNat 0), (Int.ofNat 184561632), (Int.ofNat 7050389112), (Int.negSucc 5128762967), (Int.negSucc 9385997039), (Int.ofNat 5185002240), (Int.ofNat 1713353472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 883078847), (Int.negSucc 224944559), (Int.ofNat 2302899984)]]

theorem h4n82_arithmetic : BiPoly.add h4p77 h4p81=h4p82 := by
  decide +kernel

theorem h4n82 : h4e82.toBi mapPolyEnv=h4p82 := by
  change BiPoly.add (h4e77.toBi mapPolyEnv) (h4e81.toBi mapPolyEnv)=h4p82
  rw [h4n77, h4n81]
  exact h4n82_arithmetic

#print axioms h4n82_arithmetic
end StackSorting.RationalLift
