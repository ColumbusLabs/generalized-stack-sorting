import Horner4Base
import Horner4Node198
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p199 : BiPoly.Poly := [[(Int.negSucc 15112362815), (Int.negSucc 23832138815), (Int.ofNat 117349422912), (Int.negSucc 78404921279)], [(Int.ofNat 73800982848), (Int.ofNat 140714190912), (Int.negSucc 558475190591), (Int.ofNat 365430803136), (Int.negSucc 21470786303)], [(Int.negSucc 170241630783), (Int.negSucc 223134505599), (Int.ofNat 918280333504), (Int.negSucc 528660711103), (Int.ofNat 3647548864), (Int.ofNat 108965120)], [(Int.ofNat 237419773024), (Int.ofNat 30660901120), (Int.negSucc 397233787775), (Int.ofNat 9639360), (Int.ofNat 133097306848), (Int.negSucc 3953832575)], [(Int.negSucc 208575725855), (Int.ofNat 195697840352), (Int.negSucc 381987562911), (Int.ofNat 586243115808), (Int.negSucc 184755193087), (Int.negSucc 6622474303)], [(Int.ofNat 112153667360), (Int.negSucc 143745608991), (Int.ofNat 375256336480), (Int.negSucc 362335350783), (Int.ofNat 6594726656), (Int.ofNat 12076229280)], [(Int.negSucc 34398102623), (Int.ofNat 6934116160), (Int.negSucc 45559018399), (Int.negSucc 18179645855), (Int.ofNat 88290962080), (Int.ofNat 2911688640)], [(Int.ofNat 5199481024), (Int.ofNat 24759666592), (Int.negSucc 40648727551), (Int.ofNat 53512388256), (Int.negSucc 34831587647), (Int.negSucc 7991220671)], [(Int.negSucc 246082175), (Int.negSucc 9313467935), (Int.ofNat 14840416224), (Int.negSucc 9909731135), (Int.ofNat 2344393728), (Int.ofNat 2284471296)], [(Int.ofNat 0), (Int.ofNat 1177438464), (Int.negSucc 1915390655), (Int.ofNat 737952192)]]

theorem h4n199_arithmetic : BiPoly.mul h4p7 h4p198=h4p199 := by
  decide +kernel

theorem h4n199 : h4e199.toBi mapPolyEnv=h4p199 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e198.toBi mapPolyEnv)=h4p199
  rw [h4n7, h4n198]
  exact h4n199_arithmetic

#print axioms h4n199_arithmetic
end StackSorting.RationalLift
