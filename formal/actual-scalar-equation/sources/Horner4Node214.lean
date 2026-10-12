import Horner4Base
import Horner4Node213
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p214 : BiPoly.Poly := [[(Int.ofNat 15112362816), (Int.ofNat 23832138816), (Int.negSucc 117349422911), (Int.ofNat 78404921280)], [(Int.negSucc 73800982847), (Int.negSucc 140714190911), (Int.ofNat 558475190592), (Int.negSucc 365430803135), (Int.ofNat 21470786304)], [(Int.ofNat 170241630784), (Int.ofNat 223134505600), (Int.negSucc 918280333503), (Int.ofNat 528660711104), (Int.negSucc 3647548863), (Int.negSucc 108965119)], [(Int.negSucc 237419773023), (Int.negSucc 30660901119), (Int.ofNat 397233787776), (Int.negSucc 9639359), (Int.negSucc 133097306847), (Int.ofNat 3953832576)], [(Int.ofNat 208575725856), (Int.negSucc 195697840351), (Int.ofNat 381987562912), (Int.negSucc 586243115807), (Int.ofNat 184755193088), (Int.ofNat 6622474304)], [(Int.negSucc 112153667359), (Int.ofNat 143745608992), (Int.negSucc 375256336479), (Int.ofNat 362335350784), (Int.negSucc 6594726655), (Int.negSucc 12076229279)], [(Int.ofNat 34398102624), (Int.negSucc 6934116159), (Int.ofNat 45559018400), (Int.ofNat 18179645856), (Int.negSucc 88290962079), (Int.negSucc 2911688639)], [(Int.negSucc 5199481023), (Int.negSucc 24759666591), (Int.ofNat 40648727552), (Int.negSucc 53512388255), (Int.ofNat 34831587648), (Int.ofNat 7991220672)], [(Int.ofNat 246082176), (Int.ofNat 9313467936), (Int.negSucc 14840416223), (Int.ofNat 9909731136), (Int.negSucc 2344393727), (Int.negSucc 2284471295)], [(Int.ofNat 0), (Int.negSucc 1177438463), (Int.ofNat 1915390656), (Int.negSucc 737952191)]]

theorem h4n214_arithmetic : BiPoly.mul h4p7 h4p213=h4p214 := by
  decide +kernel

theorem h4n214 : h4e214.toBi mapPolyEnv=h4p214 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e213.toBi mapPolyEnv)=h4p214
  rw [h4n7, h4n213]
  exact h4n214_arithmetic

#print axioms h4n214_arithmetic
end StackSorting.RationalLift
