import Horner1Node048
import Horner1Node050
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p51 : BiPoly.Poly := [[(Int.negSucc 12904271999), (Int.negSucc 47015776403), (Int.ofNat 24301120392), (Int.ofNat 44102768220)], [(Int.ofNat 56147921280), (Int.ofNat 194799901428), (Int.negSucc 80366642855), (Int.negSucc 172658938715), (Int.ofNat 12077317296)], [(Int.negSucc 99176499359), (Int.negSucc 360496768787), (Int.ofNat 36679699764), (Int.ofNat 287496006480), (Int.ofNat 97807860), (Int.negSucc 61292879)], [(Int.ofNat 90817398720), (Int.ofNat 394874222166), (Int.ofNat 143271323910), (Int.negSucc 196811584721), (Int.negSucc 64661164757), (Int.ofNat 2224030824)], [(Int.negSucc 45419851199), (Int.negSucc 275776185089), (Int.negSucc 261717430835), (Int.negSucc 60546013565), (Int.ofNat 100715715780), (Int.ofNat 3725141796)], [(Int.ofNat 11779529280), (Int.ofNat 120069515874), (Int.ofNat 216235022112), (Int.ofNat 191186788758), (Int.negSucc 36282466409), (Int.negSucc 6792878969)], [(Int.negSucc 1244226719), (Int.negSucc 29951697221), (Int.negSucc 103663169969), (Int.negSucc 133125663851), (Int.negSucc 30113123093), (Int.negSucc 1637824859)], [(Int.ofNat 0), (Int.ofNat 3635209260), (Int.ofNat 30089587734), (Int.ofNat 44205689718), (Int.ofNat 31077630864), (Int.ofNat 4495061628)], [(Int.ofNat 0), (Int.negSucc 138421223), (Int.negSucc 5681082041), (Int.negSucc 5367288779), (Int.negSucc 11500732799), (Int.negSucc 1285015103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 662309136), (Int.negSucc 310427963), (Int.ofNat 1749435840)]]

theorem h1n51_arithmetic : BiPoly.add h1p48 h1p50=h1p51 := by
  decide +kernel

theorem h1n51 : h1e51.toBi mapPolyEnv=h1p51 := by
  change BiPoly.add (h1e48.toBi mapPolyEnv) (h1e50.toBi mapPolyEnv)=h1p51
  rw [h1n48, h1n50]
  exact h1n51_arithmetic

#print axioms h1n51_arithmetic
end StackSorting.RationalLift
