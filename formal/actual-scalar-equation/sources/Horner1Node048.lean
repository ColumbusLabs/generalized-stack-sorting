import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p48 : BiPoly.Poly := [[(Int.negSucc 12904271999), (Int.negSucc 38515072319), (Int.ofNat 46207402560)], [(Int.ofNat 56147921280), (Int.ofNat 153286848576), (Int.negSucc 201031428095), (Int.ofNat 20818570752)], [(Int.negSucc 99176499359), (Int.negSucc 264735851471), (Int.ofNat 257953776480), (Int.negSucc 7762604399), (Int.ofNat 2210846976)], [(Int.ofNat 90817398720), (Int.ofNat 261325599840), (Int.negSucc 7524055295), (Int.negSucc 124162958303), (Int.ofNat 7982039520)], [(Int.negSucc 45419851199), (Int.negSucc 158452339295), (Int.negSucc 254473620239), (Int.ofNat 161565801168), (Int.negSucc 6934222127)], [(Int.ofNat 11779529280), (Int.ofNat 56983077984), (Int.ofNat 234005489280), (Int.negSucc 2124433343), (Int.negSucc 25780053695)], [(Int.negSucc 1244226719), (Int.negSucc 10602764495), (Int.negSucc 88214677583), (Int.negSucc 92050223615), (Int.ofNat 21188367936)], [(Int.ofNat 0), (Int.ofNat 710501184), (Int.ofNat 13237567200), (Int.ofNat 50218578432), (Int.ofNat 6989801184)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 303835103), (Int.negSucc 8337775967), (Int.negSucc 8896996223)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 104670144), (Int.ofNat 1749435840)]]

theorem h1n48_arithmetic : BiPoly.mul h1p47 h1p6=h1p48 := by
  decide +kernel

theorem h1n48 : h1e48.toBi mapPolyEnv=h1p48 := by
  change BiPoly.mul (h1e47.toBi mapPolyEnv) (h1e6.toBi mapPolyEnv)=h1p48
  rw [h1n47, h1n6]
  exact h1n48_arithmetic

#print axioms h1n48_arithmetic
end StackSorting.RationalLift
