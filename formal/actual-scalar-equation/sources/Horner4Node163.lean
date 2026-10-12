import BivariateRowEquality
import Horner4Base
import Horner4Node162
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p163 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 17001408168), (Int.ofNat 77815380672), (Int.negSucc 580407767), (Int.negSucc 176411072879)], [(Int.ofNat 0), (Int.negSucc 83026105703), (Int.negSucc 407381781887), (Int.negSucc 95704122023), (Int.ofNat 749755403280), (Int.negSucc 48309269183)], [(Int.ofNat 0), (Int.ofNat 191521834632), (Int.ofNat 825591822696), (Int.ofNat 294579085104), (Int.negSucc 1176808365287), (Int.ofNat 8574742224), (Int.ofNat 245171520)], [(Int.ofNat 0), (Int.negSucc 267097244651), (Int.negSucc 835785247715), (Int.negSucc 457884263987), (Int.ofNat 435880914228), (Int.ofNat 286124755464), (Int.negSucc 8896123295)], [(Int.ofNat 0), (Int.ofNat 234647691588), (Int.ofNat 483783004368), (Int.ofNat 473198871852), (Int.ofNat 673147383120), (Int.negSucc 438050035223), (Int.negSucc 14900567183)], [(Int.ofNat 0), (Int.negSucc 126172875779), (Int.negSucc 216804817223), (Int.negSucc 315540575531), (Int.negSucc 752240062979), (Int.ofNat 55595408796), (Int.ofNat 27171515880)], [(Int.ofNat 0), (Int.ofNat 38697865452), (Int.ofNat 108292715676), (Int.ofNat 143944850016), (Int.ofNat 266904743004), (Int.ofNat 208481613840), (Int.ofNat 6551299440)], [(Int.ofNat 0), (Int.negSucc 5849416151), (Int.negSucc 45402873371), (Int.negSucc 55382304707), (Int.negSucc 24124104503), (Int.negSucc 105341441975), (Int.negSucc 17980246511)], [(Int.ofNat 0), (Int.ofNat 276842448), (Int.ofNat 11308178772), (Int.ofNat 15568013376), (Int.negSucc 6674475599), (Int.ofNat 12984976512), (Int.ofNat 5140060416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1324618271), (Int.negSucc 1819040327), (Int.ofNat 1660392432)]]

theorem h4n163_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p162).getD 0 []=h4p163.getD 0 [] := by
  decide +kernel

theorem h4n163_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p162).getD 1 []=h4p163.getD 1 [] := by
  decide +kernel

theorem h4n163_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p162).getD 2 []=h4p163.getD 2 [] := by
  decide +kernel

theorem h4n163_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p162).getD 3 []=h4p163.getD 3 [] := by
  decide +kernel

theorem h4n163_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p162).getD 4 []=h4p163.getD 4 [] := by
  decide +kernel

theorem h4n163_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p162).getD 5 []=h4p163.getD 5 [] := by
  decide +kernel

theorem h4n163_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p162).getD 6 []=h4p163.getD 6 [] := by
  decide +kernel

theorem h4n163_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p162).getD 7 []=h4p163.getD 7 [] := by
  decide +kernel

theorem h4n163_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p162).getD 8 []=h4p163.getD 8 [] := by
  decide +kernel

theorem h4n163_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p162).getD 9 []=h4p163.getD 9 [] := by
  decide +kernel

theorem h4n163_arithmetic : BiPoly.mul h4p7 h4p162=h4p163 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p162).getD j.val []=h4p163.getD j.val [] :=
      (fun j => Fin.cases h4n163_arithmetic_row0 (fun j => Fin.cases h4n163_arithmetic_row1 (fun j => Fin.cases h4n163_arithmetic_row2 (fun j => Fin.cases h4n163_arithmetic_row3 (fun j => Fin.cases h4n163_arithmetic_row4 (fun j => Fin.cases h4n163_arithmetic_row5 (fun j => Fin.cases h4n163_arithmetic_row6 (fun j => Fin.cases h4n163_arithmetic_row7 (fun j => Fin.cases h4n163_arithmetic_row8 (fun j => Fin.cases h4n163_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n163 : h4e163.toBi mapPolyEnv=h4p163 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e162.toBi mapPolyEnv)=h4p163
  rw [h4n7, h4n162]
  exact h4n163_arithmetic

#print axioms h4n163_arithmetic
end StackSorting.RationalLift
