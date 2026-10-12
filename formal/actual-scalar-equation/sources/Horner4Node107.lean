import BivariateRowEquality
import Horner4Base
import Horner4Node106
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p107 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 5667136055), (Int.negSucc 31605596279), (Int.negSucc 14410718855), (Int.ofNat 88205536440)], [(Int.ofNat 0), (Int.ofNat 27675368568), (Int.ofNat 163469295864), (Int.ofNat 112344564168), (Int.negSucc 378903474071), (Int.ofNat 24154634592)], [(Int.ofNat 0), (Int.negSucc 63840611543), (Int.negSucc 339037885775), (Int.negSucc 245709079511), (Int.ofNat 589108529016), (Int.negSucc 4266940151), (Int.negSucc 122585759)], [(Int.ofNat 0), (Int.ofNat 89032414884), (Int.ofNat 367627497456), (Int.ofNat 253158340800), (Int.negSucc 193726055687), (Int.negSucc 143803721339), (Int.ofNat 4448061648)], [(Int.ofNat 0), (Int.negSucc 78215897195), (Int.negSucc 239476898651), (Int.negSucc 162562164347), (Int.negSucc 372457004195), (Int.ofNat 217783303680), (Int.ofNat 7450283592)], [(Int.ofNat 0), (Int.ofNat 42057625260), (Int.ofNat 114325897668), (Int.ofNat 93333213732), (Int.ofNat 379620835728), (Int.negSucc 25533411407), (Int.negSucc 13585757939)], [(Int.ofNat 0), (Int.negSucc 12899288483), (Int.negSucc 48996860375), (Int.negSucc 58280611595), (Int.negSucc 116351874491), (Int.negSucc 103694865299), (Int.negSucc 3275649719)], [(Int.ofNat 0), (Int.ofNat 1949805384), (Int.ofNat 17084096508), (Int.ofNat 29695448592), (Int.ofNat 4032775692), (Int.ofNat 51172367112), (Int.ofNat 8990123256)], [(Int.ofNat 0), (Int.negSucc 92280815), (Int.negSucc 3861673739), (Int.negSucc 8774169083), (Int.ofNat 4205149992), (Int.negSucc 6064149887), (Int.negSucc 2570030207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 441539424), (Int.ofNat 1047886200), (Int.negSucc 830196215)]]

theorem h4n107_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p106).getD 0 []=h4p107.getD 0 [] := by
  decide +kernel

theorem h4n107_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p106).getD 1 []=h4p107.getD 1 [] := by
  decide +kernel

theorem h4n107_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p106).getD 2 []=h4p107.getD 2 [] := by
  decide +kernel

theorem h4n107_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p106).getD 3 []=h4p107.getD 3 [] := by
  decide +kernel

theorem h4n107_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p106).getD 4 []=h4p107.getD 4 [] := by
  decide +kernel

theorem h4n107_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p106).getD 5 []=h4p107.getD 5 [] := by
  decide +kernel

theorem h4n107_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p106).getD 6 []=h4p107.getD 6 [] := by
  decide +kernel

theorem h4n107_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p106).getD 7 []=h4p107.getD 7 [] := by
  decide +kernel

theorem h4n107_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p106).getD 8 []=h4p107.getD 8 [] := by
  decide +kernel

theorem h4n107_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p106).getD 9 []=h4p107.getD 9 [] := by
  decide +kernel

theorem h4n107_arithmetic : BiPoly.mul h4p7 h4p106=h4p107 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p106).getD j.val []=h4p107.getD j.val [] :=
      (fun j => Fin.cases h4n107_arithmetic_row0 (fun j => Fin.cases h4n107_arithmetic_row1 (fun j => Fin.cases h4n107_arithmetic_row2 (fun j => Fin.cases h4n107_arithmetic_row3 (fun j => Fin.cases h4n107_arithmetic_row4 (fun j => Fin.cases h4n107_arithmetic_row5 (fun j => Fin.cases h4n107_arithmetic_row6 (fun j => Fin.cases h4n107_arithmetic_row7 (fun j => Fin.cases h4n107_arithmetic_row8 (fun j => Fin.cases h4n107_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n107 : h4e107.toBi mapPolyEnv=h4p107 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e106.toBi mapPolyEnv)=h4p107
  rw [h4n7, h4n106]
  exact h4n107_arithmetic

#print axioms h4n107_arithmetic
end StackSorting.RationalLift
