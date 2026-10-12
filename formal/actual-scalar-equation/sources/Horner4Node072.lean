import BivariateRowEquality
import Horner4Base
import Horner4Node071
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p72 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17001408167), (Int.negSucc 43812564335), (Int.ofNat 88205536440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 83026105704), (Int.ofNat 241329570480), (Int.negSucc 386955018935), (Int.ofNat 24154634592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 191521834631), (Int.negSucc 442548153431), (Int.ofNat 590517221760), (Int.negSucc 4226078231), (Int.negSucc 122585759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 267097244652), (Int.ofNat 301590758412), (Int.negSucc 145297252835), (Int.negSucc 145286408555), (Int.ofNat 4448061648)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 234647691587), (Int.negSucc 14487621191), (Int.negSucc 444223629467), (Int.ofNat 215299875816), (Int.ofNat 7450283592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 126172875780), (Int.negSucc 35540934335), (Int.ofNat 386622444204), (Int.negSucc 21004825427), (Int.negSucc 13585757939)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 38697865451), (Int.negSucc 30896984771), (Int.negSucc 82150880471), (Int.negSucc 102602982059), (Int.negSucc 3275649719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5849416152), (Int.ofNat 33704041068), (Int.negSucc 12025777427), (Int.ofNat 48175659360), (Int.ofNat 8990123256)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 276842447), (Int.negSucc 10754493875), (Int.ofNat 5940974376), (Int.negSucc 5207473151), (Int.negSucc 2570030207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1324618272), (Int.negSucc 830196215)]]

theorem h4n72_arithmetic_row0 :
    (BiPoly.mul h4p61 h4p71).getD 0 []=h4p72.getD 0 [] := by
  decide +kernel

theorem h4n72_arithmetic_row1 :
    (BiPoly.mul h4p61 h4p71).getD 1 []=h4p72.getD 1 [] := by
  decide +kernel

theorem h4n72_arithmetic_row2 :
    (BiPoly.mul h4p61 h4p71).getD 2 []=h4p72.getD 2 [] := by
  decide +kernel

theorem h4n72_arithmetic_row3 :
    (BiPoly.mul h4p61 h4p71).getD 3 []=h4p72.getD 3 [] := by
  decide +kernel

theorem h4n72_arithmetic_row4 :
    (BiPoly.mul h4p61 h4p71).getD 4 []=h4p72.getD 4 [] := by
  decide +kernel

theorem h4n72_arithmetic_row5 :
    (BiPoly.mul h4p61 h4p71).getD 5 []=h4p72.getD 5 [] := by
  decide +kernel

theorem h4n72_arithmetic_row6 :
    (BiPoly.mul h4p61 h4p71).getD 6 []=h4p72.getD 6 [] := by
  decide +kernel

theorem h4n72_arithmetic_row7 :
    (BiPoly.mul h4p61 h4p71).getD 7 []=h4p72.getD 7 [] := by
  decide +kernel

theorem h4n72_arithmetic_row8 :
    (BiPoly.mul h4p61 h4p71).getD 8 []=h4p72.getD 8 [] := by
  decide +kernel

theorem h4n72_arithmetic_row9 :
    (BiPoly.mul h4p61 h4p71).getD 9 []=h4p72.getD 9 [] := by
  decide +kernel

theorem h4n72_arithmetic : BiPoly.mul h4p61 h4p71=h4p72 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p61 h4p71).getD j.val []=h4p72.getD j.val [] :=
      (fun j => Fin.cases h4n72_arithmetic_row0 (fun j => Fin.cases h4n72_arithmetic_row1 (fun j => Fin.cases h4n72_arithmetic_row2 (fun j => Fin.cases h4n72_arithmetic_row3 (fun j => Fin.cases h4n72_arithmetic_row4 (fun j => Fin.cases h4n72_arithmetic_row5 (fun j => Fin.cases h4n72_arithmetic_row6 (fun j => Fin.cases h4n72_arithmetic_row7 (fun j => Fin.cases h4n72_arithmetic_row8 (fun j => Fin.cases h4n72_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n72 : h4e72.toBi mapPolyEnv=h4p72 := by
  change BiPoly.mul (h4e61.toBi mapPolyEnv) (h4e71.toBi mapPolyEnv)=h4p72
  rw [h4n61, h4n71]
  exact h4n72_arithmetic

#print axioms h4n72_arithmetic
end StackSorting.RationalLift
