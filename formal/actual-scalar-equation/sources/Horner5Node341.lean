import BivariateRowEquality
import Horner5Base
import Horner5Node340
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p341 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 28335680280), (Int.ofNat 101356620840), (Int.negSucc 73988286839), (Int.negSucc 147009227399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 166712523119), (Int.negSucc 613613734199), (Int.ofNat 389718308160), (Int.ofNat 604667307240), (Int.negSucc 40257724319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 457579900560), (Int.ofNat 1458999264240), (Int.negSucc 891540145439), (Int.negSucc 936894181559), (Int.ofNat 7247773320), (Int.ofNat 204309600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 764365132139), (Int.negSucc 1685393594159), (Int.ofNat 723706193640), (Int.ofNat 477262638600), (Int.ofNat 234526268580), (Int.negSucc 7413436079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 836241560400), (Int.ofNat 917876785320), (Int.ofNat 522356663040), (Int.ofNat 139395575160), (Int.negSucc 363836829599), (Int.negSucc 12417139319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 601367612279), (Int.negSucc 175199271059), (Int.negSucc 1325508565559), (Int.negSucc 250529571599), (Int.ofNat 70068111600), (Int.ofNat 22642929900)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 274784568720), (Int.ofNat 56756526480), (Int.ofNat 832783849080), (Int.ofNat 272915061840), (Int.ofNat 153821456400), (Int.ofNat 5459416200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 74245469339), (Int.negSucc 117417403319), (Int.negSucc 173048573519), (Int.negSucc 231254773319), (Int.negSucc 100735720559), (Int.negSucc 14983538759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10210431000), (Int.ofNat 74558962320), (Int.negSucc 12020429879), (Int.ofNat 79070263560), (Int.ofNat 27946044360), (Int.ofNat 4283383680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 461404079), (Int.negSucc 20131853579), (Int.ofNat 9077587200), (Int.negSucc 7295461559), (Int.negSucc 4283383679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2207697120), (Int.negSucc 1383660359)]]

theorem h5n341_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p340).getD 0 []=h5p341.getD 0 [] := by
  decide +kernel

theorem h5n341_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p340).getD 1 []=h5p341.getD 1 [] := by
  decide +kernel

theorem h5n341_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p340).getD 2 []=h5p341.getD 2 [] := by
  decide +kernel

theorem h5n341_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p340).getD 3 []=h5p341.getD 3 [] := by
  decide +kernel

theorem h5n341_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p340).getD 4 []=h5p341.getD 4 [] := by
  decide +kernel

theorem h5n341_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p340).getD 5 []=h5p341.getD 5 [] := by
  decide +kernel

theorem h5n341_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p340).getD 6 []=h5p341.getD 6 [] := by
  decide +kernel

theorem h5n341_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p340).getD 7 []=h5p341.getD 7 [] := by
  decide +kernel

theorem h5n341_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p340).getD 8 []=h5p341.getD 8 [] := by
  decide +kernel

theorem h5n341_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p340).getD 9 []=h5p341.getD 9 [] := by
  decide +kernel

theorem h5n341_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p340).getD 10 []=h5p341.getD 10 [] := by
  decide +kernel

theorem h5n341_arithmetic : BiPoly.mul h5p22 h5p340=h5p341 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p22 h5p340).getD j.val []=h5p341.getD j.val [] :=
      (fun j => Fin.cases h5n341_arithmetic_row0 (fun j => Fin.cases h5n341_arithmetic_row1 (fun j => Fin.cases h5n341_arithmetic_row2 (fun j => Fin.cases h5n341_arithmetic_row3 (fun j => Fin.cases h5n341_arithmetic_row4 (fun j => Fin.cases h5n341_arithmetic_row5 (fun j => Fin.cases h5n341_arithmetic_row6 (fun j => Fin.cases h5n341_arithmetic_row7 (fun j => Fin.cases h5n341_arithmetic_row8 (fun j => Fin.cases h5n341_arithmetic_row9 (fun j => Fin.cases h5n341_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n341 : h5e341.toBi mapPolyEnv=h5p341 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e340.toBi mapPolyEnv)=h5p341
  rw [h5n22, h5n340]
  exact h5n341_arithmetic

#print axioms h5n341_arithmetic
end StackSorting.RationalLift
