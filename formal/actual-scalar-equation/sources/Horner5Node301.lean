import BivariateRowEquality
import Horner5Base
import Horner5Node300
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p301 : BiPoly.Poly := [[(Int.ofNat 8602848000), (Int.ofNat 8471018880), (Int.negSucc 90761212799), (Int.ofNat 35933155200), (Int.ofNat 30804935040)], [(Int.negSucc 46034795519), (Int.negSucc 27195508223), (Int.ofNat 483670444032), (Int.negSucc 272144524031), (Int.negSucc 106262857727), (Int.ofNat 13879047168)], [(Int.ofNat 103549613760), (Int.ofNat 34150624992), (Int.negSucc 1031662635071), (Int.ofNat 588564773952), (Int.ofNat 118508005632), (Int.negSucc 2227273631), (Int.ofNat 1473897984)], [(Int.negSucc 126662598719), (Int.negSucc 31264770527), (Int.ofNat 1115435989728), (Int.negSucc 274122324191), (Int.negSucc 158888900831), (Int.negSucc 76554280127), (Int.ofNat 5321359680)], [(Int.ofNat 90824833280), (Int.ofNat 37657360384), (Int.negSucc 599567842911), (Int.negSucc 620370782239), (Int.ofNat 304042079104), (Int.ofNat 82500825568), (Int.negSucc 4622814751)], [(Int.negSucc 38132920319), (Int.negSucc 37077870079), (Int.ofNat 75082395744), (Int.ofNat 968070101184), (Int.negSucc 157396632895), (Int.negSucc 21921249567), (Int.negSucc 17186702463)], [(Int.ofNat 8682504000), (Int.ofNat 19839200800), (Int.ofNat 85880784800), (Int.negSucc 532748531487), (Int.negSucc 208606830943), (Int.ofNat 18444448896), (Int.ofNat 14125578624)], [(Int.negSucc 829484479), (Int.negSucc 5053723679), (Int.negSucc 45481965951), (Int.ofNat 99707244192), (Int.ofNat 269349307776), (Int.ofNat 422051328), (Int.ofNat 4659867456)], [(Int.ofNat 0), (Int.ofNat 473667456), (Int.ofNat 7606599168), (Int.ofNat 12157321728), (Int.negSucc 101165549951), (Int.negSucc 31400781311), (Int.negSucc 5931330815)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 202556735), (Int.negSucc 5020627199), (Int.ofNat 9717490752), (Int.ofNat 20196353664), (Int.ofNat 1166290560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 69780096), (Int.ofNat 956950272), (Int.negSucc 3498871679)]]

theorem h5n301_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p300).getD 0 []=h5p301.getD 0 [] := by
  decide +kernel

theorem h5n301_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p300).getD 1 []=h5p301.getD 1 [] := by
  decide +kernel

theorem h5n301_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p300).getD 2 []=h5p301.getD 2 [] := by
  decide +kernel

theorem h5n301_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p300).getD 3 []=h5p301.getD 3 [] := by
  decide +kernel

theorem h5n301_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p300).getD 4 []=h5p301.getD 4 [] := by
  decide +kernel

theorem h5n301_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p300).getD 5 []=h5p301.getD 5 [] := by
  decide +kernel

theorem h5n301_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p300).getD 6 []=h5p301.getD 6 [] := by
  decide +kernel

theorem h5n301_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p300).getD 7 []=h5p301.getD 7 [] := by
  decide +kernel

theorem h5n301_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p300).getD 8 []=h5p301.getD 8 [] := by
  decide +kernel

theorem h5n301_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p300).getD 9 []=h5p301.getD 9 [] := by
  decide +kernel

theorem h5n301_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p300).getD 10 []=h5p301.getD 10 [] := by
  decide +kernel

theorem h5n301_arithmetic : BiPoly.mul h5p6 h5p300=h5p301 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p300).getD j.val []=h5p301.getD j.val [] :=
      (fun j => Fin.cases h5n301_arithmetic_row0 (fun j => Fin.cases h5n301_arithmetic_row1 (fun j => Fin.cases h5n301_arithmetic_row2 (fun j => Fin.cases h5n301_arithmetic_row3 (fun j => Fin.cases h5n301_arithmetic_row4 (fun j => Fin.cases h5n301_arithmetic_row5 (fun j => Fin.cases h5n301_arithmetic_row6 (fun j => Fin.cases h5n301_arithmetic_row7 (fun j => Fin.cases h5n301_arithmetic_row8 (fun j => Fin.cases h5n301_arithmetic_row9 (fun j => Fin.cases h5n301_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n301 : h5e301.toBi mapPolyEnv=h5p301 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e300.toBi mapPolyEnv)=h5p301
  rw [h5n6, h5n300]
  exact h5n301_arithmetic

#print axioms h5n301_arithmetic
end StackSorting.RationalLift
