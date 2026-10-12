import BivariateRowEquality
import Horner5Base
import Horner5Node109
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p110 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 25502112252), (Int.ofNat 91220958756), (Int.negSucc 66589458155), (Int.negSucc 132308304659)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 150041270807), (Int.negSucc 552252360779), (Int.ofNat 350746477344), (Int.ofNat 544200576516), (Int.negSucc 36231951887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 411821910504), (Int.ofNat 1313099337816), (Int.negSucc 802386130895), (Int.negSucc 843204763403), (Int.ofNat 6522995988), (Int.ofNat 183878640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 687928618925), (Int.negSucc 1516854234743), (Int.ofNat 651335574276), (Int.ofNat 429536374740), (Int.ofNat 211073641722), (Int.negSucc 6672092471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 752617404360), (Int.ofNat 826089106788), (Int.ofNat 470120996736), (Int.ofNat 125456017644), (Int.negSucc 327453146639), (Int.negSucc 11175425387)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 541230851051), (Int.negSucc 157679343953), (Int.negSucc 1192957709003), (Int.negSucc 225476614439), (Int.ofNat 63061300440), (Int.ofNat 20378636910)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 247306111848), (Int.ofNat 51080873832), (Int.ofNat 749505464172), (Int.ofNat 245623555656), (Int.ofNat 138439310760), (Int.ofNat 4913474580)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 66820922405), (Int.negSucc 105675662987), (Int.negSucc 155743716167), (Int.negSucc 208129295987), (Int.negSucc 90662148503), (Int.negSucc 13485184883)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9189387900), (Int.ofNat 67103066088), (Int.negSucc 10818386891), (Int.ofNat 71163237204), (Int.ofNat 25151439924), (Int.ofNat 3855045312)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 415263671), (Int.negSucc 18118668221), (Int.ofNat 8169828480), (Int.negSucc 6565915403), (Int.negSucc 3855045311)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1986927408), (Int.negSucc 1245294323)]]

theorem h5n110_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p109).getD 0 []=h5p110.getD 0 [] := by
  decide +kernel

theorem h5n110_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p109).getD 1 []=h5p110.getD 1 [] := by
  decide +kernel

theorem h5n110_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p109).getD 2 []=h5p110.getD 2 [] := by
  decide +kernel

theorem h5n110_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p109).getD 3 []=h5p110.getD 3 [] := by
  decide +kernel

theorem h5n110_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p109).getD 4 []=h5p110.getD 4 [] := by
  decide +kernel

theorem h5n110_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p109).getD 5 []=h5p110.getD 5 [] := by
  decide +kernel

theorem h5n110_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p109).getD 6 []=h5p110.getD 6 [] := by
  decide +kernel

theorem h5n110_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p109).getD 7 []=h5p110.getD 7 [] := by
  decide +kernel

theorem h5n110_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p109).getD 8 []=h5p110.getD 8 [] := by
  decide +kernel

theorem h5n110_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p109).getD 9 []=h5p110.getD 9 [] := by
  decide +kernel

theorem h5n110_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p109).getD 10 []=h5p110.getD 10 [] := by
  decide +kernel

theorem h5n110_arithmetic : BiPoly.mul h5p22 h5p109=h5p110 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p22 h5p109).getD j.val []=h5p110.getD j.val [] :=
      (fun j => Fin.cases h5n110_arithmetic_row0 (fun j => Fin.cases h5n110_arithmetic_row1 (fun j => Fin.cases h5n110_arithmetic_row2 (fun j => Fin.cases h5n110_arithmetic_row3 (fun j => Fin.cases h5n110_arithmetic_row4 (fun j => Fin.cases h5n110_arithmetic_row5 (fun j => Fin.cases h5n110_arithmetic_row6 (fun j => Fin.cases h5n110_arithmetic_row7 (fun j => Fin.cases h5n110_arithmetic_row8 (fun j => Fin.cases h5n110_arithmetic_row9 (fun j => Fin.cases h5n110_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n110 : h5e110.toBi mapPolyEnv=h5p110 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e109.toBi mapPolyEnv)=h5p110
  rw [h5n22, h5n109]
  exact h5n110_arithmetic

#print axioms h5n110_arithmetic
end StackSorting.RationalLift
