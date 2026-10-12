import BivariateRowEquality
import Horner5Base
import Horner5Node101
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p102 : BiPoly.Poly := [[(Int.negSucc 6452135999), (Int.negSucc 6353264159), (Int.ofNat 68070909600), (Int.negSucc 26949866399), (Int.negSucc 23103701279)], [(Int.ofNat 34526096640), (Int.ofNat 20396631168), (Int.negSucc 362752833023), (Int.ofNat 204108393024), (Int.ofNat 79697143296), (Int.negSucc 10409285375)], [(Int.negSucc 77662210319), (Int.negSucc 25612968743), (Int.ofNat 773746976304), (Int.negSucc 441423580463), (Int.negSucc 88881004223), (Int.ofNat 1670455224), (Int.negSucc 1105423487)], [(Int.ofNat 94996949040), (Int.ofNat 23448577896), (Int.negSucc 836576992295), (Int.ofNat 205591743144), (Int.ofNat 119166675624), (Int.ofNat 57415710096), (Int.negSucc 3991019759)], [(Int.negSucc 68118624959), (Int.negSucc 28243020287), (Int.ofNat 449675882184), (Int.ofNat 465278086680), (Int.negSucc 228031559327), (Int.negSucc 61875619175), (Int.ofNat 3467111064)], [(Int.ofNat 28599690240), (Int.ofNat 27808402560), (Int.negSucc 56311796807), (Int.negSucc 726052575887), (Int.ofNat 118047474672), (Int.ofNat 16440937176), (Int.ofNat 12890026848)], [(Int.negSucc 6511877999), (Int.negSucc 14879400599), (Int.negSucc 64410588599), (Int.ofNat 399561398616), (Int.ofNat 156455123208), (Int.negSucc 13833336671), (Int.negSucc 10594183967)], [(Int.ofNat 622113360), (Int.ofNat 3790292760), (Int.ofNat 34111474464), (Int.negSucc 74780433143), (Int.negSucc 202011980831), (Int.negSucc 316538495), (Int.negSucc 3494900591)], [(Int.ofNat 0), (Int.negSucc 355250591), (Int.negSucc 5704949375), (Int.negSucc 9117991295), (Int.ofNat 75874162464), (Int.ofNat 23550585984), (Int.ofNat 4448498112)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 151917552), (Int.ofNat 3765470400), (Int.negSucc 7288118063), (Int.negSucc 15147265247), (Int.negSucc 874717919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 52335071), (Int.negSucc 717712703), (Int.ofNat 2624153760)]]

theorem h5n102_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p101).getD 0 []=h5p102.getD 0 [] := by
  decide +kernel

theorem h5n102_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p101).getD 1 []=h5p102.getD 1 [] := by
  decide +kernel

theorem h5n102_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p101).getD 2 []=h5p102.getD 2 [] := by
  decide +kernel

theorem h5n102_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p101).getD 3 []=h5p102.getD 3 [] := by
  decide +kernel

theorem h5n102_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p101).getD 4 []=h5p102.getD 4 [] := by
  decide +kernel

theorem h5n102_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p101).getD 5 []=h5p102.getD 5 [] := by
  decide +kernel

theorem h5n102_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p101).getD 6 []=h5p102.getD 6 [] := by
  decide +kernel

theorem h5n102_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p101).getD 7 []=h5p102.getD 7 [] := by
  decide +kernel

theorem h5n102_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p101).getD 8 []=h5p102.getD 8 [] := by
  decide +kernel

theorem h5n102_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p101).getD 9 []=h5p102.getD 9 [] := by
  decide +kernel

theorem h5n102_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p101).getD 10 []=h5p102.getD 10 [] := by
  decide +kernel

theorem h5n102_arithmetic : BiPoly.mul h5p6 h5p101=h5p102 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p101).getD j.val []=h5p102.getD j.val [] :=
      (fun j => Fin.cases h5n102_arithmetic_row0 (fun j => Fin.cases h5n102_arithmetic_row1 (fun j => Fin.cases h5n102_arithmetic_row2 (fun j => Fin.cases h5n102_arithmetic_row3 (fun j => Fin.cases h5n102_arithmetic_row4 (fun j => Fin.cases h5n102_arithmetic_row5 (fun j => Fin.cases h5n102_arithmetic_row6 (fun j => Fin.cases h5n102_arithmetic_row7 (fun j => Fin.cases h5n102_arithmetic_row8 (fun j => Fin.cases h5n102_arithmetic_row9 (fun j => Fin.cases h5n102_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n102 : h5e102.toBi mapPolyEnv=h5p102 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e101.toBi mapPolyEnv)=h5p102
  rw [h5n6, h5n101]
  exact h5n102_arithmetic

#print axioms h5n102_arithmetic
end StackSorting.RationalLift
