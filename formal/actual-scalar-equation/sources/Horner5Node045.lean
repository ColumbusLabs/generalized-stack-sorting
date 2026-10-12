import BivariateRowEquality
import Horner5Base
import Horner5Node044
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p45 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 38712816000), (Int.ofNat 76832400960), (Int.negSucc 254167424639), (Int.ofNat 138622207680)], [(Int.ofNat 0), (Int.negSucc 207156579839), (Int.negSucc 329536366847), (Int.ofNat 1432667471616), (Int.negSucc 942794411903), (Int.ofNat 62455712256)], [(Int.ofNat 0), (Int.ofNat 465973261920), (Int.ofNat 619651074384), (Int.negSucc 3090884259599), (Int.ofNat 2065793423472), (Int.negSucc 154831778639), (Int.ofNat 6632540928)], [(Int.ofNat 0), (Int.negSucc 569981694239), (Int.negSucc 710673161615), (Int.ofNat 3168825403680), (Int.negSucc 1221093763055), (Int.negSucc 343226826143), (Int.ofNat 10681036704)], [(Int.ofNat 0), (Int.ofNat 408711749760), (Int.ofNat 578169871488), (Int.negSucc 1302461922095), (Int.negSucc 1575462807359), (Int.ofNat 1274423938272), (Int.negSucc 68694903503)], [(Int.ofNat 0), (Int.negSucc 171598141439), (Int.negSucc 338448556799), (Int.negSucc 343774058831), (Int.ofNat 2719928892816), (Int.negSucc 919230612335), (Int.negSucc 35734828319)], [(Int.ofNat 0), (Int.ofNat 39071268000), (Int.ofNat 128347671600), (Int.ofNat 592953739200), (Int.negSucc 1398899597615), (Int.negSucc 404309335679), (Int.ofNat 218245425984)], [(Int.ofNat 0), (Int.negSucc 3732680159), (Int.negSucc 26474436719), (Int.negSucc 238608643823), (Int.ofNat 142194360960), (Int.ofNat 745552777248), (Int.negSucc 106160804063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2131503552), (Int.ofNat 36361199808), (Int.ofNat 95332154688), (Int.negSucc 278664406271), (Int.negSucc 68629795775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 911505311), (Int.negSucc 23504327711), (Int.ofNat 18401370048), (Int.ofNat 58630284864)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 314010432), (Int.ofNat 4620286656), (Int.negSucc 10496615039)]]

theorem h5n45_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p44).getD 0 []=h5p45.getD 0 [] := by
  decide +kernel

theorem h5n45_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p44).getD 1 []=h5p45.getD 1 [] := by
  decide +kernel

theorem h5n45_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p44).getD 2 []=h5p45.getD 2 [] := by
  decide +kernel

theorem h5n45_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p44).getD 3 []=h5p45.getD 3 [] := by
  decide +kernel

theorem h5n45_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p44).getD 4 []=h5p45.getD 4 [] := by
  decide +kernel

theorem h5n45_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p44).getD 5 []=h5p45.getD 5 [] := by
  decide +kernel

theorem h5n45_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p44).getD 6 []=h5p45.getD 6 [] := by
  decide +kernel

theorem h5n45_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p44).getD 7 []=h5p45.getD 7 [] := by
  decide +kernel

theorem h5n45_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p44).getD 8 []=h5p45.getD 8 [] := by
  decide +kernel

theorem h5n45_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p44).getD 9 []=h5p45.getD 9 [] := by
  decide +kernel

theorem h5n45_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p44).getD 10 []=h5p45.getD 10 [] := by
  decide +kernel

theorem h5n45_arithmetic : BiPoly.mul h5p6 h5p44=h5p45 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p44).getD j.val []=h5p45.getD j.val [] :=
      (fun j => Fin.cases h5n45_arithmetic_row0 (fun j => Fin.cases h5n45_arithmetic_row1 (fun j => Fin.cases h5n45_arithmetic_row2 (fun j => Fin.cases h5n45_arithmetic_row3 (fun j => Fin.cases h5n45_arithmetic_row4 (fun j => Fin.cases h5n45_arithmetic_row5 (fun j => Fin.cases h5n45_arithmetic_row6 (fun j => Fin.cases h5n45_arithmetic_row7 (fun j => Fin.cases h5n45_arithmetic_row8 (fun j => Fin.cases h5n45_arithmetic_row9 (fun j => Fin.cases h5n45_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n45 : h5e45.toBi mapPolyEnv=h5p45 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e44.toBi mapPolyEnv)=h5p45
  rw [h5n6, h5n44]
  exact h5n45_arithmetic

#print axioms h5n45_arithmetic
end StackSorting.RationalLift
