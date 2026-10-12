import BivariateRowEquality
import Horner5Base
import Horner5Node321
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p322 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 112962816), (Int.ofNat 836204832), (Int.negSucc 4566372767), (Int.negSucc 4643999135), (Int.ofNat 3182782752), (Int.ofNat 2537167104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 542812415), (Int.negSucc 3317453615), (Int.ofNat 23706761376), (Int.ofNat 13973574624), (Int.negSucc 12432231263), (Int.negSucc 3227977199), (Int.ofNat 704768640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1036213440), (Int.ofNat 4880599680), (Int.negSucc 47914075871), (Int.negSucc 17800364255), (Int.ofNat 8921273280), (Int.negSucc 150731903), (Int.ofNat 1245267840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 967982111), (Int.negSucc 2847571919), (Int.ofNat 47550666240), (Int.ofNat 22456874976), (Int.ofNat 10788408960), (Int.negSucc 2374556303), (Int.negSucc 1574137727)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 411537408), (Int.negSucc 190439519), (Int.negSucc 23355066431), (Int.negSucc 30780114719), (Int.negSucc 16257093695), (Int.ofNat 2076177312), (Int.negSucc 559179071)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 18886847), (Int.ofNat 1054412016), (Int.ofNat 4543416288), (Int.ofNat 24692885856), (Int.ofNat 8830457280), (Int.ofNat 3080337120), (Int.ofNat 566752896)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 39842495), (Int.negSucc 503733887), (Int.ofNat 23134176), (Int.negSucc 8847701279), (Int.negSucc 4987878047), (Int.negSucc 2748667391), (Int.negSucc 52140671)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8810208), (Int.ofNat 92787984), (Int.ofNat 55645056), (Int.ofNat 854702496), (Int.ofNat 2491254144), (Int.ofNat 506725632)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4805567), (Int.negSucc 44108063), (Int.ofNat 93104640), (Int.negSucc 454584959)]]

theorem h5n322_arithmetic_row0 :
    (BiPoly.mul h5p3 h5p321).getD 0 []=h5p322.getD 0 [] := by
  decide +kernel

theorem h5n322_arithmetic_row1 :
    (BiPoly.mul h5p3 h5p321).getD 1 []=h5p322.getD 1 [] := by
  decide +kernel

theorem h5n322_arithmetic_row2 :
    (BiPoly.mul h5p3 h5p321).getD 2 []=h5p322.getD 2 [] := by
  decide +kernel

theorem h5n322_arithmetic_row3 :
    (BiPoly.mul h5p3 h5p321).getD 3 []=h5p322.getD 3 [] := by
  decide +kernel

theorem h5n322_arithmetic_row4 :
    (BiPoly.mul h5p3 h5p321).getD 4 []=h5p322.getD 4 [] := by
  decide +kernel

theorem h5n322_arithmetic_row5 :
    (BiPoly.mul h5p3 h5p321).getD 5 []=h5p322.getD 5 [] := by
  decide +kernel

theorem h5n322_arithmetic_row6 :
    (BiPoly.mul h5p3 h5p321).getD 6 []=h5p322.getD 6 [] := by
  decide +kernel

theorem h5n322_arithmetic_row7 :
    (BiPoly.mul h5p3 h5p321).getD 7 []=h5p322.getD 7 [] := by
  decide +kernel

theorem h5n322_arithmetic_row8 :
    (BiPoly.mul h5p3 h5p321).getD 8 []=h5p322.getD 8 [] := by
  decide +kernel

theorem h5n322_arithmetic : BiPoly.mul h5p3 h5p321=h5p322 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<9 at hk
    have hf : ∀ j : Fin 9, (BiPoly.mul h5p3 h5p321).getD j.val []=h5p322.getD j.val [] :=
      (fun j => Fin.cases h5n322_arithmetic_row0 (fun j => Fin.cases h5n322_arithmetic_row1 (fun j => Fin.cases h5n322_arithmetic_row2 (fun j => Fin.cases h5n322_arithmetic_row3 (fun j => Fin.cases h5n322_arithmetic_row4 (fun j => Fin.cases h5n322_arithmetic_row5 (fun j => Fin.cases h5n322_arithmetic_row6 (fun j => Fin.cases h5n322_arithmetic_row7 (fun j => Fin.cases h5n322_arithmetic_row8 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n322 : h5e322.toBi mapPolyEnv=h5p322 := by
  change BiPoly.mul (h5e3.toBi mapPolyEnv) (h5e321.toBi mapPolyEnv)=h5p322
  rw [h5n3, h5n321]
  exact h5n322_arithmetic

#print axioms h5n322_arithmetic
end StackSorting.RationalLift
