import BivariateRowEquality
import Horner5Base
import Horner5Node083
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p84 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 38712815999), (Int.negSucc 76832400959), (Int.ofNat 254167424640), (Int.negSucc 138622207679)], [(Int.ofNat 0), (Int.ofNat 207156579840), (Int.ofNat 329536366848), (Int.negSucc 1432667471615), (Int.ofNat 942794411904), (Int.negSucc 62455712255)], [(Int.ofNat 0), (Int.negSucc 465973261919), (Int.negSucc 619651074383), (Int.ofNat 3090884259600), (Int.negSucc 2065793423471), (Int.ofNat 154831778640), (Int.negSucc 6632540927)], [(Int.ofNat 0), (Int.ofNat 569981694240), (Int.ofNat 710673161616), (Int.negSucc 3168825403679), (Int.ofNat 1221093763056), (Int.ofNat 343226826144), (Int.negSucc 10681036703)], [(Int.ofNat 0), (Int.negSucc 408711749759), (Int.negSucc 578169871487), (Int.ofNat 1302461922096), (Int.ofNat 1575462807360), (Int.negSucc 1274423938271), (Int.ofNat 68694903504)], [(Int.ofNat 0), (Int.ofNat 171598141440), (Int.ofNat 338448556800), (Int.ofNat 343774058832), (Int.negSucc 2719928892815), (Int.ofNat 919230612336), (Int.ofNat 35734828320)], [(Int.ofNat 0), (Int.negSucc 39071267999), (Int.negSucc 128347671599), (Int.negSucc 592953739199), (Int.ofNat 1398899597616), (Int.ofNat 404309335680), (Int.negSucc 218245425983)], [(Int.ofNat 0), (Int.ofNat 3732680160), (Int.ofNat 26474436720), (Int.ofNat 238608643824), (Int.negSucc 142194360959), (Int.negSucc 745552777247), (Int.ofNat 106160804064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2131503551), (Int.negSucc 36361199807), (Int.negSucc 95332154687), (Int.ofNat 278664406272), (Int.ofNat 68629795776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 911505312), (Int.ofNat 23504327712), (Int.negSucc 18401370047), (Int.negSucc 58630284863)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 314010431), (Int.negSucc 4620286655), (Int.ofNat 10496615040)]]

theorem h5n84_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p83).getD 0 []=h5p84.getD 0 [] := by
  decide +kernel

theorem h5n84_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p83).getD 1 []=h5p84.getD 1 [] := by
  decide +kernel

theorem h5n84_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p83).getD 2 []=h5p84.getD 2 [] := by
  decide +kernel

theorem h5n84_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p83).getD 3 []=h5p84.getD 3 [] := by
  decide +kernel

theorem h5n84_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p83).getD 4 []=h5p84.getD 4 [] := by
  decide +kernel

theorem h5n84_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p83).getD 5 []=h5p84.getD 5 [] := by
  decide +kernel

theorem h5n84_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p83).getD 6 []=h5p84.getD 6 [] := by
  decide +kernel

theorem h5n84_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p83).getD 7 []=h5p84.getD 7 [] := by
  decide +kernel

theorem h5n84_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p83).getD 8 []=h5p84.getD 8 [] := by
  decide +kernel

theorem h5n84_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p83).getD 9 []=h5p84.getD 9 [] := by
  decide +kernel

theorem h5n84_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p83).getD 10 []=h5p84.getD 10 [] := by
  decide +kernel

theorem h5n84_arithmetic : BiPoly.mul h5p6 h5p83=h5p84 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p83).getD j.val []=h5p84.getD j.val [] :=
      (fun j => Fin.cases h5n84_arithmetic_row0 (fun j => Fin.cases h5n84_arithmetic_row1 (fun j => Fin.cases h5n84_arithmetic_row2 (fun j => Fin.cases h5n84_arithmetic_row3 (fun j => Fin.cases h5n84_arithmetic_row4 (fun j => Fin.cases h5n84_arithmetic_row5 (fun j => Fin.cases h5n84_arithmetic_row6 (fun j => Fin.cases h5n84_arithmetic_row7 (fun j => Fin.cases h5n84_arithmetic_row8 (fun j => Fin.cases h5n84_arithmetic_row9 (fun j => Fin.cases h5n84_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n84 : h5e84.toBi mapPolyEnv=h5p84 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e83.toBi mapPolyEnv)=h5p84
  rw [h5n6, h5n83]
  exact h5n84_arithmetic

#print axioms h5n84_arithmetic
end StackSorting.RationalLift
