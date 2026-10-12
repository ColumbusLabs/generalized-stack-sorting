import BivariateRowEquality
import Horner1Node020
import Horner1Node061
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p62 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 104976), (Int.ofNat 419904), (Int.ofNat 524880), (Int.ofNat 209952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 703727), (Int.negSucc 2476655), (Int.negSucc 2546639), (Int.negSucc 859247), (Int.negSucc 85535)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2041236), (Int.ofNat 6511464), (Int.ofNat 6056856), (Int.ofNat 2838960), (Int.ofNat 858276), (Int.negSucc 48311)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3341063), (Int.negSucc 10280447), (Int.negSucc 10113071), (Int.negSucc 6822959), (Int.negSucc 2017559), (Int.negSucc 68927), (Int.ofNat 11616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3369196), (Int.ofNat 11096432), (Int.ofNat 13088336), (Int.ofNat 10125552), (Int.ofNat 3312212), (Int.ofNat 1047904), (Int.negSucc 102783), (Int.ofNat 3872)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2139039), (Int.negSucc 8679911), (Int.negSucc 12755359), (Int.negSucc 10036527), (Int.negSucc 5099455), (Int.negSucc 1665015), (Int.ofNat 3584), (Int.ofNat 1760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 833004), (Int.ofNat 4885128), (Int.ofNat 9046348), (Int.ofNat 7627720), (Int.ofNat 5366776), (Int.ofNat 1377200), (Int.ofNat 559364), (Int.negSucc 39927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 181479), (Int.negSucc 1844431), (Int.negSucc 4607391), (Int.negSucc 4712911), (Int.negSucc 3394191), (Int.negSucc 1354687), (Int.negSucc 526127), (Int.negSucc 2783)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 16900), (Int.ofNat 407520), (Int.ofNat 1617000), (Int.ofNat 2228816), (Int.ofNat 1466472), (Int.ofNat 1025040), (Int.ofNat 154464), (Int.ofNat 105408)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 38999), (Int.negSucc 342815), (Int.negSucc 726575), (Int.negSucc 550415), (Int.negSucc 360143), (Int.negSucc 110591), (Int.negSucc 32831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 31860), (Int.ofNat 138024), (Int.ofNat 171216), (Int.ofNat 68544), (Int.ofNat 47952), (Int.ofNat 2592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10799), (Int.negSucc 28511), (Int.negSucc 16415), (Int.negSucc 5183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1296), (Int.ofNat 2592)]]

theorem h1n62_arithmetic_row0 :
    (BiPoly.mul h1p20 h1p61).getD 0 []=h1p62.getD 0 [] := by
  decide +kernel

theorem h1n62_arithmetic_row1 :
    (BiPoly.mul h1p20 h1p61).getD 1 []=h1p62.getD 1 [] := by
  decide +kernel

theorem h1n62_arithmetic_row2 :
    (BiPoly.mul h1p20 h1p61).getD 2 []=h1p62.getD 2 [] := by
  decide +kernel

theorem h1n62_arithmetic_row3 :
    (BiPoly.mul h1p20 h1p61).getD 3 []=h1p62.getD 3 [] := by
  decide +kernel

theorem h1n62_arithmetic_row4 :
    (BiPoly.mul h1p20 h1p61).getD 4 []=h1p62.getD 4 [] := by
  decide +kernel

theorem h1n62_arithmetic_row5 :
    (BiPoly.mul h1p20 h1p61).getD 5 []=h1p62.getD 5 [] := by
  decide +kernel

theorem h1n62_arithmetic_row6 :
    (BiPoly.mul h1p20 h1p61).getD 6 []=h1p62.getD 6 [] := by
  decide +kernel

theorem h1n62_arithmetic_row7 :
    (BiPoly.mul h1p20 h1p61).getD 7 []=h1p62.getD 7 [] := by
  decide +kernel

theorem h1n62_arithmetic_row8 :
    (BiPoly.mul h1p20 h1p61).getD 8 []=h1p62.getD 8 [] := by
  decide +kernel

theorem h1n62_arithmetic_row9 :
    (BiPoly.mul h1p20 h1p61).getD 9 []=h1p62.getD 9 [] := by
  decide +kernel

theorem h1n62_arithmetic_row10 :
    (BiPoly.mul h1p20 h1p61).getD 10 []=h1p62.getD 10 [] := by
  decide +kernel

theorem h1n62_arithmetic_row11 :
    (BiPoly.mul h1p20 h1p61).getD 11 []=h1p62.getD 11 [] := by
  decide +kernel

theorem h1n62_arithmetic_row12 :
    (BiPoly.mul h1p20 h1p61).getD 12 []=h1p62.getD 12 [] := by
  decide +kernel

theorem h1n62_arithmetic : BiPoly.mul h1p20 h1p61=h1p62 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<13 at hk
    have hf : ∀ j : Fin 13, (BiPoly.mul h1p20 h1p61).getD j.val []=h1p62.getD j.val [] :=
      (fun j => Fin.cases h1n62_arithmetic_row0 (fun j => Fin.cases h1n62_arithmetic_row1 (fun j => Fin.cases h1n62_arithmetic_row2 (fun j => Fin.cases h1n62_arithmetic_row3 (fun j => Fin.cases h1n62_arithmetic_row4 (fun j => Fin.cases h1n62_arithmetic_row5 (fun j => Fin.cases h1n62_arithmetic_row6 (fun j => Fin.cases h1n62_arithmetic_row7 (fun j => Fin.cases h1n62_arithmetic_row8 (fun j => Fin.cases h1n62_arithmetic_row9 (fun j => Fin.cases h1n62_arithmetic_row10 (fun j => Fin.cases h1n62_arithmetic_row11 (fun j => Fin.cases h1n62_arithmetic_row12 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n62 : h1e62.toBi mapPolyEnv=h1p62 := by
  change BiPoly.mul (h1e20.toBi mapPolyEnv) (h1e61.toBi mapPolyEnv)=h1p62
  rw [h1n20, h1n61]
  exact h1n62_arithmetic

#print axioms h1n62_arithmetic
end StackSorting.RationalLift
