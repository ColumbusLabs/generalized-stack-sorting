import BivariateRowEquality
import Horner2Node060
import Horner2Node062
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p63 : BiPoly.Poly := [[(Int.negSucc 20155391), (Int.negSucc 60466175), (Int.negSucc 60466175), (Int.negSucc 20155391)], [(Int.ofNat 175426560), (Int.ofNat 461334528), (Int.ofNat 404600832), (Int.ofNat 126904320), (Int.ofNat 8211456)], [(Int.negSucc 682304255), (Int.negSucc 1599554303), (Int.negSucc 1324353023), (Int.negSucc 508239359), (Int.negSucc 96498431), (Int.ofNat 4637952)], [(Int.ofNat 1560434688), (Int.ofNat 3389331456), (Int.ofNat 2927600640), (Int.ofNat 1466440704), (Int.ofNat 365635584), (Int.negSucc 3216383), (Int.negSucc 1115135)], [(Int.negSucc 2321771519), (Int.negSucc 5006636543), (Int.negSucc 4874431487), (Int.negSucc 2919636479), (Int.negSucc 845406719), (Int.negSucc 103053311), (Int.ofNat 11911680), (Int.negSucc 371711)], [(Int.ofNat 2345951232), (Int.ofNat 5555467776), (Int.ofNat 6207143424), (Int.ofNat 4127606784), (Int.ofNat 1508376576), (Int.ofNat 356915712), (Int.negSucc 20906495), (Int.ofNat 574464)], [(Int.negSucc 1628213759), (Int.negSucc 4773331967), (Int.negSucc 6002799359), (Int.negSucc 4404973823), (Int.negSucc 2077264127), (Int.negSucc 575014655), (Int.negSucc 41243903), (Int.ofNat 3799296)], [(Int.ofNat 765413376), (Int.ofNat 3131149824), (Int.ofNat 4441709568), (Int.ofNat 3684963840), (Int.ofNat 2082631680), (Int.ofNat 634987008), (Int.ofNat 153778176), (Int.negSucc 7567871)], [(Int.negSucc 232869887), (Int.negSucc 1491580415), (Int.negSucc 2557890815), (Int.negSucc 2403032831), (Int.negSucc 1511500799), (Int.negSucc 573782015), (Int.negSucc 172954367), (Int.negSucc 6820607)], [(Int.ofNat 41333760), (Int.ofNat 476772864), (Int.ofNat 1135928832), (Int.ofNat 1199757312), (Int.ofNat 821222400), (Int.ofNat 400908288), (Int.ofNat 102610944), (Int.ofNat 23657472)], [(Int.negSucc 3244799), (Int.negSucc 89975039), (Int.negSucc 361492223), (Int.negSucc 458676479), (Int.negSucc 341881343), (Int.negSucc 190296575), (Int.negSucc 49001471), (Int.negSucc 16671743)], [(Int.ofNat 0), (Int.ofNat 7488000), (Int.ofNat 70566912), (Int.ofNat 131498496), (Int.ofNat 108481536), (Int.ofNat 58558464), (Int.ofNat 22146048), (Int.ofNat 3649536)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6117119), (Int.negSucc 24530687), (Int.negSucc 25657343), (Int.negSucc 12718079), (Int.negSucc 5723135), (Int.negSucc 248831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2073600), (Int.ofNat 3898368), (Int.ofNat 2322432), (Int.ofNat 497664)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 248831), (Int.negSucc 248831)]]

theorem h2n63_arithmetic_row0 :
    (BiPoly.mul h2p60 h2p62).getD 0 []=h2p63.getD 0 [] := by
  decide +kernel

theorem h2n63_arithmetic_row1 :
    (BiPoly.mul h2p60 h2p62).getD 1 []=h2p63.getD 1 [] := by
  decide +kernel

theorem h2n63_arithmetic_row2 :
    (BiPoly.mul h2p60 h2p62).getD 2 []=h2p63.getD 2 [] := by
  decide +kernel

theorem h2n63_arithmetic_row3 :
    (BiPoly.mul h2p60 h2p62).getD 3 []=h2p63.getD 3 [] := by
  decide +kernel

theorem h2n63_arithmetic_row4 :
    (BiPoly.mul h2p60 h2p62).getD 4 []=h2p63.getD 4 [] := by
  decide +kernel

theorem h2n63_arithmetic_row5 :
    (BiPoly.mul h2p60 h2p62).getD 5 []=h2p63.getD 5 [] := by
  decide +kernel

theorem h2n63_arithmetic_row6 :
    (BiPoly.mul h2p60 h2p62).getD 6 []=h2p63.getD 6 [] := by
  decide +kernel

theorem h2n63_arithmetic_row7 :
    (BiPoly.mul h2p60 h2p62).getD 7 []=h2p63.getD 7 [] := by
  decide +kernel

theorem h2n63_arithmetic_row8 :
    (BiPoly.mul h2p60 h2p62).getD 8 []=h2p63.getD 8 [] := by
  decide +kernel

theorem h2n63_arithmetic_row9 :
    (BiPoly.mul h2p60 h2p62).getD 9 []=h2p63.getD 9 [] := by
  decide +kernel

theorem h2n63_arithmetic_row10 :
    (BiPoly.mul h2p60 h2p62).getD 10 []=h2p63.getD 10 [] := by
  decide +kernel

theorem h2n63_arithmetic_row11 :
    (BiPoly.mul h2p60 h2p62).getD 11 []=h2p63.getD 11 [] := by
  decide +kernel

theorem h2n63_arithmetic_row12 :
    (BiPoly.mul h2p60 h2p62).getD 12 []=h2p63.getD 12 [] := by
  decide +kernel

theorem h2n63_arithmetic_row13 :
    (BiPoly.mul h2p60 h2p62).getD 13 []=h2p63.getD 13 [] := by
  decide +kernel

theorem h2n63_arithmetic_row14 :
    (BiPoly.mul h2p60 h2p62).getD 14 []=h2p63.getD 14 [] := by
  decide +kernel

theorem h2n63_arithmetic : BiPoly.mul h2p60 h2p62=h2p63 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<15 at hk
    have hf : ∀ j : Fin 15, (BiPoly.mul h2p60 h2p62).getD j.val []=h2p63.getD j.val [] :=
      (fun j => Fin.cases h2n63_arithmetic_row0 (fun j => Fin.cases h2n63_arithmetic_row1 (fun j => Fin.cases h2n63_arithmetic_row2 (fun j => Fin.cases h2n63_arithmetic_row3 (fun j => Fin.cases h2n63_arithmetic_row4 (fun j => Fin.cases h2n63_arithmetic_row5 (fun j => Fin.cases h2n63_arithmetic_row6 (fun j => Fin.cases h2n63_arithmetic_row7 (fun j => Fin.cases h2n63_arithmetic_row8 (fun j => Fin.cases h2n63_arithmetic_row9 (fun j => Fin.cases h2n63_arithmetic_row10 (fun j => Fin.cases h2n63_arithmetic_row11 (fun j => Fin.cases h2n63_arithmetic_row12 (fun j => Fin.cases h2n63_arithmetic_row13 (fun j => Fin.cases h2n63_arithmetic_row14 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n63 : h2e63.toBi mapPolyEnv=h2p63 := by
  change BiPoly.mul (h2e60.toBi mapPolyEnv) (h2e62.toBi mapPolyEnv)=h2p63
  rw [h2n60, h2n62]
  exact h2n63_arithmetic

#print axioms h2n63_arithmetic
end StackSorting.RationalLift
