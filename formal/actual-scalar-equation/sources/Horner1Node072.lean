import BivariateRowEquality
import Horner1Node020
import Horner1Node071
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p72 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 419904), (Int.ofNat 1049760), (Int.ofNat 839808), (Int.ofNat 209952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2814911), (Int.negSucc 5684255), (Int.negSucc 3771359), (Int.negSucc 987551), (Int.negSucc 85535)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8164944), (Int.ofNat 13798440), (Int.ofNat 9653472), (Int.ofNat 4162608), (Int.ofNat 785808), (Int.negSucc 48311)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13364255), (Int.negSucc 21075407), (Int.negSucc 18862367), (Int.negSucc 9793247), (Int.negSucc 2129663), (Int.negSucc 51503), (Int.ofNat 11616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 13476784), (Int.ofNat 24170552), (Int.ofNat 26205104), (Int.ofNat 14268672), (Int.ofNat 4962608), (Int.ofNat 890824), (Int.negSucc 96975), (Int.ofNat 3872)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8556159), (Int.negSucc 21885407), (Int.negSucc 24610447), (Int.negSucc 16435935), (Int.negSucc 7599007), (Int.negSucc 1660959), (Int.ofNat 6224), (Int.ofNat 1760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3332016), (Int.ofNat 14542488), (Int.ofNat 16870672), (Int.ofNat 14862232), (Int.ofNat 6998080), (Int.ofNat 2246192), (Int.ofNat 499472), (Int.negSucc 39927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 725919), (Int.negSucc 6288847), (Int.negSucc 9540735), (Int.negSucc 8984959), (Int.negSucc 5032671), (Int.negSucc 2141791), (Int.negSucc 530303), (Int.negSucc 2783)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 67600), (Int.ofNat 1528680), (Int.ofNat 4225680), (Int.ofNat 3697904), (Int.ofNat 2927712), (Int.ofNat 1177680), (Int.ofNat 312576), (Int.ofNat 105408)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 155999), (Int.negSucc 1137263), (Int.negSucc 1317407), (Int.negSucc 1019999), (Int.negSucc 501407), (Int.negSucc 159839), (Int.negSucc 32831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 127440), (Int.ofNat 360936), (Int.ofNat 239040), (Int.ofNat 138528), (Int.ofNat 51840), (Int.ofNat 2592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 43199), (Int.negSucc 49247), (Int.negSucc 24191), (Int.negSucc 5183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5184), (Int.ofNat 2592)]]

theorem h1n72_arithmetic_row0 :
    (BiPoly.mul h1p20 h1p71).getD 0 []=h1p72.getD 0 [] := by
  decide +kernel

theorem h1n72_arithmetic_row1 :
    (BiPoly.mul h1p20 h1p71).getD 1 []=h1p72.getD 1 [] := by
  decide +kernel

theorem h1n72_arithmetic_row2 :
    (BiPoly.mul h1p20 h1p71).getD 2 []=h1p72.getD 2 [] := by
  decide +kernel

theorem h1n72_arithmetic_row3 :
    (BiPoly.mul h1p20 h1p71).getD 3 []=h1p72.getD 3 [] := by
  decide +kernel

theorem h1n72_arithmetic_row4 :
    (BiPoly.mul h1p20 h1p71).getD 4 []=h1p72.getD 4 [] := by
  decide +kernel

theorem h1n72_arithmetic_row5 :
    (BiPoly.mul h1p20 h1p71).getD 5 []=h1p72.getD 5 [] := by
  decide +kernel

theorem h1n72_arithmetic_row6 :
    (BiPoly.mul h1p20 h1p71).getD 6 []=h1p72.getD 6 [] := by
  decide +kernel

theorem h1n72_arithmetic_row7 :
    (BiPoly.mul h1p20 h1p71).getD 7 []=h1p72.getD 7 [] := by
  decide +kernel

theorem h1n72_arithmetic_row8 :
    (BiPoly.mul h1p20 h1p71).getD 8 []=h1p72.getD 8 [] := by
  decide +kernel

theorem h1n72_arithmetic_row9 :
    (BiPoly.mul h1p20 h1p71).getD 9 []=h1p72.getD 9 [] := by
  decide +kernel

theorem h1n72_arithmetic_row10 :
    (BiPoly.mul h1p20 h1p71).getD 10 []=h1p72.getD 10 [] := by
  decide +kernel

theorem h1n72_arithmetic_row11 :
    (BiPoly.mul h1p20 h1p71).getD 11 []=h1p72.getD 11 [] := by
  decide +kernel

theorem h1n72_arithmetic_row12 :
    (BiPoly.mul h1p20 h1p71).getD 12 []=h1p72.getD 12 [] := by
  decide +kernel

theorem h1n72_arithmetic : BiPoly.mul h1p20 h1p71=h1p72 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<13 at hk
    have hf : ∀ j : Fin 13, (BiPoly.mul h1p20 h1p71).getD j.val []=h1p72.getD j.val [] :=
      (fun j => Fin.cases h1n72_arithmetic_row0 (fun j => Fin.cases h1n72_arithmetic_row1 (fun j => Fin.cases h1n72_arithmetic_row2 (fun j => Fin.cases h1n72_arithmetic_row3 (fun j => Fin.cases h1n72_arithmetic_row4 (fun j => Fin.cases h1n72_arithmetic_row5 (fun j => Fin.cases h1n72_arithmetic_row6 (fun j => Fin.cases h1n72_arithmetic_row7 (fun j => Fin.cases h1n72_arithmetic_row8 (fun j => Fin.cases h1n72_arithmetic_row9 (fun j => Fin.cases h1n72_arithmetic_row10 (fun j => Fin.cases h1n72_arithmetic_row11 (fun j => Fin.cases h1n72_arithmetic_row12 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n72 : h1e72.toBi mapPolyEnv=h1p72 := by
  change BiPoly.mul (h1e20.toBi mapPolyEnv) (h1e71.toBi mapPolyEnv)=h1p72
  rw [h1n20, h1n71]
  exact h1n72_arithmetic

#print axioms h1n72_arithmetic
end StackSorting.RationalLift
