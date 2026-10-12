import BivariateRowEquality
import Horner4Base
import Horner4Node010
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p87 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8706816), (Int.negSucc 9664187), (Int.ofNat 90904872), (Int.negSucc 48917243), (Int.negSucc 105715295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 32256463), (Int.ofNat 36644638), (Int.negSucc 473549633), (Int.ofNat 135326642), (Int.ofNat 288699378), (Int.negSucc 29365359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 47168280), (Int.negSucc 13402305), (Int.ofNat 893344012), (Int.negSucc 80551389), (Int.negSucc 257964479), (Int.negSucc 15132415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 35069627), (Int.negSucc 74148087), (Int.negSucc 763715547), (Int.negSucc 276429285), (Int.negSucc 25390241), (Int.ofNat 120027336)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14493284), (Int.ofNat 98211592), (Int.ofNat 316578468), (Int.ofNat 522692754), (Int.ofNat 172213548), (Int.negSucc 77904503)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3409379), (Int.negSucc 44925365), (Int.negSucc 81601049), (Int.negSucc 315486647), (Int.negSucc 135404603), (Int.negSucc 37586879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 367092), (Int.ofNat 7483950), (Int.ofNat 22107276), (Int.ofNat 70552224), (Int.ofNat 64107504), (Int.ofNat 41239152)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 200231), (Int.negSucc 3517451), (Int.negSucc 3445631), (Int.negSucc 18941039)]]

theorem h4n87_arithmetic_row0 :
    (BiPoly.mul h4p4 h4p10).getD 0 []=h4p87.getD 0 [] := by
  decide +kernel

theorem h4n87_arithmetic_row1 :
    (BiPoly.mul h4p4 h4p10).getD 1 []=h4p87.getD 1 [] := by
  decide +kernel

theorem h4n87_arithmetic_row2 :
    (BiPoly.mul h4p4 h4p10).getD 2 []=h4p87.getD 2 [] := by
  decide +kernel

theorem h4n87_arithmetic_row3 :
    (BiPoly.mul h4p4 h4p10).getD 3 []=h4p87.getD 3 [] := by
  decide +kernel

theorem h4n87_arithmetic_row4 :
    (BiPoly.mul h4p4 h4p10).getD 4 []=h4p87.getD 4 [] := by
  decide +kernel

theorem h4n87_arithmetic_row5 :
    (BiPoly.mul h4p4 h4p10).getD 5 []=h4p87.getD 5 [] := by
  decide +kernel

theorem h4n87_arithmetic_row6 :
    (BiPoly.mul h4p4 h4p10).getD 6 []=h4p87.getD 6 [] := by
  decide +kernel

theorem h4n87_arithmetic_row7 :
    (BiPoly.mul h4p4 h4p10).getD 7 []=h4p87.getD 7 [] := by
  decide +kernel

theorem h4n87_arithmetic : BiPoly.mul h4p4 h4p10=h4p87 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<8 at hk
    have hf : ∀ j : Fin 8, (BiPoly.mul h4p4 h4p10).getD j.val []=h4p87.getD j.val [] :=
      (fun j => Fin.cases h4n87_arithmetic_row0 (fun j => Fin.cases h4n87_arithmetic_row1 (fun j => Fin.cases h4n87_arithmetic_row2 (fun j => Fin.cases h4n87_arithmetic_row3 (fun j => Fin.cases h4n87_arithmetic_row4 (fun j => Fin.cases h4n87_arithmetic_row5 (fun j => Fin.cases h4n87_arithmetic_row6 (fun j => Fin.cases h4n87_arithmetic_row7 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n87 : h4e87.toBi mapPolyEnv=h4p87 := by
  change BiPoly.mul (h4e4.toBi mapPolyEnv) (h4e10.toBi mapPolyEnv)=h4p87
  rw [h4n4, h4n10]
  exact h4n87_arithmetic

#print axioms h4n87_arithmetic
end StackSorting.RationalLift
