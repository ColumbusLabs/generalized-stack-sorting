import BivariateRowEquality
import Horner5Base
import Horner5Node075
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p267 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1567226879), (Int.ofNat 172326960), (Int.negSucc 14623323119), (Int.negSucc 7557773039), (Int.ofNat 27833857200), (Int.ofNat 19028753280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7373390400), (Int.negSucc 2529425159), (Int.ofNat 95005776240), (Int.ofNat 52075034640), (Int.negSucc 95353436879), (Int.negSucc 46680123239), (Int.ofNat 5285764800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14296453919), (Int.ofNat 518159520), (Int.negSucc 243628441199), (Int.negSucc 121943876399), (Int.ofNat 112898744640), (Int.ofNat 43871676480), (Int.ofNat 2723834880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14802823440), (Int.ofNat 17246773800), (Int.ofNat 311617376640), (Int.ofNat 172726819920), (Int.ofNat 7893908640), (Int.negSucc 19758511799), (Int.negSucc 21604920479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8921324159), (Int.negSucc 33633533519), (Int.negSucc 212131009439), (Int.negSucc 200826091439), (Int.negSucc 129653377919), (Int.ofNat 4629292560), (Int.ofNat 14022810720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3222479520), (Int.ofNat 26378340840), (Int.ofNat 79758879120), (Int.ofNat 165560481360), (Int.ofNat 112158864000), (Int.ofNat 17115656400), (Int.ofNat 6765638400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 679764959), (Int.negSucc 9499753439), (Int.negSucc 20014609679), (Int.negSucc 73466306639), (Int.negSucc 48611579759), (Int.negSucc 25728036479), (Int.negSucc 7423047359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 66076560), (Int.ofNat 1383152760), (Int.ofNat 4648492800), (Int.ofNat 13952755440), (Int.ofNat 15568951680), (Int.ofNat 10832434560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 36041759), (Int.negSucc 633141359), (Int.negSucc 620213759), (Int.negSucc 3409387199)]]

theorem h5n267_arithmetic_row0 :
    (BiPoly.mul h5p4 h5p75).getD 0 []=h5p267.getD 0 [] := by
  decide +kernel

theorem h5n267_arithmetic_row1 :
    (BiPoly.mul h5p4 h5p75).getD 1 []=h5p267.getD 1 [] := by
  decide +kernel

theorem h5n267_arithmetic_row2 :
    (BiPoly.mul h5p4 h5p75).getD 2 []=h5p267.getD 2 [] := by
  decide +kernel

theorem h5n267_arithmetic_row3 :
    (BiPoly.mul h5p4 h5p75).getD 3 []=h5p267.getD 3 [] := by
  decide +kernel

theorem h5n267_arithmetic_row4 :
    (BiPoly.mul h5p4 h5p75).getD 4 []=h5p267.getD 4 [] := by
  decide +kernel

theorem h5n267_arithmetic_row5 :
    (BiPoly.mul h5p4 h5p75).getD 5 []=h5p267.getD 5 [] := by
  decide +kernel

theorem h5n267_arithmetic_row6 :
    (BiPoly.mul h5p4 h5p75).getD 6 []=h5p267.getD 6 [] := by
  decide +kernel

theorem h5n267_arithmetic_row7 :
    (BiPoly.mul h5p4 h5p75).getD 7 []=h5p267.getD 7 [] := by
  decide +kernel

theorem h5n267_arithmetic_row8 :
    (BiPoly.mul h5p4 h5p75).getD 8 []=h5p267.getD 8 [] := by
  decide +kernel

theorem h5n267_arithmetic : BiPoly.mul h5p4 h5p75=h5p267 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<9 at hk
    have hf : ∀ j : Fin 9, (BiPoly.mul h5p4 h5p75).getD j.val []=h5p267.getD j.val [] :=
      (fun j => Fin.cases h5n267_arithmetic_row0 (fun j => Fin.cases h5n267_arithmetic_row1 (fun j => Fin.cases h5n267_arithmetic_row2 (fun j => Fin.cases h5n267_arithmetic_row3 (fun j => Fin.cases h5n267_arithmetic_row4 (fun j => Fin.cases h5n267_arithmetic_row5 (fun j => Fin.cases h5n267_arithmetic_row6 (fun j => Fin.cases h5n267_arithmetic_row7 (fun j => Fin.cases h5n267_arithmetic_row8 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n267 : h5e267.toBi mapPolyEnv=h5p267 := by
  change BiPoly.mul (h5e4.toBi mapPolyEnv) (h5e75.toBi mapPolyEnv)=h5p267
  rw [h5n4, h5n75]
  exact h5n267_arithmetic

#print axioms h5n267_arithmetic
end StackSorting.RationalLift
