import BivariateRowEquality
import Horner4Base
import Horner4Node071
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p171 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34002816336), (Int.ofNat 87625128672), (Int.negSucc 176411072879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 166052211407), (Int.negSucc 482659140959), (Int.ofNat 773910037872), (Int.negSucc 48309269183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 383043669264), (Int.ofNat 885096306864), (Int.negSucc 1181034443519), (Int.ofNat 8452156464), (Int.ofNat 245171520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 534194489303), (Int.negSucc 603181516823), (Int.ofNat 290594505672), (Int.ofNat 290572817112), (Int.negSucc 8896123295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 469295383176), (Int.ofNat 28975242384), (Int.ofNat 888447258936), (Int.negSucc 430599751631), (Int.negSucc 14900567183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 252345751559), (Int.ofNat 71081868672), (Int.negSucc 773244888407), (Int.ofNat 42009650856), (Int.ofNat 27171515880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 77395730904), (Int.ofNat 61793969544), (Int.ofNat 164301760944), (Int.ofNat 205205964120), (Int.ofNat 6551299440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11698832303), (Int.negSucc 67408082135), (Int.ofNat 24051554856), (Int.negSucc 96351318719), (Int.negSucc 17980246511)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 553684896), (Int.ofNat 21508987752), (Int.negSucc 11881948751), (Int.ofNat 10414946304), (Int.ofNat 5140060416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2649236543), (Int.ofNat 1660392432)]]

theorem h4n171_arithmetic_row0 :
    (BiPoly.mul h4p6 h4p71).getD 0 []=h4p171.getD 0 [] := by
  decide +kernel

theorem h4n171_arithmetic_row1 :
    (BiPoly.mul h4p6 h4p71).getD 1 []=h4p171.getD 1 [] := by
  decide +kernel

theorem h4n171_arithmetic_row2 :
    (BiPoly.mul h4p6 h4p71).getD 2 []=h4p171.getD 2 [] := by
  decide +kernel

theorem h4n171_arithmetic_row3 :
    (BiPoly.mul h4p6 h4p71).getD 3 []=h4p171.getD 3 [] := by
  decide +kernel

theorem h4n171_arithmetic_row4 :
    (BiPoly.mul h4p6 h4p71).getD 4 []=h4p171.getD 4 [] := by
  decide +kernel

theorem h4n171_arithmetic_row5 :
    (BiPoly.mul h4p6 h4p71).getD 5 []=h4p171.getD 5 [] := by
  decide +kernel

theorem h4n171_arithmetic_row6 :
    (BiPoly.mul h4p6 h4p71).getD 6 []=h4p171.getD 6 [] := by
  decide +kernel

theorem h4n171_arithmetic_row7 :
    (BiPoly.mul h4p6 h4p71).getD 7 []=h4p171.getD 7 [] := by
  decide +kernel

theorem h4n171_arithmetic_row8 :
    (BiPoly.mul h4p6 h4p71).getD 8 []=h4p171.getD 8 [] := by
  decide +kernel

theorem h4n171_arithmetic_row9 :
    (BiPoly.mul h4p6 h4p71).getD 9 []=h4p171.getD 9 [] := by
  decide +kernel

theorem h4n171_arithmetic : BiPoly.mul h4p6 h4p71=h4p171 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p6 h4p71).getD j.val []=h4p171.getD j.val [] :=
      (fun j => Fin.cases h4n171_arithmetic_row0 (fun j => Fin.cases h4n171_arithmetic_row1 (fun j => Fin.cases h4n171_arithmetic_row2 (fun j => Fin.cases h4n171_arithmetic_row3 (fun j => Fin.cases h4n171_arithmetic_row4 (fun j => Fin.cases h4n171_arithmetic_row5 (fun j => Fin.cases h4n171_arithmetic_row6 (fun j => Fin.cases h4n171_arithmetic_row7 (fun j => Fin.cases h4n171_arithmetic_row8 (fun j => Fin.cases h4n171_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n171 : h4e171.toBi mapPolyEnv=h4p171 := by
  change BiPoly.mul (h4e6.toBi mapPolyEnv) (h4e71.toBi mapPolyEnv)=h4p171
  rw [h4n6, h4n71]
  exact h4n171_arithmetic

#print axioms h4n171_arithmetic
end StackSorting.RationalLift
