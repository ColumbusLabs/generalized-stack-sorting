import BivariateRowEquality
import Horner4Base
import Horner4Node071
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p119 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 28335680279), (Int.negSucc 73020940559), (Int.ofNat 147009227400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 138376842840), (Int.ofNat 402215950800), (Int.negSucc 644925031559), (Int.ofNat 40257724320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 319203057719), (Int.negSucc 737580255719), (Int.ofNat 984195369600), (Int.negSucc 7043463719), (Int.negSucc 204309599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 445162074420), (Int.ofNat 502651264020), (Int.negSucc 242162088059), (Int.negSucc 242144014259), (Int.ofNat 7413436080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 391079485979), (Int.negSucc 24146035319), (Int.negSucc 740372715779), (Int.ofNat 358833126360), (Int.ofNat 12417139320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 210288126300), (Int.negSucc 59234890559), (Int.ofNat 644370740340), (Int.negSucc 35008042379), (Int.negSucc 22642929899)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 64496442419), (Int.negSucc 51494974619), (Int.negSucc 136918134119), (Int.negSucc 171004970099), (Int.negSucc 5459416199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9749026920), (Int.ofNat 56173401780), (Int.negSucc 20042962379), (Int.ofNat 80292765600), (Int.ofNat 14983538760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 461404079), (Int.negSucc 17924156459), (Int.ofNat 9901623960), (Int.negSucc 8679121919), (Int.negSucc 4283383679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2207697120), (Int.negSucc 1383660359)]]

theorem h4n119_arithmetic_row0 :
    (BiPoly.mul h4p118 h4p71).getD 0 []=h4p119.getD 0 [] := by
  decide +kernel

theorem h4n119_arithmetic_row1 :
    (BiPoly.mul h4p118 h4p71).getD 1 []=h4p119.getD 1 [] := by
  decide +kernel

theorem h4n119_arithmetic_row2 :
    (BiPoly.mul h4p118 h4p71).getD 2 []=h4p119.getD 2 [] := by
  decide +kernel

theorem h4n119_arithmetic_row3 :
    (BiPoly.mul h4p118 h4p71).getD 3 []=h4p119.getD 3 [] := by
  decide +kernel

theorem h4n119_arithmetic_row4 :
    (BiPoly.mul h4p118 h4p71).getD 4 []=h4p119.getD 4 [] := by
  decide +kernel

theorem h4n119_arithmetic_row5 :
    (BiPoly.mul h4p118 h4p71).getD 5 []=h4p119.getD 5 [] := by
  decide +kernel

theorem h4n119_arithmetic_row6 :
    (BiPoly.mul h4p118 h4p71).getD 6 []=h4p119.getD 6 [] := by
  decide +kernel

theorem h4n119_arithmetic_row7 :
    (BiPoly.mul h4p118 h4p71).getD 7 []=h4p119.getD 7 [] := by
  decide +kernel

theorem h4n119_arithmetic_row8 :
    (BiPoly.mul h4p118 h4p71).getD 8 []=h4p119.getD 8 [] := by
  decide +kernel

theorem h4n119_arithmetic_row9 :
    (BiPoly.mul h4p118 h4p71).getD 9 []=h4p119.getD 9 [] := by
  decide +kernel

theorem h4n119_arithmetic : BiPoly.mul h4p118 h4p71=h4p119 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p118 h4p71).getD j.val []=h4p119.getD j.val [] :=
      (fun j => Fin.cases h4n119_arithmetic_row0 (fun j => Fin.cases h4n119_arithmetic_row1 (fun j => Fin.cases h4n119_arithmetic_row2 (fun j => Fin.cases h4n119_arithmetic_row3 (fun j => Fin.cases h4n119_arithmetic_row4 (fun j => Fin.cases h4n119_arithmetic_row5 (fun j => Fin.cases h4n119_arithmetic_row6 (fun j => Fin.cases h4n119_arithmetic_row7 (fun j => Fin.cases h4n119_arithmetic_row8 (fun j => Fin.cases h4n119_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n119 : h4e119.toBi mapPolyEnv=h4p119 := by
  change BiPoly.mul (h4e118.toBi mapPolyEnv) (h4e71.toBi mapPolyEnv)=h4p119
  rw [h4n118, h4n71]
  exact h4n119_arithmetic

#print axioms h4n119_arithmetic
end StackSorting.RationalLift
