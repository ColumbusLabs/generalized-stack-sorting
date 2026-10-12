import BivariateRowEquality
import Horner5Base
import Horner5Node379
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p380 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 3226067999), (Int.negSucc 6402700079), (Int.ofNat 21180618720), (Int.negSucc 11551850639)], [(Int.ofNat 0), (Int.ofNat 17263048320), (Int.ofNat 27461363904), (Int.negSucc 119388955967), (Int.ofNat 78566200992), (Int.negSucc 5204642687)], [(Int.ofNat 0), (Int.negSucc 38831105159), (Int.negSucc 51637589531), (Int.ofNat 257573688300), (Int.negSucc 172149451955), (Int.ofNat 12902648220), (Int.negSucc 552711743)], [(Int.ofNat 0), (Int.ofNat 47498474520), (Int.ofNat 59222763468), (Int.negSucc 264068783639), (Int.ofNat 101757813588), (Int.ofNat 28602235512), (Int.negSucc 890086391)], [(Int.ofNat 0), (Int.negSucc 34059312479), (Int.negSucc 48180822623), (Int.ofNat 108538493508), (Int.ofNat 131288567280), (Int.negSucc 106201994855), (Int.ofNat 5724575292)], [(Int.ofNat 0), (Int.ofNat 14299845120), (Int.ofNat 28204046400), (Int.ofNat 28647838236), (Int.negSucc 226660741067), (Int.ofNat 76602551028), (Int.ofNat 2977902360)], [(Int.ofNat 0), (Int.negSucc 3255938999), (Int.negSucc 10695639299), (Int.negSucc 49412811599), (Int.ofNat 116574966468), (Int.ofNat 33692444640), (Int.negSucc 18187118831)], [(Int.ofNat 0), (Int.ofNat 311056680), (Int.ofNat 2206203060), (Int.ofNat 19884053652), (Int.negSucc 11849530079), (Int.negSucc 62129398103), (Int.ofNat 8846733672)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 177625295), (Int.negSucc 3030099983), (Int.negSucc 7944346223), (Int.ofNat 23222033856), (Int.ofNat 5719149648)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 75958776), (Int.ofNat 1958693976), (Int.negSucc 1533447503), (Int.negSucc 4885857071)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26167535), (Int.negSucc 385023887), (Int.ofNat 874717920)]]

theorem h5n380_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p379).getD 0 []=h5p380.getD 0 [] := by
  decide +kernel

theorem h5n380_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p379).getD 1 []=h5p380.getD 1 [] := by
  decide +kernel

theorem h5n380_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p379).getD 2 []=h5p380.getD 2 [] := by
  decide +kernel

theorem h5n380_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p379).getD 3 []=h5p380.getD 3 [] := by
  decide +kernel

theorem h5n380_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p379).getD 4 []=h5p380.getD 4 [] := by
  decide +kernel

theorem h5n380_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p379).getD 5 []=h5p380.getD 5 [] := by
  decide +kernel

theorem h5n380_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p379).getD 6 []=h5p380.getD 6 [] := by
  decide +kernel

theorem h5n380_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p379).getD 7 []=h5p380.getD 7 [] := by
  decide +kernel

theorem h5n380_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p379).getD 8 []=h5p380.getD 8 [] := by
  decide +kernel

theorem h5n380_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p379).getD 9 []=h5p380.getD 9 [] := by
  decide +kernel

theorem h5n380_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p379).getD 10 []=h5p380.getD 10 [] := by
  decide +kernel

theorem h5n380_arithmetic : BiPoly.mul h5p6 h5p379=h5p380 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p379).getD j.val []=h5p380.getD j.val [] :=
      (fun j => Fin.cases h5n380_arithmetic_row0 (fun j => Fin.cases h5n380_arithmetic_row1 (fun j => Fin.cases h5n380_arithmetic_row2 (fun j => Fin.cases h5n380_arithmetic_row3 (fun j => Fin.cases h5n380_arithmetic_row4 (fun j => Fin.cases h5n380_arithmetic_row5 (fun j => Fin.cases h5n380_arithmetic_row6 (fun j => Fin.cases h5n380_arithmetic_row7 (fun j => Fin.cases h5n380_arithmetic_row8 (fun j => Fin.cases h5n380_arithmetic_row9 (fun j => Fin.cases h5n380_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n380 : h5e380.toBi mapPolyEnv=h5p380 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e379.toBi mapPolyEnv)=h5p380
  rw [h5n6, h5n379]
  exact h5n380_arithmetic

#print axioms h5n380_arithmetic
end StackSorting.RationalLift
