import BivariateRowEquality
import Horner1Base
import Horner1Node040
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p41 : BiPoly.Poly := [[(Int.ofNat 3226068000), (Int.ofNat 22533040080), (Int.ofNat 26963221680), (Int.negSucc 46207402559)], [(Int.negSucc 14036980319), (Int.negSucc 94469633423), (Int.negSucc 103028991551), (Int.ofNat 195826785408), (Int.negSucc 20818570751)], [(Int.ofNat 24794124840), (Int.ofNat 165360462228), (Int.ofNat 200247407352), (Int.negSucc 256013125379), (Int.ofNat 7209892656), (Int.negSucc 2210846975)], [(Int.negSucc 22704349679), (Int.negSucc 156148798679), (Int.negSucc 259444586015), (Int.ofNat 38564794872), (Int.ofNat 122167448424), (Int.negSucc 7982039519)], [(Int.ofNat 11354962800), (Int.ofNat 85032936024), (Int.ofNat 222070744356), (Int.ofNat 214082169948), (Int.negSucc 159832245635), (Int.ofNat 6934222128)], [(Int.negSucc 2944882319), (Int.negSucc 26025298775), (Int.negSucc 115484450303), (Int.negSucc 233474380943), (Int.ofNat 8569446768), (Int.ofNat 25780053696)], [(Int.ofNat 311056680), (Int.ofNat 3894917844), (Int.ofNat 32656433892), (Int.ofNat 111227233488), (Int.ofNat 86753131632), (Int.negSucc 21188367935)], [(Int.ofNat 0), (Int.negSucc 177625295), (Int.negSucc 4019892983), (Int.negSucc 25792211807), (Int.negSucc 51966028727), (Int.negSucc 6989801183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 75958776), (Int.ofNat 2388279096), (Int.ofNat 10562025024), (Int.ofNat 8896996224)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26167535), (Int.negSucc 542029103), (Int.negSucc 1749435839)]]

theorem h1n41_arithmetic_row0 :
    (BiPoly.mul h1p6 h1p40).getD 0 []=h1p41.getD 0 [] := by
  decide +kernel

theorem h1n41_arithmetic_row1 :
    (BiPoly.mul h1p6 h1p40).getD 1 []=h1p41.getD 1 [] := by
  decide +kernel

theorem h1n41_arithmetic_row2 :
    (BiPoly.mul h1p6 h1p40).getD 2 []=h1p41.getD 2 [] := by
  decide +kernel

theorem h1n41_arithmetic_row3 :
    (BiPoly.mul h1p6 h1p40).getD 3 []=h1p41.getD 3 [] := by
  decide +kernel

theorem h1n41_arithmetic_row4 :
    (BiPoly.mul h1p6 h1p40).getD 4 []=h1p41.getD 4 [] := by
  decide +kernel

theorem h1n41_arithmetic_row5 :
    (BiPoly.mul h1p6 h1p40).getD 5 []=h1p41.getD 5 [] := by
  decide +kernel

theorem h1n41_arithmetic_row6 :
    (BiPoly.mul h1p6 h1p40).getD 6 []=h1p41.getD 6 [] := by
  decide +kernel

theorem h1n41_arithmetic_row7 :
    (BiPoly.mul h1p6 h1p40).getD 7 []=h1p41.getD 7 [] := by
  decide +kernel

theorem h1n41_arithmetic_row8 :
    (BiPoly.mul h1p6 h1p40).getD 8 []=h1p41.getD 8 [] := by
  decide +kernel

theorem h1n41_arithmetic_row9 :
    (BiPoly.mul h1p6 h1p40).getD 9 []=h1p41.getD 9 [] := by
  decide +kernel

theorem h1n41_arithmetic : BiPoly.mul h1p6 h1p40=h1p41 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h1p6 h1p40).getD j.val []=h1p41.getD j.val [] :=
      (fun j => Fin.cases h1n41_arithmetic_row0 (fun j => Fin.cases h1n41_arithmetic_row1 (fun j => Fin.cases h1n41_arithmetic_row2 (fun j => Fin.cases h1n41_arithmetic_row3 (fun j => Fin.cases h1n41_arithmetic_row4 (fun j => Fin.cases h1n41_arithmetic_row5 (fun j => Fin.cases h1n41_arithmetic_row6 (fun j => Fin.cases h1n41_arithmetic_row7 (fun j => Fin.cases h1n41_arithmetic_row8 (fun j => Fin.cases h1n41_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n41 : h1e41.toBi mapPolyEnv=h1p41 := by
  change BiPoly.mul (h1e6.toBi mapPolyEnv) (h1e40.toBi mapPolyEnv)=h1p41
  rw [h1n6, h1n40]
  exact h1n41_arithmetic

#print axioms h1n41_arithmetic
end StackSorting.RationalLift
