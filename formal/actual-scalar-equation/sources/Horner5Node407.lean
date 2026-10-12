import BivariateRowEquality
import Horner5Base
import Horner5Node406
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p407 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6452135999), (Int.negSucc 25709672159), (Int.ofNat 3846165120), (Int.ofNat 23103701280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34526096640), (Int.ofNat 123974921088), (Int.negSucc 46975991039), (Int.negSucc 90106428671), (Int.ofNat 10409285376)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 77662210319), (Int.negSucc 258599599703), (Int.ofNat 97124676552), (Int.ofNat 114686300664), (Int.negSucc 2775878711), (Int.ofNat 1105423488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 94996949040), (Int.ofNat 308439425016), (Int.negSucc 2076115967), (Int.negSucc 61962204599), (Int.negSucc 59195882879), (Int.ofNat 3991019760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 68118624959), (Int.negSucc 232598895167), (Int.negSucc 202700952119), (Int.ofNat 15627569616), (Int.ofNat 73324769760), (Int.negSucc 3467111063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 28599690240), (Int.ofNat 113607473280), (Int.ofNat 272731093752), (Int.ofNat 35157627384), (Int.negSucc 10485132455), (Int.negSucc 12890026847)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6511877999), (Int.negSucc 34415034599), (Int.negSucc 166411465679), (Int.negSucc 89070233927), (Int.negSucc 22540900991), (Int.ofNat 10594183968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 622113360), (Int.ofNat 5656632840), (Int.ofNat 51081372984), (Int.ofNat 77753184624), (Int.ofNat 18010005840), (Int.ofNat 3494900592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 355250591), (Int.negSucc 6770701151), (Int.negSucc 29430094751), (Int.negSucc 12112286687), (Int.negSucc 4448498111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 151917552), (Int.ofNat 4221223056), (Int.ofNat 5375551104), (Int.ofNat 874717920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 52335071), (Int.negSucc 874717919)]]

theorem h5n407_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p406).getD 0 []=h5p407.getD 0 [] := by
  decide +kernel

theorem h5n407_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p406).getD 1 []=h5p407.getD 1 [] := by
  decide +kernel

theorem h5n407_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p406).getD 2 []=h5p407.getD 2 [] := by
  decide +kernel

theorem h5n407_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p406).getD 3 []=h5p407.getD 3 [] := by
  decide +kernel

theorem h5n407_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p406).getD 4 []=h5p407.getD 4 [] := by
  decide +kernel

theorem h5n407_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p406).getD 5 []=h5p407.getD 5 [] := by
  decide +kernel

theorem h5n407_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p406).getD 6 []=h5p407.getD 6 [] := by
  decide +kernel

theorem h5n407_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p406).getD 7 []=h5p407.getD 7 [] := by
  decide +kernel

theorem h5n407_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p406).getD 8 []=h5p407.getD 8 [] := by
  decide +kernel

theorem h5n407_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p406).getD 9 []=h5p407.getD 9 [] := by
  decide +kernel

theorem h5n407_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p406).getD 10 []=h5p407.getD 10 [] := by
  decide +kernel

theorem h5n407_arithmetic : BiPoly.mul h5p6 h5p406=h5p407 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p406).getD j.val []=h5p407.getD j.val [] :=
      (fun j => Fin.cases h5n407_arithmetic_row0 (fun j => Fin.cases h5n407_arithmetic_row1 (fun j => Fin.cases h5n407_arithmetic_row2 (fun j => Fin.cases h5n407_arithmetic_row3 (fun j => Fin.cases h5n407_arithmetic_row4 (fun j => Fin.cases h5n407_arithmetic_row5 (fun j => Fin.cases h5n407_arithmetic_row6 (fun j => Fin.cases h5n407_arithmetic_row7 (fun j => Fin.cases h5n407_arithmetic_row8 (fun j => Fin.cases h5n407_arithmetic_row9 (fun j => Fin.cases h5n407_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n407 : h5e407.toBi mapPolyEnv=h5p407 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e406.toBi mapPolyEnv)=h5p407
  rw [h5n6, h5n406]
  exact h5n407_arithmetic

#print axioms h5n407_arithmetic
end StackSorting.RationalLift
