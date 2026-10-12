import BivariateRowEquality
import Horner4Base
import Horner4Node080
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p81 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 11334272112), (Int.ofNat 40542648336), (Int.negSucc 29595314735), (Int.negSucc 58803690959)], [(Int.ofNat 0), (Int.negSucc 55350737135), (Int.negSucc 216237117455), (Int.ofNat 97083632304), (Int.ofNat 241866922896), (Int.negSucc 16103089727)], [(Int.ofNat 0), (Int.ofNat 127681223088), (Int.ofNat 422713325376), (Int.negSucc 98646045551), (Int.negSucc 390860762351), (Int.ofNat 2899109328), (Int.ofNat 81723840)], [(Int.ofNat 0), (Int.negSucc 178064829767), (Int.negSucc 379125335375), (Int.negSucc 104195670383), (Int.ofNat 193722440928), (Int.ofNat 93892231272), (Int.negSucc 2965374431)], [(Int.ofNat 0), (Int.ofNat 156431794392), (Int.ofNat 166090208520), (Int.ofNat 305807500440), (Int.ofNat 152615835768), (Int.negSucc 148500106271), (Int.negSucc 4966855727)], [(Int.ofNat 0), (Int.negSucc 84115250519), (Int.negSucc 60421294295), (Int.negSucc 234054339911), (Int.negSucc 243745079183), (Int.ofNat 23060388912), (Int.ofNat 9057171960)], [(Int.ofNat 0), (Int.ofNat 25798576968), (Int.ofNat 46396566816), (Int.ofNat 75365243496), (Int.ofNat 123169241688), (Int.ofNat 70585754520), (Int.ofNat 2183766480)], [(Int.ofNat 0), (Int.negSucc 3899610767), (Int.negSucc 26368971479), (Int.negSucc 14452175759), (Int.negSucc 24099921287), (Int.negSucc 38110521743), (Int.negSucc 5993415503)], [(Int.ofNat 0), (Int.ofNat 184561632), (Int.ofNat 7354224216), (Int.ofNat 3209013000), (Int.negSucc 489000815), (Int.ofNat 5185002240), (Int.ofNat 1713353472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 883078847), (Int.negSucc 329614703), (Int.ofNat 553464144)]]

theorem h4n81_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p80).getD 0 []=h4p81.getD 0 [] := by
  decide +kernel

theorem h4n81_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p80).getD 1 []=h4p81.getD 1 [] := by
  decide +kernel

theorem h4n81_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p80).getD 2 []=h4p81.getD 2 [] := by
  decide +kernel

theorem h4n81_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p80).getD 3 []=h4p81.getD 3 [] := by
  decide +kernel

theorem h4n81_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p80).getD 4 []=h4p81.getD 4 [] := by
  decide +kernel

theorem h4n81_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p80).getD 5 []=h4p81.getD 5 [] := by
  decide +kernel

theorem h4n81_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p80).getD 6 []=h4p81.getD 6 [] := by
  decide +kernel

theorem h4n81_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p80).getD 7 []=h4p81.getD 7 [] := by
  decide +kernel

theorem h4n81_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p80).getD 8 []=h4p81.getD 8 [] := by
  decide +kernel

theorem h4n81_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p80).getD 9 []=h4p81.getD 9 [] := by
  decide +kernel

theorem h4n81_arithmetic : BiPoly.mul h4p7 h4p80=h4p81 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p80).getD j.val []=h4p81.getD j.val [] :=
      (fun j => Fin.cases h4n81_arithmetic_row0 (fun j => Fin.cases h4n81_arithmetic_row1 (fun j => Fin.cases h4n81_arithmetic_row2 (fun j => Fin.cases h4n81_arithmetic_row3 (fun j => Fin.cases h4n81_arithmetic_row4 (fun j => Fin.cases h4n81_arithmetic_row5 (fun j => Fin.cases h4n81_arithmetic_row6 (fun j => Fin.cases h4n81_arithmetic_row7 (fun j => Fin.cases h4n81_arithmetic_row8 (fun j => Fin.cases h4n81_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n81 : h4e81.toBi mapPolyEnv=h4p81 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e80.toBi mapPolyEnv)=h4p81
  rw [h4n7, h4n80]
  exact h4n81_arithmetic

#print axioms h4n81_arithmetic
end StackSorting.RationalLift
