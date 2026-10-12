import BivariateRowEquality
import Horner5Base
import Horner5Node075
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p76 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 85007040839), (Int.negSucc 304069862519), (Int.ofNat 221964860520), (Int.ofNat 441027682200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 500137569360), (Int.ofNat 1840841202600), (Int.negSucc 1169154924479), (Int.negSucc 1814001921719), (Int.ofNat 120773172960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1372739701679), (Int.negSucc 4376997792719), (Int.ofNat 2674620436320), (Int.ofNat 2810682544680), (Int.negSucc 21743319959), (Int.negSucc 612928799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2293095396420), (Int.ofNat 5056180782480), (Int.negSucc 2171118580919), (Int.negSucc 1431787915799), (Int.negSucc 703578805739), (Int.ofNat 22240308240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2508724681199), (Int.negSucc 2753630355959), (Int.negSucc 1567069989119), (Int.negSucc 418186725479), (Int.ofNat 1091510488800), (Int.ofNat 37251417960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1804102836840), (Int.ofNat 525597813180), (Int.ofNat 3976525696680), (Int.ofNat 751588714800), (Int.negSucc 210204334799), (Int.negSucc 67928789699)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 824353706159), (Int.negSucc 170269579439), (Int.negSucc 2498351547239), (Int.negSucc 818745185519), (Int.negSucc 461464369199), (Int.negSucc 16378248599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 222736408020), (Int.ofNat 352252209960), (Int.ofNat 519145720560), (Int.ofNat 693764319960), (Int.ofNat 302207161680), (Int.ofNat 44950616280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 30631292999), (Int.negSucc 223676886959), (Int.ofNat 36061289640), (Int.negSucc 237210790679), (Int.negSucc 83838133079), (Int.negSucc 12850151039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1384212240), (Int.ofNat 60395560740), (Int.negSucc 27232761599), (Int.ofNat 21886384680), (Int.ofNat 12850151040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6623091359), (Int.ofNat 4150981080)]]

theorem h5n76_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p75).getD 0 []=h5p76.getD 0 [] := by
  decide +kernel

theorem h5n76_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p75).getD 1 []=h5p76.getD 1 [] := by
  decide +kernel

theorem h5n76_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p75).getD 2 []=h5p76.getD 2 [] := by
  decide +kernel

theorem h5n76_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p75).getD 3 []=h5p76.getD 3 [] := by
  decide +kernel

theorem h5n76_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p75).getD 4 []=h5p76.getD 4 [] := by
  decide +kernel

theorem h5n76_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p75).getD 5 []=h5p76.getD 5 [] := by
  decide +kernel

theorem h5n76_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p75).getD 6 []=h5p76.getD 6 [] := by
  decide +kernel

theorem h5n76_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p75).getD 7 []=h5p76.getD 7 [] := by
  decide +kernel

theorem h5n76_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p75).getD 8 []=h5p76.getD 8 [] := by
  decide +kernel

theorem h5n76_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p75).getD 9 []=h5p76.getD 9 [] := by
  decide +kernel

theorem h5n76_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p75).getD 10 []=h5p76.getD 10 [] := by
  decide +kernel

theorem h5n76_arithmetic : BiPoly.mul h5p22 h5p75=h5p76 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p22 h5p75).getD j.val []=h5p76.getD j.val [] :=
      (fun j => Fin.cases h5n76_arithmetic_row0 (fun j => Fin.cases h5n76_arithmetic_row1 (fun j => Fin.cases h5n76_arithmetic_row2 (fun j => Fin.cases h5n76_arithmetic_row3 (fun j => Fin.cases h5n76_arithmetic_row4 (fun j => Fin.cases h5n76_arithmetic_row5 (fun j => Fin.cases h5n76_arithmetic_row6 (fun j => Fin.cases h5n76_arithmetic_row7 (fun j => Fin.cases h5n76_arithmetic_row8 (fun j => Fin.cases h5n76_arithmetic_row9 (fun j => Fin.cases h5n76_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n76 : h5e76.toBi mapPolyEnv=h5p76 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e75.toBi mapPolyEnv)=h5p76
  rw [h5n22, h5n75]
  exact h5n76_arithmetic

#print axioms h5n76_arithmetic
end StackSorting.RationalLift
