import BivariateRowEquality
import Horner4Base
import Horner4Node149
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p150 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 68005632672), (Int.ofNat 311261522688), (Int.negSucc 2321631071), (Int.negSucc 705644291519)], [(Int.ofNat 0), (Int.negSucc 332104422815), (Int.negSucc 1629527127551), (Int.negSucc 382816488095), (Int.ofNat 2999021613120), (Int.negSucc 193237076735)], [(Int.ofNat 0), (Int.ofNat 766087338528), (Int.ofNat 3302367290784), (Int.ofNat 1178316340416), (Int.negSucc 4707233461151), (Int.ofNat 34298968896), (Int.ofNat 980686080)], [(Int.ofNat 0), (Int.negSucc 1068388978607), (Int.negSucc 3343140990863), (Int.negSucc 1831537055951), (Int.ofNat 1743523656912), (Int.ofNat 1144499021856), (Int.negSucc 35584493183)], [(Int.ofNat 0), (Int.ofNat 938590766352), (Int.ofNat 1935132017472), (Int.ofNat 1892795487408), (Int.ofNat 2692589532480), (Int.negSucc 1752200140895), (Int.negSucc 59602268735)], [(Int.ofNat 0), (Int.negSucc 504691503119), (Int.negSucc 867219268895), (Int.negSucc 1262162302127), (Int.negSucc 3008960251919), (Int.ofNat 222381635184), (Int.ofNat 108686063520)], [(Int.ofNat 0), (Int.ofNat 154791461808), (Int.ofNat 433170862704), (Int.ofNat 575779400064), (Int.ofNat 1067618972016), (Int.ofNat 833926455360), (Int.ofNat 26205197760)], [(Int.ofNat 0), (Int.negSucc 23397664607), (Int.negSucc 181611493487), (Int.negSucc 221529218831), (Int.negSucc 96496418015), (Int.negSucc 421365767903), (Int.negSucc 71920986047)], [(Int.ofNat 0), (Int.ofNat 1107369792), (Int.ofNat 45232715088), (Int.ofNat 62272053504), (Int.negSucc 26697902399), (Int.ofNat 51939906048), (Int.ofNat 20560241664)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5298473087), (Int.negSucc 7276161311), (Int.ofNat 6641569728)]]

theorem h4n150_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p149).getD 0 []=h4p150.getD 0 [] := by
  decide +kernel

theorem h4n150_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p149).getD 1 []=h4p150.getD 1 [] := by
  decide +kernel

theorem h4n150_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p149).getD 2 []=h4p150.getD 2 [] := by
  decide +kernel

theorem h4n150_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p149).getD 3 []=h4p150.getD 3 [] := by
  decide +kernel

theorem h4n150_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p149).getD 4 []=h4p150.getD 4 [] := by
  decide +kernel

theorem h4n150_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p149).getD 5 []=h4p150.getD 5 [] := by
  decide +kernel

theorem h4n150_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p149).getD 6 []=h4p150.getD 6 [] := by
  decide +kernel

theorem h4n150_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p149).getD 7 []=h4p150.getD 7 [] := by
  decide +kernel

theorem h4n150_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p149).getD 8 []=h4p150.getD 8 [] := by
  decide +kernel

theorem h4n150_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p149).getD 9 []=h4p150.getD 9 [] := by
  decide +kernel

theorem h4n150_arithmetic : BiPoly.mul h4p7 h4p149=h4p150 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p149).getD j.val []=h4p150.getD j.val [] :=
      (fun j => Fin.cases h4n150_arithmetic_row0 (fun j => Fin.cases h4n150_arithmetic_row1 (fun j => Fin.cases h4n150_arithmetic_row2 (fun j => Fin.cases h4n150_arithmetic_row3 (fun j => Fin.cases h4n150_arithmetic_row4 (fun j => Fin.cases h4n150_arithmetic_row5 (fun j => Fin.cases h4n150_arithmetic_row6 (fun j => Fin.cases h4n150_arithmetic_row7 (fun j => Fin.cases h4n150_arithmetic_row8 (fun j => Fin.cases h4n150_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n150 : h4e150.toBi mapPolyEnv=h4p150 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e149.toBi mapPolyEnv)=h4p150
  rw [h4n7, h4n149]
  exact h4n150_arithmetic

#print axioms h4n150_arithmetic
end StackSorting.RationalLift
