import BivariateRowEquality
import Horner5Base
import Horner5Node257
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p258 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 9678203999), (Int.negSucc 38564508239), (Int.negSucc 13587160319), (Int.negSucc 23117056559), (Int.ofNat 69311103840)], [(Int.ofNat 0), (Int.ofNat 51789144960), (Int.ofNat 185962381632), (Int.ofNat 13757895360), (Int.ofNat 94770629856), (Int.negSucc 285933214079), (Int.ofNat 31227856128)], [(Int.ofNat 0), (Int.negSucc 116493315479), (Int.negSucc 387899399555), (Int.negSucc 3077734211), (Int.negSucc 225074326211), (Int.ofNat 382766846652), (Int.negSucc 9985771367), (Int.ofNat 3316270464)], [(Int.ofNat 0), (Int.ofNat 142495423560), (Int.ofNat 462659137524), (Int.ofNat 133111924128), (Int.ofNat 299045092860), (Int.negSucc 100079907263), (Int.negSucc 180257907815), (Int.ofNat 11973059280)], [(Int.ofNat 0), (Int.negSucc 102177937439), (Int.negSucc 348898342751), (Int.negSucc 372181204979), (Int.negSucc 214237154519), (Int.negSucc 271723275719), (Int.ofNat 237148035156), (Int.negSucc 10401333191)], [(Int.ofNat 0), (Int.ofNat 42899535360), (Int.ofNat 170411209920), (Int.ofNat 426765934548), (Int.ofNat 138211058052), (Int.ofNat 335280535236), (Int.negSucc 22521690287), (Int.negSucc 38670080543)], [(Int.ofNat 0), (Int.negSucc 9767816999), (Int.negSucc 51622551899), (Int.negSucc 251483538599), (Int.negSucc 149509497635), (Int.negSucc 166133367863), (Int.negSucc 122184059471), (Int.ofNat 31782551904)], [(Int.ofNat 0), (Int.ofNat 933170040), (Int.ofNat 8484949260), (Int.ofNat 76622059476), (Int.ofNat 117695528712), (Int.ofNat 46871359560), (Int.ofNat 80570218536), (Int.ofNat 10484701776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 532875887), (Int.negSucc 10156051727), (Int.negSucc 44145142127), (Int.negSucc 18624182687), (Int.negSucc 19179411119), (Int.negSucc 13345494335)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 227876328), (Int.ofNat 6331834584), (Int.ofNat 8063326656), (Int.ofNat 1469082096), (Int.ofNat 2624153760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 78502607), (Int.negSucc 1312076879)]]

theorem h5n258_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p257).getD 0 []=h5p258.getD 0 [] := by
  decide +kernel

theorem h5n258_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p257).getD 1 []=h5p258.getD 1 [] := by
  decide +kernel

theorem h5n258_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p257).getD 2 []=h5p258.getD 2 [] := by
  decide +kernel

theorem h5n258_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p257).getD 3 []=h5p258.getD 3 [] := by
  decide +kernel

theorem h5n258_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p257).getD 4 []=h5p258.getD 4 [] := by
  decide +kernel

theorem h5n258_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p257).getD 5 []=h5p258.getD 5 [] := by
  decide +kernel

theorem h5n258_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p257).getD 6 []=h5p258.getD 6 [] := by
  decide +kernel

theorem h5n258_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p257).getD 7 []=h5p258.getD 7 [] := by
  decide +kernel

theorem h5n258_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p257).getD 8 []=h5p258.getD 8 [] := by
  decide +kernel

theorem h5n258_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p257).getD 9 []=h5p258.getD 9 [] := by
  decide +kernel

theorem h5n258_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p257).getD 10 []=h5p258.getD 10 [] := by
  decide +kernel

theorem h5n258_arithmetic : BiPoly.mul h5p6 h5p257=h5p258 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p257).getD j.val []=h5p258.getD j.val [] :=
      (fun j => Fin.cases h5n258_arithmetic_row0 (fun j => Fin.cases h5n258_arithmetic_row1 (fun j => Fin.cases h5n258_arithmetic_row2 (fun j => Fin.cases h5n258_arithmetic_row3 (fun j => Fin.cases h5n258_arithmetic_row4 (fun j => Fin.cases h5n258_arithmetic_row5 (fun j => Fin.cases h5n258_arithmetic_row6 (fun j => Fin.cases h5n258_arithmetic_row7 (fun j => Fin.cases h5n258_arithmetic_row8 (fun j => Fin.cases h5n258_arithmetic_row9 (fun j => Fin.cases h5n258_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n258 : h5e258.toBi mapPolyEnv=h5p258 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e257.toBi mapPolyEnv)=h5p258
  rw [h5n6, h5n257]
  exact h5n258_arithmetic

#print axioms h5n258_arithmetic
end StackSorting.RationalLift
