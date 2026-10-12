import BivariateRowEquality
import Horner4Base
import Horner4Node069
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p179 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 9678204000), (Int.ofNat 28886304240), (Int.negSucc 34655551919)], [(Int.ofNat 0), (Int.negSucc 42110940959), (Int.negSucc 114965136431), (Int.ofNat 150773571072), (Int.negSucc 15613928063)], [(Int.ofNat 0), (Int.ofNat 74382374520), (Int.ofNat 198551888604), (Int.negSucc 193465332359), (Int.ofNat 5821953300), (Int.negSucc 1658135231)], [(Int.ofNat 0), (Int.negSucc 68113049039), (Int.negSucc 195994199879), (Int.ofNat 5643041472), (Int.ofNat 93122218728), (Int.negSucc 5986529639)], [(Int.ofNat 0), (Int.ofNat 34064888400), (Int.ofNat 118839254472), (Int.ofNat 190855215180), (Int.negSucc 121174350875), (Int.ofNat 5200666596)], [(Int.ofNat 0), (Int.negSucc 8834646959), (Int.negSucc 42737308487), (Int.negSucc 175504116959), (Int.ofNat 1593325008), (Int.ofNat 19335040272)], [(Int.ofNat 0), (Int.ofNat 933170040), (Int.ofNat 7952073372), (Int.ofNat 66161008188), (Int.ofNat 69037667712), (Int.negSucc 15891275951)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 532875887), (Int.negSucc 9928175399), (Int.negSucc 37663933823), (Int.negSucc 5242350887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 227876328), (Int.ofNat 6253331976), (Int.ofNat 6672747168)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 78502607), (Int.negSucc 1312076879)]]

theorem h4n179_arithmetic_row0 :
    (BiPoly.mul h4p61 h4p69).getD 0 []=h4p179.getD 0 [] := by
  decide +kernel

theorem h4n179_arithmetic_row1 :
    (BiPoly.mul h4p61 h4p69).getD 1 []=h4p179.getD 1 [] := by
  decide +kernel

theorem h4n179_arithmetic_row2 :
    (BiPoly.mul h4p61 h4p69).getD 2 []=h4p179.getD 2 [] := by
  decide +kernel

theorem h4n179_arithmetic_row3 :
    (BiPoly.mul h4p61 h4p69).getD 3 []=h4p179.getD 3 [] := by
  decide +kernel

theorem h4n179_arithmetic_row4 :
    (BiPoly.mul h4p61 h4p69).getD 4 []=h4p179.getD 4 [] := by
  decide +kernel

theorem h4n179_arithmetic_row5 :
    (BiPoly.mul h4p61 h4p69).getD 5 []=h4p179.getD 5 [] := by
  decide +kernel

theorem h4n179_arithmetic_row6 :
    (BiPoly.mul h4p61 h4p69).getD 6 []=h4p179.getD 6 [] := by
  decide +kernel

theorem h4n179_arithmetic_row7 :
    (BiPoly.mul h4p61 h4p69).getD 7 []=h4p179.getD 7 [] := by
  decide +kernel

theorem h4n179_arithmetic_row8 :
    (BiPoly.mul h4p61 h4p69).getD 8 []=h4p179.getD 8 [] := by
  decide +kernel

theorem h4n179_arithmetic_row9 :
    (BiPoly.mul h4p61 h4p69).getD 9 []=h4p179.getD 9 [] := by
  decide +kernel

theorem h4n179_arithmetic : BiPoly.mul h4p61 h4p69=h4p179 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p61 h4p69).getD j.val []=h4p179.getD j.val [] :=
      (fun j => Fin.cases h4n179_arithmetic_row0 (fun j => Fin.cases h4n179_arithmetic_row1 (fun j => Fin.cases h4n179_arithmetic_row2 (fun j => Fin.cases h4n179_arithmetic_row3 (fun j => Fin.cases h4n179_arithmetic_row4 (fun j => Fin.cases h4n179_arithmetic_row5 (fun j => Fin.cases h4n179_arithmetic_row6 (fun j => Fin.cases h4n179_arithmetic_row7 (fun j => Fin.cases h4n179_arithmetic_row8 (fun j => Fin.cases h4n179_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n179 : h4e179.toBi mapPolyEnv=h4p179 := by
  change BiPoly.mul (h4e61.toBi mapPolyEnv) (h4e69.toBi mapPolyEnv)=h4p179
  rw [h4n61, h4n69]
  exact h4n179_arithmetic

#print axioms h4n179_arithmetic
end StackSorting.RationalLift
