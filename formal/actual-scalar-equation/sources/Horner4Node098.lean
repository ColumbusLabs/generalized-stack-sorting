import BivariateRowEquality
import Horner4Base
import Horner4Node069
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p98 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 9678203999), (Int.negSucc 28886304239), (Int.ofNat 34655551920)], [(Int.ofNat 0), (Int.ofNat 42110940960), (Int.ofNat 114965136432), (Int.negSucc 150773571071), (Int.ofNat 15613928064)], [(Int.ofNat 0), (Int.negSucc 74382374519), (Int.negSucc 198551888603), (Int.ofNat 193465332360), (Int.negSucc 5821953299), (Int.ofNat 1658135232)], [(Int.ofNat 0), (Int.ofNat 68113049040), (Int.ofNat 195994199880), (Int.negSucc 5643041471), (Int.negSucc 93122218727), (Int.ofNat 5986529640)], [(Int.ofNat 0), (Int.negSucc 34064888399), (Int.negSucc 118839254471), (Int.negSucc 190855215179), (Int.ofNat 121174350876), (Int.negSucc 5200666595)], [(Int.ofNat 0), (Int.ofNat 8834646960), (Int.ofNat 42737308488), (Int.ofNat 175504116960), (Int.negSucc 1593325007), (Int.negSucc 19335040271)], [(Int.ofNat 0), (Int.negSucc 933170039), (Int.negSucc 7952073371), (Int.negSucc 66161008187), (Int.negSucc 69037667711), (Int.ofNat 15891275952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 532875888), (Int.ofNat 9928175400), (Int.ofNat 37663933824), (Int.ofNat 5242350888)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 227876327), (Int.negSucc 6253331975), (Int.negSucc 6672747167)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 78502608), (Int.ofNat 1312076880)]]

theorem h4n98_arithmetic_row0 :
    (BiPoly.mul h4p97 h4p69).getD 0 []=h4p98.getD 0 [] := by
  decide +kernel

theorem h4n98_arithmetic_row1 :
    (BiPoly.mul h4p97 h4p69).getD 1 []=h4p98.getD 1 [] := by
  decide +kernel

theorem h4n98_arithmetic_row2 :
    (BiPoly.mul h4p97 h4p69).getD 2 []=h4p98.getD 2 [] := by
  decide +kernel

theorem h4n98_arithmetic_row3 :
    (BiPoly.mul h4p97 h4p69).getD 3 []=h4p98.getD 3 [] := by
  decide +kernel

theorem h4n98_arithmetic_row4 :
    (BiPoly.mul h4p97 h4p69).getD 4 []=h4p98.getD 4 [] := by
  decide +kernel

theorem h4n98_arithmetic_row5 :
    (BiPoly.mul h4p97 h4p69).getD 5 []=h4p98.getD 5 [] := by
  decide +kernel

theorem h4n98_arithmetic_row6 :
    (BiPoly.mul h4p97 h4p69).getD 6 []=h4p98.getD 6 [] := by
  decide +kernel

theorem h4n98_arithmetic_row7 :
    (BiPoly.mul h4p97 h4p69).getD 7 []=h4p98.getD 7 [] := by
  decide +kernel

theorem h4n98_arithmetic_row8 :
    (BiPoly.mul h4p97 h4p69).getD 8 []=h4p98.getD 8 [] := by
  decide +kernel

theorem h4n98_arithmetic_row9 :
    (BiPoly.mul h4p97 h4p69).getD 9 []=h4p98.getD 9 [] := by
  decide +kernel

theorem h4n98_arithmetic : BiPoly.mul h4p97 h4p69=h4p98 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p97 h4p69).getD j.val []=h4p98.getD j.val [] :=
      (fun j => Fin.cases h4n98_arithmetic_row0 (fun j => Fin.cases h4n98_arithmetic_row1 (fun j => Fin.cases h4n98_arithmetic_row2 (fun j => Fin.cases h4n98_arithmetic_row3 (fun j => Fin.cases h4n98_arithmetic_row4 (fun j => Fin.cases h4n98_arithmetic_row5 (fun j => Fin.cases h4n98_arithmetic_row6 (fun j => Fin.cases h4n98_arithmetic_row7 (fun j => Fin.cases h4n98_arithmetic_row8 (fun j => Fin.cases h4n98_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n98 : h4e98.toBi mapPolyEnv=h4p98 := by
  change BiPoly.mul (h4e97.toBi mapPolyEnv) (h4e69.toBi mapPolyEnv)=h4p98
  rw [h4n97, h4n69]
  exact h4n98_arithmetic

#print axioms h4n98_arithmetic
end StackSorting.RationalLift
