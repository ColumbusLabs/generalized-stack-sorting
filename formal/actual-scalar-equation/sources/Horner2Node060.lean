import BivariateRowEquality
import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p60 : BiPoly.Poly := [[(Int.ofNat 1679616), (Int.ofNat 3359232), (Int.ofNat 1679616)], [(Int.negSucc 14618879), (Int.negSucc 23825663), (Int.negSucc 9891071), (Int.negSucc 684287)], [(Int.ofNat 56858688), (Int.ofNat 76437504), (Int.ofNat 33925248), (Int.ofNat 8428032), (Int.negSucc 386495)], [(Int.negSucc 130036223), (Int.negSucc 152408063), (Int.negSucc 91558655), (Int.negSucc 30644735), (Int.ofNat 175104), (Int.ofNat 92928)], [(Int.ofNat 193480960), (Int.ofNat 223738752), (Int.ofNat 182463872), (Int.ofNat 60839168), (Int.ofNat 9611392), (Int.negSucc 1023615), (Int.ofNat 30976)], [(Int.negSucc 195495935), (Int.negSucc 267459711), (Int.negSucc 249802239), (Int.negSucc 94164991), (Int.negSucc 31533055), (Int.ofNat 1790080), (Int.negSucc 47871)], [(Int.ofNat 135684480), (Int.ofNat 262093184), (Int.ofNat 238140096), (Int.ofNat 128941056), (Int.ofNat 44164288), (Int.ofNat 3753600), (Int.negSucc 316607)], [(Int.negSucc 63784447), (Int.negSucc 197144703), (Int.negSucc 172997759), (Int.negSucc 134082559), (Int.negSucc 39470079), (Int.negSucc 13445503), (Int.ofNat 630656)], [(Int.ofNat 19405824), (Int.ofNat 104892544), (Int.ofNat 108265024), (Int.ofNat 91987712), (Int.ofNat 33970688), (Int.ofNat 13844480), (Int.ofNat 568384)], [(Int.negSucc 3444479), (Int.negSucc 36286591), (Int.negSucc 58374143), (Int.negSucc 41605631), (Int.negSucc 26829567), (Int.negSucc 6579455), (Int.negSucc 1971455)], [(Int.ofNat 270400), (Int.ofNat 7227520), (Int.ofNat 22896832), (Int.ofNat 15326208), (Int.ofNat 13163904), (Int.ofNat 2694144), (Int.ofNat 1389312)], [(Int.ofNat 0), (Int.negSucc 623999), (Int.negSucc 5256575), (Int.negSucc 5701631), (Int.negSucc 3338495), (Int.negSucc 1541375), (Int.negSucc 304127)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 509760), (Int.ofNat 1534464), (Int.ofNat 603648), (Int.ofNat 456192), (Int.ofNat 20736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 172799), (Int.negSucc 152063), (Int.negSucc 41471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20736)]]

theorem h2n60_arithmetic_row0 :
    (BiPoly.mul h2p34 h2p34).getD 0 []=h2p60.getD 0 [] := by
  decide +kernel

theorem h2n60_arithmetic_row1 :
    (BiPoly.mul h2p34 h2p34).getD 1 []=h2p60.getD 1 [] := by
  decide +kernel

theorem h2n60_arithmetic_row2 :
    (BiPoly.mul h2p34 h2p34).getD 2 []=h2p60.getD 2 [] := by
  decide +kernel

theorem h2n60_arithmetic_row3 :
    (BiPoly.mul h2p34 h2p34).getD 3 []=h2p60.getD 3 [] := by
  decide +kernel

theorem h2n60_arithmetic_row4 :
    (BiPoly.mul h2p34 h2p34).getD 4 []=h2p60.getD 4 [] := by
  decide +kernel

theorem h2n60_arithmetic_row5 :
    (BiPoly.mul h2p34 h2p34).getD 5 []=h2p60.getD 5 [] := by
  decide +kernel

theorem h2n60_arithmetic_row6 :
    (BiPoly.mul h2p34 h2p34).getD 6 []=h2p60.getD 6 [] := by
  decide +kernel

theorem h2n60_arithmetic_row7 :
    (BiPoly.mul h2p34 h2p34).getD 7 []=h2p60.getD 7 [] := by
  decide +kernel

theorem h2n60_arithmetic_row8 :
    (BiPoly.mul h2p34 h2p34).getD 8 []=h2p60.getD 8 [] := by
  decide +kernel

theorem h2n60_arithmetic_row9 :
    (BiPoly.mul h2p34 h2p34).getD 9 []=h2p60.getD 9 [] := by
  decide +kernel

theorem h2n60_arithmetic_row10 :
    (BiPoly.mul h2p34 h2p34).getD 10 []=h2p60.getD 10 [] := by
  decide +kernel

theorem h2n60_arithmetic_row11 :
    (BiPoly.mul h2p34 h2p34).getD 11 []=h2p60.getD 11 [] := by
  decide +kernel

theorem h2n60_arithmetic_row12 :
    (BiPoly.mul h2p34 h2p34).getD 12 []=h2p60.getD 12 [] := by
  decide +kernel

theorem h2n60_arithmetic_row13 :
    (BiPoly.mul h2p34 h2p34).getD 13 []=h2p60.getD 13 [] := by
  decide +kernel

theorem h2n60_arithmetic_row14 :
    (BiPoly.mul h2p34 h2p34).getD 14 []=h2p60.getD 14 [] := by
  decide +kernel

theorem h2n60_arithmetic : BiPoly.mul h2p34 h2p34=h2p60 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<15 at hk
    have hf : ∀ j : Fin 15, (BiPoly.mul h2p34 h2p34).getD j.val []=h2p60.getD j.val [] :=
      (fun j => Fin.cases h2n60_arithmetic_row0 (fun j => Fin.cases h2n60_arithmetic_row1 (fun j => Fin.cases h2n60_arithmetic_row2 (fun j => Fin.cases h2n60_arithmetic_row3 (fun j => Fin.cases h2n60_arithmetic_row4 (fun j => Fin.cases h2n60_arithmetic_row5 (fun j => Fin.cases h2n60_arithmetic_row6 (fun j => Fin.cases h2n60_arithmetic_row7 (fun j => Fin.cases h2n60_arithmetic_row8 (fun j => Fin.cases h2n60_arithmetic_row9 (fun j => Fin.cases h2n60_arithmetic_row10 (fun j => Fin.cases h2n60_arithmetic_row11 (fun j => Fin.cases h2n60_arithmetic_row12 (fun j => Fin.cases h2n60_arithmetic_row13 (fun j => Fin.cases h2n60_arithmetic_row14 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n60 : h2e60.toBi mapPolyEnv=h2p60 := by
  change BiPoly.mul (h2e34.toBi mapPolyEnv) (h2e34.toBi mapPolyEnv)=h2p60
  rw [h2n34]
  exact h2n60_arithmetic

#print axioms h2n60_arithmetic
end StackSorting.RationalLift
