import BivariateRowEquality
import Horner0Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p67 : BiPoly.Poly := [[(Int.ofNat 1679616), (Int.ofNat 3359232), (Int.ofNat 1679616)], [(Int.negSucc 14618879), (Int.negSucc 23825663), (Int.negSucc 9891071), (Int.negSucc 684287)], [(Int.ofNat 56858688), (Int.ofNat 76437504), (Int.ofNat 33925248), (Int.ofNat 8428032), (Int.negSucc 386495)], [(Int.negSucc 130036223), (Int.negSucc 152408063), (Int.negSucc 91558655), (Int.negSucc 30644735), (Int.ofNat 175104), (Int.ofNat 92928)], [(Int.ofNat 193480960), (Int.ofNat 223738752), (Int.ofNat 182463872), (Int.ofNat 60839168), (Int.ofNat 9611392), (Int.negSucc 1023615), (Int.ofNat 30976)], [(Int.negSucc 195495935), (Int.negSucc 267459711), (Int.negSucc 249802239), (Int.negSucc 94164991), (Int.negSucc 31533055), (Int.ofNat 1790080), (Int.negSucc 47871)], [(Int.ofNat 135684480), (Int.ofNat 262093184), (Int.ofNat 238140096), (Int.ofNat 128941056), (Int.ofNat 44164288), (Int.ofNat 3753600), (Int.negSucc 316607)], [(Int.negSucc 63784447), (Int.negSucc 197144703), (Int.negSucc 172997759), (Int.negSucc 134082559), (Int.negSucc 39470079), (Int.negSucc 13445503), (Int.ofNat 630656)], [(Int.ofNat 19405824), (Int.ofNat 104892544), (Int.ofNat 108265024), (Int.ofNat 91987712), (Int.ofNat 33970688), (Int.ofNat 13844480), (Int.ofNat 568384)], [(Int.negSucc 3444479), (Int.negSucc 36286591), (Int.negSucc 58374143), (Int.negSucc 41605631), (Int.negSucc 26829567), (Int.negSucc 6579455), (Int.negSucc 1971455)], [(Int.ofNat 270400), (Int.ofNat 7227520), (Int.ofNat 22896832), (Int.ofNat 15326208), (Int.ofNat 13163904), (Int.ofNat 2694144), (Int.ofNat 1389312)], [(Int.ofNat 0), (Int.negSucc 623999), (Int.negSucc 5256575), (Int.negSucc 5701631), (Int.negSucc 3338495), (Int.negSucc 1541375), (Int.negSucc 304127)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 509760), (Int.ofNat 1534464), (Int.ofNat 603648), (Int.ofNat 456192), (Int.ofNat 20736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 172799), (Int.negSucc 152063), (Int.negSucc 41471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20736)]]

theorem h0n67_arithmetic_row0 :
    (BiPoly.mul h0p35 h0p35).getD 0 []=h0p67.getD 0 [] := by
  decide +kernel

theorem h0n67_arithmetic_row1 :
    (BiPoly.mul h0p35 h0p35).getD 1 []=h0p67.getD 1 [] := by
  decide +kernel

theorem h0n67_arithmetic_row2 :
    (BiPoly.mul h0p35 h0p35).getD 2 []=h0p67.getD 2 [] := by
  decide +kernel

theorem h0n67_arithmetic_row3 :
    (BiPoly.mul h0p35 h0p35).getD 3 []=h0p67.getD 3 [] := by
  decide +kernel

theorem h0n67_arithmetic_row4 :
    (BiPoly.mul h0p35 h0p35).getD 4 []=h0p67.getD 4 [] := by
  decide +kernel

theorem h0n67_arithmetic_row5 :
    (BiPoly.mul h0p35 h0p35).getD 5 []=h0p67.getD 5 [] := by
  decide +kernel

theorem h0n67_arithmetic_row6 :
    (BiPoly.mul h0p35 h0p35).getD 6 []=h0p67.getD 6 [] := by
  decide +kernel

theorem h0n67_arithmetic_row7 :
    (BiPoly.mul h0p35 h0p35).getD 7 []=h0p67.getD 7 [] := by
  decide +kernel

theorem h0n67_arithmetic_row8 :
    (BiPoly.mul h0p35 h0p35).getD 8 []=h0p67.getD 8 [] := by
  decide +kernel

theorem h0n67_arithmetic_row9 :
    (BiPoly.mul h0p35 h0p35).getD 9 []=h0p67.getD 9 [] := by
  decide +kernel

theorem h0n67_arithmetic_row10 :
    (BiPoly.mul h0p35 h0p35).getD 10 []=h0p67.getD 10 [] := by
  decide +kernel

theorem h0n67_arithmetic_row11 :
    (BiPoly.mul h0p35 h0p35).getD 11 []=h0p67.getD 11 [] := by
  decide +kernel

theorem h0n67_arithmetic_row12 :
    (BiPoly.mul h0p35 h0p35).getD 12 []=h0p67.getD 12 [] := by
  decide +kernel

theorem h0n67_arithmetic_row13 :
    (BiPoly.mul h0p35 h0p35).getD 13 []=h0p67.getD 13 [] := by
  decide +kernel

theorem h0n67_arithmetic_row14 :
    (BiPoly.mul h0p35 h0p35).getD 14 []=h0p67.getD 14 [] := by
  decide +kernel

theorem h0n67_arithmetic : BiPoly.mul h0p35 h0p35=h0p67 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<15 at hk
    have hf : ∀ j : Fin 15, (BiPoly.mul h0p35 h0p35).getD j.val []=h0p67.getD j.val [] :=
      (fun j => Fin.cases h0n67_arithmetic_row0 (fun j => Fin.cases h0n67_arithmetic_row1 (fun j => Fin.cases h0n67_arithmetic_row2 (fun j => Fin.cases h0n67_arithmetic_row3 (fun j => Fin.cases h0n67_arithmetic_row4 (fun j => Fin.cases h0n67_arithmetic_row5 (fun j => Fin.cases h0n67_arithmetic_row6 (fun j => Fin.cases h0n67_arithmetic_row7 (fun j => Fin.cases h0n67_arithmetic_row8 (fun j => Fin.cases h0n67_arithmetic_row9 (fun j => Fin.cases h0n67_arithmetic_row10 (fun j => Fin.cases h0n67_arithmetic_row11 (fun j => Fin.cases h0n67_arithmetic_row12 (fun j => Fin.cases h0n67_arithmetic_row13 (fun j => Fin.cases h0n67_arithmetic_row14 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n67 : h0e67.toBi mapPolyEnv=h0p67 := by
  change BiPoly.mul (h0e35.toBi mapPolyEnv) (h0e35.toBi mapPolyEnv)=h0p67
  rw [h0n35]
  exact h0n67_arithmetic

#print axioms h0n67_arithmetic
end StackSorting.RationalLift
