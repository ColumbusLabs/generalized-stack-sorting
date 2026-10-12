import BivariateRowEquality
import Horner5Base
import Horner5Node370
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p371 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8500704083), (Int.negSucc 30406986251), (Int.ofNat 22196486052), (Int.ofNat 44102768220)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 50013756936), (Int.ofNat 184084120260), (Int.negSucc 116915492447), (Int.negSucc 181400192171), (Int.ofNat 12077317296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 137273970167), (Int.negSucc 437699779271), (Int.ofNat 267462043632), (Int.ofNat 281068254468), (Int.negSucc 2174331995), (Int.negSucc 61292879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 229309539642), (Int.ofNat 505618078248), (Int.negSucc 217111858091), (Int.negSucc 143178791579), (Int.negSucc 70357880573), (Int.ofNat 2224030824)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 250872468119), (Int.negSucc 275363035595), (Int.negSucc 156706998911), (Int.negSucc 41818672547), (Int.ofNat 109151048880), (Int.ofNat 3725141796)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 180410283684), (Int.ofNat 52559781318), (Int.ofNat 397652569668), (Int.ofNat 75158871480), (Int.negSucc 21020433479), (Int.negSucc 6792878969)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 82435370615), (Int.negSucc 17026957943), (Int.negSucc 249835154723), (Int.negSucc 81874518551), (Int.negSucc 46146436919), (Int.negSucc 1637824859)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 22273640802), (Int.ofNat 35225220996), (Int.ofNat 51914572056), (Int.ofNat 69376431996), (Int.ofNat 30220716168), (Int.ofNat 4495061628)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3063129299), (Int.negSucc 22367688695), (Int.ofNat 3606128964), (Int.negSucc 23721079067), (Int.negSucc 8383813307), (Int.negSucc 1285015103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 138421224), (Int.ofNat 6039556074), (Int.negSucc 2723276159), (Int.ofNat 2188638468), (Int.ofNat 1285015104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 662309135), (Int.ofNat 415098108)]]

theorem h5n371_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p370).getD 0 []=h5p371.getD 0 [] := by
  decide +kernel

theorem h5n371_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p370).getD 1 []=h5p371.getD 1 [] := by
  decide +kernel

theorem h5n371_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p370).getD 2 []=h5p371.getD 2 [] := by
  decide +kernel

theorem h5n371_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p370).getD 3 []=h5p371.getD 3 [] := by
  decide +kernel

theorem h5n371_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p370).getD 4 []=h5p371.getD 4 [] := by
  decide +kernel

theorem h5n371_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p370).getD 5 []=h5p371.getD 5 [] := by
  decide +kernel

theorem h5n371_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p370).getD 6 []=h5p371.getD 6 [] := by
  decide +kernel

theorem h5n371_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p370).getD 7 []=h5p371.getD 7 [] := by
  decide +kernel

theorem h5n371_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p370).getD 8 []=h5p371.getD 8 [] := by
  decide +kernel

theorem h5n371_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p370).getD 9 []=h5p371.getD 9 [] := by
  decide +kernel

theorem h5n371_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p370).getD 10 []=h5p371.getD 10 [] := by
  decide +kernel

theorem h5n371_arithmetic : BiPoly.mul h5p22 h5p370=h5p371 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p22 h5p370).getD j.val []=h5p371.getD j.val [] :=
      (fun j => Fin.cases h5n371_arithmetic_row0 (fun j => Fin.cases h5n371_arithmetic_row1 (fun j => Fin.cases h5n371_arithmetic_row2 (fun j => Fin.cases h5n371_arithmetic_row3 (fun j => Fin.cases h5n371_arithmetic_row4 (fun j => Fin.cases h5n371_arithmetic_row5 (fun j => Fin.cases h5n371_arithmetic_row6 (fun j => Fin.cases h5n371_arithmetic_row7 (fun j => Fin.cases h5n371_arithmetic_row8 (fun j => Fin.cases h5n371_arithmetic_row9 (fun j => Fin.cases h5n371_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n371 : h5e371.toBi mapPolyEnv=h5p371 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e370.toBi mapPolyEnv)=h5p371
  rw [h5n22, h5n370]
  exact h5n371_arithmetic

#print axioms h5n371_arithmetic
end StackSorting.RationalLift
