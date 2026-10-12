import BivariateRowEquality
import Horner5Base
import Horner5Node140
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p141 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 6452135999), (Int.negSucc 19257536159), (Int.ofNat 16651565280), (Int.negSucc 19257536159), (Int.ofNat 23103701280)], [(Int.ofNat 0), (Int.ofNat 34526096640), (Int.ofNat 89448824448), (Int.negSucc 114802990847), (Int.ofNat 110156410944), (Int.negSucc 100515714047), (Int.ofNat 10409285376)], [(Int.ofNat 0), (Int.negSucc 77662210319), (Int.negSucc 180937389383), (Int.ofNat 256547776896), (Int.negSucc 247174227359), (Int.ofNat 140491597104), (Int.negSucc 3881302199), (Int.ofNat 1105423488)], [(Int.ofNat 0), (Int.ofNat 94996949040), (Int.ofNat 213442475976), (Int.negSucc 219698142263), (Int.ofNat 201439511208), (Int.negSucc 4757733575), (Int.negSucc 60976055663), (Int.ofNat 3991019760)], [(Int.ofNat 0), (Int.negSucc 68118624959), (Int.negSucc 164480270207), (Int.negSucc 15521908151), (Int.ofNat 59876182440), (Int.negSucc 196776420095), (Int.ofNat 84773920344), (Int.negSucc 3467111063)], [(Int.ofNat 0), (Int.ofNat 28599690240), (Int.ofNat 85007783040), (Int.ofNat 170903149752), (Int.negSucc 180590388383), (Int.ofNat 188362729440), (Int.negSucc 4529327735), (Int.negSucc 12890026847)], [(Int.ofNat 0), (Int.negSucc 6511877999), (Int.negSucc 27903156599), (Int.negSucc 133240657799), (Int.ofNat 66738467256), (Int.negSucc 21685344647), (Int.negSucc 58915138655), (Int.ofNat 10594183968)], [(Int.ofNat 0), (Int.ofNat 622113360), (Int.ofNat 5034519480), (Int.ofNat 45424740144), (Int.ofNat 27382312824), (Int.negSucc 46505611583), (Int.ofNat 35703473184), (Int.ofNat 3494900592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 355250591), (Int.negSucc 6415450559), (Int.negSucc 22659393599), (Int.ofNat 17013972960), (Int.negSucc 673987391), (Int.negSucc 4448498111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 151917552), (Int.ofNat 4069305504), (Int.ofNat 1154328048), (Int.negSucc 4396163039), (Int.ofNat 874717920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 52335071), (Int.negSucc 822382847), (Int.ofNat 874717920)]]

theorem h5n141_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p140).getD 0 []=h5p141.getD 0 [] := by
  decide +kernel

theorem h5n141_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p140).getD 1 []=h5p141.getD 1 [] := by
  decide +kernel

theorem h5n141_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p140).getD 2 []=h5p141.getD 2 [] := by
  decide +kernel

theorem h5n141_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p140).getD 3 []=h5p141.getD 3 [] := by
  decide +kernel

theorem h5n141_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p140).getD 4 []=h5p141.getD 4 [] := by
  decide +kernel

theorem h5n141_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p140).getD 5 []=h5p141.getD 5 [] := by
  decide +kernel

theorem h5n141_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p140).getD 6 []=h5p141.getD 6 [] := by
  decide +kernel

theorem h5n141_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p140).getD 7 []=h5p141.getD 7 [] := by
  decide +kernel

theorem h5n141_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p140).getD 8 []=h5p141.getD 8 [] := by
  decide +kernel

theorem h5n141_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p140).getD 9 []=h5p141.getD 9 [] := by
  decide +kernel

theorem h5n141_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p140).getD 10 []=h5p141.getD 10 [] := by
  decide +kernel

theorem h5n141_arithmetic : BiPoly.mul h5p6 h5p140=h5p141 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p140).getD j.val []=h5p141.getD j.val [] :=
      (fun j => Fin.cases h5n141_arithmetic_row0 (fun j => Fin.cases h5n141_arithmetic_row1 (fun j => Fin.cases h5n141_arithmetic_row2 (fun j => Fin.cases h5n141_arithmetic_row3 (fun j => Fin.cases h5n141_arithmetic_row4 (fun j => Fin.cases h5n141_arithmetic_row5 (fun j => Fin.cases h5n141_arithmetic_row6 (fun j => Fin.cases h5n141_arithmetic_row7 (fun j => Fin.cases h5n141_arithmetic_row8 (fun j => Fin.cases h5n141_arithmetic_row9 (fun j => Fin.cases h5n141_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n141 : h5e141.toBi mapPolyEnv=h5p141 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e140.toBi mapPolyEnv)=h5p141
  rw [h5n6, h5n140]
  exact h5n141_arithmetic

#print axioms h5n141_arithmetic
end StackSorting.RationalLift
