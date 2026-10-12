import BivariateRowEquality
import Horner5Base
import Horner5Node120
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p121 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 9678204000), (Int.ofNat 19208100240), (Int.negSucc 63541856159), (Int.ofNat 34655551920)], [(Int.ofNat 0), (Int.negSucc 51789144959), (Int.negSucc 82384091711), (Int.ofNat 358166867904), (Int.negSucc 235698602975), (Int.ofNat 15613928064)], [(Int.ofNat 0), (Int.ofNat 116493315480), (Int.ofNat 154912768596), (Int.negSucc 772721064899), (Int.ofNat 516448355868), (Int.negSucc 38707944659), (Int.ofNat 1658135232)], [(Int.ofNat 0), (Int.negSucc 142495423559), (Int.negSucc 177668290403), (Int.ofNat 792206350920), (Int.negSucc 305273440763), (Int.negSucc 85806706535), (Int.ofNat 2670259176)], [(Int.ofNat 0), (Int.ofNat 102177937440), (Int.ofNat 144542467872), (Int.negSucc 325615480523), (Int.negSucc 393865701839), (Int.ofNat 318605984568), (Int.negSucc 17173725875)], [(Int.ofNat 0), (Int.negSucc 42899535359), (Int.negSucc 84612139199), (Int.negSucc 85943514707), (Int.ofNat 679982223204), (Int.negSucc 229807653083), (Int.negSucc 8933707079)], [(Int.ofNat 0), (Int.ofNat 9767817000), (Int.ofNat 32086917900), (Int.ofNat 148238434800), (Int.negSucc 349724899403), (Int.negSucc 101077333919), (Int.ofNat 54561356496)], [(Int.ofNat 0), (Int.negSucc 933170039), (Int.negSucc 6618609179), (Int.negSucc 59652160955), (Int.ofNat 35548590240), (Int.ofNat 186388194312), (Int.negSucc 26540201015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 532875888), (Int.ofNat 9090299952), (Int.ofNat 23833038672), (Int.negSucc 69666101567), (Int.negSucc 17157448943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 227876327), (Int.negSucc 5876081927), (Int.ofNat 4600342512), (Int.ofNat 14657571216)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 78502608), (Int.ofNat 1155071664), (Int.negSucc 2624153759)]]

theorem h5n121_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p120).getD 0 []=h5p121.getD 0 [] := by
  decide +kernel

theorem h5n121_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p120).getD 1 []=h5p121.getD 1 [] := by
  decide +kernel

theorem h5n121_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p120).getD 2 []=h5p121.getD 2 [] := by
  decide +kernel

theorem h5n121_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p120).getD 3 []=h5p121.getD 3 [] := by
  decide +kernel

theorem h5n121_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p120).getD 4 []=h5p121.getD 4 [] := by
  decide +kernel

theorem h5n121_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p120).getD 5 []=h5p121.getD 5 [] := by
  decide +kernel

theorem h5n121_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p120).getD 6 []=h5p121.getD 6 [] := by
  decide +kernel

theorem h5n121_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p120).getD 7 []=h5p121.getD 7 [] := by
  decide +kernel

theorem h5n121_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p120).getD 8 []=h5p121.getD 8 [] := by
  decide +kernel

theorem h5n121_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p120).getD 9 []=h5p121.getD 9 [] := by
  decide +kernel

theorem h5n121_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p120).getD 10 []=h5p121.getD 10 [] := by
  decide +kernel

theorem h5n121_arithmetic : BiPoly.mul h5p6 h5p120=h5p121 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p120).getD j.val []=h5p121.getD j.val [] :=
      (fun j => Fin.cases h5n121_arithmetic_row0 (fun j => Fin.cases h5n121_arithmetic_row1 (fun j => Fin.cases h5n121_arithmetic_row2 (fun j => Fin.cases h5n121_arithmetic_row3 (fun j => Fin.cases h5n121_arithmetic_row4 (fun j => Fin.cases h5n121_arithmetic_row5 (fun j => Fin.cases h5n121_arithmetic_row6 (fun j => Fin.cases h5n121_arithmetic_row7 (fun j => Fin.cases h5n121_arithmetic_row8 (fun j => Fin.cases h5n121_arithmetic_row9 (fun j => Fin.cases h5n121_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n121 : h5e121.toBi mapPolyEnv=h5p121 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e120.toBi mapPolyEnv)=h5p121
  rw [h5n6, h5n120]
  exact h5n121_arithmetic

#print axioms h5n121_arithmetic
end StackSorting.RationalLift
