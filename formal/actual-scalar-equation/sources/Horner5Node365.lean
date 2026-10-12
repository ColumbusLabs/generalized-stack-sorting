import BivariateRowEquality
import Horner5Base
import Horner5Node364
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p365 : BiPoly.Poly := [[(Int.ofNat 2150712000), (Int.ofNat 2117754720), (Int.negSucc 22690303199), (Int.ofNat 8983288800), (Int.ofNat 7701233760)], [(Int.negSucc 11508698879), (Int.negSucc 6798877055), (Int.ofNat 120917611008), (Int.negSucc 68036131007), (Int.negSucc 26565714431), (Int.ofNat 3469761792)], [(Int.ofNat 25887403440), (Int.ofNat 8537656248), (Int.negSucc 257915658767), (Int.ofNat 147141193488), (Int.ofNat 29627001408), (Int.negSucc 556818407), (Int.ofNat 368474496)], [(Int.negSucc 31665649679), (Int.negSucc 7816192631), (Int.ofNat 278858997432), (Int.negSucc 68530581047), (Int.negSucc 39722225207), (Int.negSucc 19138570031), (Int.ofNat 1330339920)], [(Int.ofNat 22706208320), (Int.ofNat 9414340096), (Int.negSucc 149891960727), (Int.negSucc 155092695559), (Int.ofNat 76010519776), (Int.ofNat 20625206392), (Int.negSucc 1155703687)], [(Int.negSucc 9533230079), (Int.negSucc 9269467519), (Int.ofNat 18770598936), (Int.ofNat 242017525296), (Int.negSucc 39349158223), (Int.negSucc 5480312391), (Int.negSucc 4296675615)], [(Int.ofNat 2170626000), (Int.ofNat 4959800200), (Int.ofNat 21470196200), (Int.negSucc 133187132871), (Int.negSucc 52151707735), (Int.ofNat 4611112224), (Int.ofNat 3531394656)], [(Int.negSucc 207371119), (Int.negSucc 1263430919), (Int.negSucc 11370491487), (Int.ofNat 24926811048), (Int.ofNat 67337326944), (Int.ofNat 105512832), (Int.ofNat 1164966864)], [(Int.ofNat 0), (Int.ofNat 118416864), (Int.ofNat 1901649792), (Int.ofNat 3039330432), (Int.negSucc 25291387487), (Int.negSucc 7850195327), (Int.negSucc 1482832703)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 50639183), (Int.negSucc 1255156799), (Int.ofNat 2429372688), (Int.ofNat 5049088416), (Int.ofNat 291572640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 17445024), (Int.ofNat 239237568), (Int.negSucc 874717919)]]

theorem h5n365_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p364).getD 0 []=h5p365.getD 0 [] := by
  decide +kernel

theorem h5n365_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p364).getD 1 []=h5p365.getD 1 [] := by
  decide +kernel

theorem h5n365_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p364).getD 2 []=h5p365.getD 2 [] := by
  decide +kernel

theorem h5n365_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p364).getD 3 []=h5p365.getD 3 [] := by
  decide +kernel

theorem h5n365_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p364).getD 4 []=h5p365.getD 4 [] := by
  decide +kernel

theorem h5n365_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p364).getD 5 []=h5p365.getD 5 [] := by
  decide +kernel

theorem h5n365_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p364).getD 6 []=h5p365.getD 6 [] := by
  decide +kernel

theorem h5n365_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p364).getD 7 []=h5p365.getD 7 [] := by
  decide +kernel

theorem h5n365_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p364).getD 8 []=h5p365.getD 8 [] := by
  decide +kernel

theorem h5n365_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p364).getD 9 []=h5p365.getD 9 [] := by
  decide +kernel

theorem h5n365_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p364).getD 10 []=h5p365.getD 10 [] := by
  decide +kernel

theorem h5n365_arithmetic : BiPoly.mul h5p6 h5p364=h5p365 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p364).getD j.val []=h5p365.getD j.val [] :=
      (fun j => Fin.cases h5n365_arithmetic_row0 (fun j => Fin.cases h5n365_arithmetic_row1 (fun j => Fin.cases h5n365_arithmetic_row2 (fun j => Fin.cases h5n365_arithmetic_row3 (fun j => Fin.cases h5n365_arithmetic_row4 (fun j => Fin.cases h5n365_arithmetic_row5 (fun j => Fin.cases h5n365_arithmetic_row6 (fun j => Fin.cases h5n365_arithmetic_row7 (fun j => Fin.cases h5n365_arithmetic_row8 (fun j => Fin.cases h5n365_arithmetic_row9 (fun j => Fin.cases h5n365_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n365 : h5e365.toBi mapPolyEnv=h5p365 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e364.toBi mapPolyEnv)=h5p365
  rw [h5n6, h5n364]
  exact h5n365_arithmetic

#print axioms h5n365_arithmetic
end StackSorting.RationalLift
