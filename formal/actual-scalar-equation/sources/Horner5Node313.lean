import BivariateRowEquality
import Horner5Base
import Horner5Node312
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p313 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 12904271999), (Int.negSucc 25610800319), (Int.ofNat 84722474880), (Int.negSucc 46207402559)], [(Int.ofNat 0), (Int.ofNat 69052193280), (Int.ofNat 109845455616), (Int.negSucc 477555823871), (Int.ofNat 314264803968), (Int.negSucc 20818570751)], [(Int.ofNat 0), (Int.negSucc 155324420639), (Int.negSucc 206550358127), (Int.ofNat 1030294753200), (Int.negSucc 688597807823), (Int.ofNat 51610592880), (Int.negSucc 2210846975)], [(Int.ofNat 0), (Int.ofNat 189993898080), (Int.ofNat 236891053872), (Int.negSucc 1056275134559), (Int.ofNat 407031254352), (Int.ofNat 114408942048), (Int.negSucc 3560345567)], [(Int.ofNat 0), (Int.negSucc 136237249919), (Int.negSucc 192723290495), (Int.ofNat 434153974032), (Int.ofNat 525154269120), (Int.negSucc 424807979423), (Int.ofNat 22898301168)], [(Int.ofNat 0), (Int.ofNat 57199380480), (Int.ofNat 112816185600), (Int.ofNat 114591352944), (Int.negSucc 906642964271), (Int.ofNat 306410204112), (Int.ofNat 11911609440)], [(Int.ofNat 0), (Int.negSucc 13023755999), (Int.negSucc 42782557199), (Int.negSucc 197651246399), (Int.ofNat 466299865872), (Int.ofNat 134769778560), (Int.negSucc 72748475327)], [(Int.ofNat 0), (Int.ofNat 1244226720), (Int.ofNat 8824812240), (Int.ofNat 79536214608), (Int.negSucc 47398120319), (Int.negSucc 248517592415), (Int.ofNat 35386934688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 710501183), (Int.negSucc 12120399935), (Int.negSucc 31777384895), (Int.ofNat 92888135424), (Int.ofNat 22876598592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 303835104), (Int.ofNat 7834775904), (Int.negSucc 6133790015), (Int.negSucc 19543428287)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 104670143), (Int.negSucc 1540095551), (Int.ofNat 3498871680)]]

theorem h5n313_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p312).getD 0 []=h5p313.getD 0 [] := by
  decide +kernel

theorem h5n313_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p312).getD 1 []=h5p313.getD 1 [] := by
  decide +kernel

theorem h5n313_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p312).getD 2 []=h5p313.getD 2 [] := by
  decide +kernel

theorem h5n313_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p312).getD 3 []=h5p313.getD 3 [] := by
  decide +kernel

theorem h5n313_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p312).getD 4 []=h5p313.getD 4 [] := by
  decide +kernel

theorem h5n313_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p312).getD 5 []=h5p313.getD 5 [] := by
  decide +kernel

theorem h5n313_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p312).getD 6 []=h5p313.getD 6 [] := by
  decide +kernel

theorem h5n313_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p312).getD 7 []=h5p313.getD 7 [] := by
  decide +kernel

theorem h5n313_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p312).getD 8 []=h5p313.getD 8 [] := by
  decide +kernel

theorem h5n313_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p312).getD 9 []=h5p313.getD 9 [] := by
  decide +kernel

theorem h5n313_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p312).getD 10 []=h5p313.getD 10 [] := by
  decide +kernel

theorem h5n313_arithmetic : BiPoly.mul h5p6 h5p312=h5p313 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p312).getD j.val []=h5p313.getD j.val [] :=
      (fun j => Fin.cases h5n313_arithmetic_row0 (fun j => Fin.cases h5n313_arithmetic_row1 (fun j => Fin.cases h5n313_arithmetic_row2 (fun j => Fin.cases h5n313_arithmetic_row3 (fun j => Fin.cases h5n313_arithmetic_row4 (fun j => Fin.cases h5n313_arithmetic_row5 (fun j => Fin.cases h5n313_arithmetic_row6 (fun j => Fin.cases h5n313_arithmetic_row7 (fun j => Fin.cases h5n313_arithmetic_row8 (fun j => Fin.cases h5n313_arithmetic_row9 (fun j => Fin.cases h5n313_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n313 : h5e313.toBi mapPolyEnv=h5p313 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e312.toBi mapPolyEnv)=h5p313
  rw [h5n6, h5n312]
  exact h5n313_arithmetic

#print axioms h5n313_arithmetic
end StackSorting.RationalLift
