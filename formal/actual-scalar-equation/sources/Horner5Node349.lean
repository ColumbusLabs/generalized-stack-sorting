import BivariateRowEquality
import Horner5Base
import Horner5Node348
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p349 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 12904272000), (Int.ofNat 25610800320), (Int.negSucc 84722474879), (Int.ofNat 46207402560)], [(Int.ofNat 0), (Int.negSucc 69052193279), (Int.negSucc 109845455615), (Int.ofNat 477555823872), (Int.negSucc 314264803967), (Int.ofNat 20818570752)], [(Int.ofNat 0), (Int.ofNat 155324420640), (Int.ofNat 206550358128), (Int.negSucc 1030294753199), (Int.ofNat 688597807824), (Int.negSucc 51610592879), (Int.ofNat 2210846976)], [(Int.ofNat 0), (Int.negSucc 189993898079), (Int.negSucc 236891053871), (Int.ofNat 1056275134560), (Int.negSucc 407031254351), (Int.negSucc 114408942047), (Int.ofNat 3560345568)], [(Int.ofNat 0), (Int.ofNat 136237249920), (Int.ofNat 192723290496), (Int.negSucc 434153974031), (Int.negSucc 525154269119), (Int.ofNat 424807979424), (Int.negSucc 22898301167)], [(Int.ofNat 0), (Int.negSucc 57199380479), (Int.negSucc 112816185599), (Int.negSucc 114591352943), (Int.ofNat 906642964272), (Int.negSucc 306410204111), (Int.negSucc 11911609439)], [(Int.ofNat 0), (Int.ofNat 13023756000), (Int.ofNat 42782557200), (Int.ofNat 197651246400), (Int.negSucc 466299865871), (Int.negSucc 134769778559), (Int.ofNat 72748475328)], [(Int.ofNat 0), (Int.negSucc 1244226719), (Int.negSucc 8824812239), (Int.negSucc 79536214607), (Int.ofNat 47398120320), (Int.ofNat 248517592416), (Int.negSucc 35386934687)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 710501184), (Int.ofNat 12120399936), (Int.ofNat 31777384896), (Int.negSucc 92888135423), (Int.negSucc 22876598591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 303835103), (Int.negSucc 7834775903), (Int.ofNat 6133790016), (Int.ofNat 19543428288)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 104670144), (Int.ofNat 1540095552), (Int.negSucc 3498871679)]]

theorem h5n349_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p348).getD 0 []=h5p349.getD 0 [] := by
  decide +kernel

theorem h5n349_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p348).getD 1 []=h5p349.getD 1 [] := by
  decide +kernel

theorem h5n349_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p348).getD 2 []=h5p349.getD 2 [] := by
  decide +kernel

theorem h5n349_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p348).getD 3 []=h5p349.getD 3 [] := by
  decide +kernel

theorem h5n349_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p348).getD 4 []=h5p349.getD 4 [] := by
  decide +kernel

theorem h5n349_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p348).getD 5 []=h5p349.getD 5 [] := by
  decide +kernel

theorem h5n349_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p348).getD 6 []=h5p349.getD 6 [] := by
  decide +kernel

theorem h5n349_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p348).getD 7 []=h5p349.getD 7 [] := by
  decide +kernel

theorem h5n349_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p348).getD 8 []=h5p349.getD 8 [] := by
  decide +kernel

theorem h5n349_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p348).getD 9 []=h5p349.getD 9 [] := by
  decide +kernel

theorem h5n349_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p348).getD 10 []=h5p349.getD 10 [] := by
  decide +kernel

theorem h5n349_arithmetic : BiPoly.mul h5p6 h5p348=h5p349 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p348).getD j.val []=h5p349.getD j.val [] :=
      (fun j => Fin.cases h5n349_arithmetic_row0 (fun j => Fin.cases h5n349_arithmetic_row1 (fun j => Fin.cases h5n349_arithmetic_row2 (fun j => Fin.cases h5n349_arithmetic_row3 (fun j => Fin.cases h5n349_arithmetic_row4 (fun j => Fin.cases h5n349_arithmetic_row5 (fun j => Fin.cases h5n349_arithmetic_row6 (fun j => Fin.cases h5n349_arithmetic_row7 (fun j => Fin.cases h5n349_arithmetic_row8 (fun j => Fin.cases h5n349_arithmetic_row9 (fun j => Fin.cases h5n349_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n349 : h5e349.toBi mapPolyEnv=h5p349 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e348.toBi mapPolyEnv)=h5p349
  rw [h5n6, h5n348]
  exact h5n349_arithmetic

#print axioms h5n349_arithmetic
end StackSorting.RationalLift
