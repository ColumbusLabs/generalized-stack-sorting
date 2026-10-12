import BivariateRowEquality
import Horner5Base
import Horner5Node249
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p250 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14517306000), (Int.ofNat 57846762360), (Int.negSucc 8653871519), (Int.negSucc 51983327879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 77683717439), (Int.negSucc 278943572447), (Int.ofNat 105695979840), (Int.ofNat 202739464512), (Int.negSucc 23420892095)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 174739973220), (Int.ofNat 581849099334), (Int.negSucc 218530522241), (Int.negSucc 258044176493), (Int.ofNat 6245727102), (Int.negSucc 2487202847)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 213743135339), (Int.negSucc 693988706285), (Int.ofNat 4671260928), (Int.ofNat 139414960350), (Int.ofNat 133190736480), (Int.negSucc 8979794459)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 153266906160), (Int.ofNat 523347514128), (Int.ofNat 456077142270), (Int.negSucc 35162031635), (Int.negSucc 164980731959), (Int.ofNat 7800999894)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 64349303039), (Int.negSucc 255616814879), (Int.negSucc 613644960941), (Int.negSucc 79104661613), (Int.ofNat 23591548026), (Int.ofNat 29002560408)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14651725500), (Int.ofNat 77433827850), (Int.ofNat 374425797780), (Int.ofNat 200408026338), (Int.ofNat 50717027232), (Int.negSucc 23836913927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1399755059), (Int.negSucc 12727423889), (Int.negSucc 114933089213), (Int.negSucc 174944665403), (Int.negSucc 40522513139), (Int.negSucc 7863526331)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 799313832), (Int.ofNat 15234077592), (Int.ofNat 66217713192), (Int.ofNat 27252645048), (Int.ofNat 10009120752)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 341814491), (Int.negSucc 9497751875), (Int.negSucc 12094989983), (Int.negSucc 1968115319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 117753912), (Int.ofNat 1968115320)]]

theorem h5n250_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p249).getD 0 []=h5p250.getD 0 [] := by
  decide +kernel

theorem h5n250_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p249).getD 1 []=h5p250.getD 1 [] := by
  decide +kernel

theorem h5n250_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p249).getD 2 []=h5p250.getD 2 [] := by
  decide +kernel

theorem h5n250_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p249).getD 3 []=h5p250.getD 3 [] := by
  decide +kernel

theorem h5n250_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p249).getD 4 []=h5p250.getD 4 [] := by
  decide +kernel

theorem h5n250_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p249).getD 5 []=h5p250.getD 5 [] := by
  decide +kernel

theorem h5n250_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p249).getD 6 []=h5p250.getD 6 [] := by
  decide +kernel

theorem h5n250_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p249).getD 7 []=h5p250.getD 7 [] := by
  decide +kernel

theorem h5n250_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p249).getD 8 []=h5p250.getD 8 [] := by
  decide +kernel

theorem h5n250_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p249).getD 9 []=h5p250.getD 9 [] := by
  decide +kernel

theorem h5n250_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p249).getD 10 []=h5p250.getD 10 [] := by
  decide +kernel

theorem h5n250_arithmetic : BiPoly.mul h5p6 h5p249=h5p250 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p249).getD j.val []=h5p250.getD j.val [] :=
      (fun j => Fin.cases h5n250_arithmetic_row0 (fun j => Fin.cases h5n250_arithmetic_row1 (fun j => Fin.cases h5n250_arithmetic_row2 (fun j => Fin.cases h5n250_arithmetic_row3 (fun j => Fin.cases h5n250_arithmetic_row4 (fun j => Fin.cases h5n250_arithmetic_row5 (fun j => Fin.cases h5n250_arithmetic_row6 (fun j => Fin.cases h5n250_arithmetic_row7 (fun j => Fin.cases h5n250_arithmetic_row8 (fun j => Fin.cases h5n250_arithmetic_row9 (fun j => Fin.cases h5n250_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n250 : h5e250.toBi mapPolyEnv=h5p250 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e249.toBi mapPolyEnv)=h5p250
  rw [h5n6, h5n249]
  exact h5n250_arithmetic

#print axioms h5n250_arithmetic
end StackSorting.RationalLift
