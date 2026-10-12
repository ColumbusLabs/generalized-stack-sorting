import BivariateRowEquality
import Horner5Base
import Horner5Node390
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p391 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3226068000), (Int.ofNat 12854836080), (Int.negSucc 1923082559), (Int.negSucc 11551850639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17263048319), (Int.negSucc 61987460543), (Int.ofNat 23487995520), (Int.ofNat 45053214336), (Int.negSucc 5204642687)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 38831105160), (Int.ofNat 129299799852), (Int.negSucc 48562338275), (Int.negSucc 57343150331), (Int.ofNat 1387939356), (Int.negSucc 552711743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 47498474519), (Int.negSucc 154219712507), (Int.ofNat 1038057984), (Int.ofNat 30981102300), (Int.ofNat 29597941440), (Int.negSucc 1995509879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34059312480), (Int.ofNat 116299447584), (Int.ofNat 101350476060), (Int.negSucc 7813784807), (Int.negSucc 36662384879), (Int.ofNat 1733555532)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14299845119), (Int.negSucc 56803736639), (Int.negSucc 136365546875), (Int.negSucc 17578813691), (Int.ofNat 5242566228), (Int.ofNat 6445013424)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3255939000), (Int.ofNat 17207517300), (Int.ofNat 83205732840), (Int.ofNat 44535116964), (Int.ofNat 11270450496), (Int.negSucc 5297091983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 311056679), (Int.negSucc 2828316419), (Int.negSucc 25540686491), (Int.negSucc 38876592311), (Int.negSucc 9005002919), (Int.negSucc 1747450295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 177625296), (Int.ofNat 3385350576), (Int.ofNat 14715047376), (Int.ofNat 6056143344), (Int.ofNat 2224249056)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 75958775), (Int.negSucc 2110611527), (Int.negSucc 2687775551), (Int.negSucc 437358959)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26167536), (Int.ofNat 437358960)]]

theorem h5n391_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p390).getD 0 []=h5p391.getD 0 [] := by
  decide +kernel

theorem h5n391_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p390).getD 1 []=h5p391.getD 1 [] := by
  decide +kernel

theorem h5n391_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p390).getD 2 []=h5p391.getD 2 [] := by
  decide +kernel

theorem h5n391_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p390).getD 3 []=h5p391.getD 3 [] := by
  decide +kernel

theorem h5n391_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p390).getD 4 []=h5p391.getD 4 [] := by
  decide +kernel

theorem h5n391_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p390).getD 5 []=h5p391.getD 5 [] := by
  decide +kernel

theorem h5n391_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p390).getD 6 []=h5p391.getD 6 [] := by
  decide +kernel

theorem h5n391_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p390).getD 7 []=h5p391.getD 7 [] := by
  decide +kernel

theorem h5n391_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p390).getD 8 []=h5p391.getD 8 [] := by
  decide +kernel

theorem h5n391_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p390).getD 9 []=h5p391.getD 9 [] := by
  decide +kernel

theorem h5n391_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p390).getD 10 []=h5p391.getD 10 [] := by
  decide +kernel

theorem h5n391_arithmetic : BiPoly.mul h5p6 h5p390=h5p391 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p390).getD j.val []=h5p391.getD j.val [] :=
      (fun j => Fin.cases h5n391_arithmetic_row0 (fun j => Fin.cases h5n391_arithmetic_row1 (fun j => Fin.cases h5n391_arithmetic_row2 (fun j => Fin.cases h5n391_arithmetic_row3 (fun j => Fin.cases h5n391_arithmetic_row4 (fun j => Fin.cases h5n391_arithmetic_row5 (fun j => Fin.cases h5n391_arithmetic_row6 (fun j => Fin.cases h5n391_arithmetic_row7 (fun j => Fin.cases h5n391_arithmetic_row8 (fun j => Fin.cases h5n391_arithmetic_row9 (fun j => Fin.cases h5n391_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n391 : h5e391.toBi mapPolyEnv=h5p391 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e390.toBi mapPolyEnv)=h5p391
  rw [h5n6, h5n390]
  exact h5n391_arithmetic

#print axioms h5n391_arithmetic
end StackSorting.RationalLift
