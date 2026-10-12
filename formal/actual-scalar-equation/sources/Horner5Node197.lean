import BivariateRowEquality
import Horner5Base
import Horner5Node196
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p197 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 417927168), (Int.negSucc 45953855), (Int.ofNat 3899552832), (Int.ofNat 2015406144), (Int.negSucc 7422361919), (Int.negSucc 5074334207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1966237439), (Int.ofNat 674513376), (Int.negSucc 25334873663), (Int.negSucc 13886675903), (Int.ofNat 25427583168), (Int.ofNat 12448032864), (Int.negSucc 1409537279)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3812387712), (Int.negSucc 138175871), (Int.ofNat 64967584320), (Int.ofNat 32518367040), (Int.negSucc 30106331903), (Int.negSucc 11699113727), (Int.negSucc 726355967)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3947419583), (Int.negSucc 4599139679), (Int.negSucc 83097967103), (Int.negSucc 46060485311), (Int.negSucc 2105042303), (Int.ofNat 5268936480), (Int.ofNat 5761312128)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2379019776), (Int.ofNat 8968942272), (Int.ofNat 56568269184), (Int.ofNat 53553624384), (Int.ofNat 34574234112), (Int.negSucc 1234478015), (Int.negSucc 3739416191)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 859327871), (Int.negSucc 7034224223), (Int.negSucc 21269034431), (Int.negSucc 44149461695), (Int.negSucc 29909030399), (Int.negSucc 4564175039), (Int.negSucc 1804170239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 181270656), (Int.ofNat 2533267584), (Int.ofNat 5337229248), (Int.ofNat 19591015104), (Int.ofNat 12963087936), (Int.ofNat 6860809728), (Int.ofNat 1979479296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17620415), (Int.negSucc 368840735), (Int.negSucc 1239598079), (Int.negSucc 3720734783), (Int.negSucc 4151720447), (Int.negSucc 2888649215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9611136), (Int.ofNat 168837696), (Int.ofNat 165390336), (Int.ofNat 909169920)]]

theorem h5n197_arithmetic_row0 :
    (BiPoly.mul h5p4 h5p196).getD 0 []=h5p197.getD 0 [] := by
  decide +kernel

theorem h5n197_arithmetic_row1 :
    (BiPoly.mul h5p4 h5p196).getD 1 []=h5p197.getD 1 [] := by
  decide +kernel

theorem h5n197_arithmetic_row2 :
    (BiPoly.mul h5p4 h5p196).getD 2 []=h5p197.getD 2 [] := by
  decide +kernel

theorem h5n197_arithmetic_row3 :
    (BiPoly.mul h5p4 h5p196).getD 3 []=h5p197.getD 3 [] := by
  decide +kernel

theorem h5n197_arithmetic_row4 :
    (BiPoly.mul h5p4 h5p196).getD 4 []=h5p197.getD 4 [] := by
  decide +kernel

theorem h5n197_arithmetic_row5 :
    (BiPoly.mul h5p4 h5p196).getD 5 []=h5p197.getD 5 [] := by
  decide +kernel

theorem h5n197_arithmetic_row6 :
    (BiPoly.mul h5p4 h5p196).getD 6 []=h5p197.getD 6 [] := by
  decide +kernel

theorem h5n197_arithmetic_row7 :
    (BiPoly.mul h5p4 h5p196).getD 7 []=h5p197.getD 7 [] := by
  decide +kernel

theorem h5n197_arithmetic_row8 :
    (BiPoly.mul h5p4 h5p196).getD 8 []=h5p197.getD 8 [] := by
  decide +kernel

theorem h5n197_arithmetic : BiPoly.mul h5p4 h5p196=h5p197 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<9 at hk
    have hf : ∀ j : Fin 9, (BiPoly.mul h5p4 h5p196).getD j.val []=h5p197.getD j.val [] :=
      (fun j => Fin.cases h5n197_arithmetic_row0 (fun j => Fin.cases h5n197_arithmetic_row1 (fun j => Fin.cases h5n197_arithmetic_row2 (fun j => Fin.cases h5n197_arithmetic_row3 (fun j => Fin.cases h5n197_arithmetic_row4 (fun j => Fin.cases h5n197_arithmetic_row5 (fun j => Fin.cases h5n197_arithmetic_row6 (fun j => Fin.cases h5n197_arithmetic_row7 (fun j => Fin.cases h5n197_arithmetic_row8 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n197 : h5e197.toBi mapPolyEnv=h5p197 := by
  change BiPoly.mul (h5e4.toBi mapPolyEnv) (h5e196.toBi mapPolyEnv)=h5p197
  rw [h5n4, h5n196]
  exact h5n197_arithmetic

#print axioms h5n197_arithmetic
end StackSorting.RationalLift
