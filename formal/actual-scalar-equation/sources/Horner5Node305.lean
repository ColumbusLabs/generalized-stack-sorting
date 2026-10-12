import BivariateRowEquality
import Horner5Base
import Horner5Node304
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p305 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11334272111), (Int.negSucc 40542648335), (Int.ofNat 29595314736), (Int.ofNat 58803690960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 66685009248), (Int.ofNat 245445493680), (Int.negSucc 155887323263), (Int.negSucc 241866922895), (Int.ofNat 16103089728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 183031960223), (Int.negSucc 583599705695), (Int.ofNat 356616058176), (Int.ofNat 374757672624), (Int.negSucc 2899109327), (Int.negSucc 81723839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 305746052856), (Int.ofNat 674157437664), (Int.negSucc 289482477455), (Int.negSucc 190905055439), (Int.negSucc 93810507431), (Int.ofNat 2965374432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 334496624159), (Int.negSucc 367150714127), (Int.negSucc 208942665215), (Int.negSucc 55758230063), (Int.ofNat 145534731840), (Int.ofNat 4966855728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 240547044912), (Int.ofNat 70079708424), (Int.ofNat 530203426224), (Int.ofNat 100211828640), (Int.negSucc 28027244639), (Int.negSucc 9057171959)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 109913827487), (Int.negSucc 22702610591), (Int.negSucc 333113539631), (Int.negSucc 109166024735), (Int.negSucc 61528582559), (Int.negSucc 2183766479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 29698187736), (Int.ofNat 46966961328), (Int.ofNat 69219429408), (Int.ofNat 92501909328), (Int.ofNat 40294288224), (Int.ofNat 5993415504)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4084172399), (Int.negSucc 29823584927), (Int.ofNat 4808171952), (Int.negSucc 31628105423), (Int.negSucc 11178417743), (Int.negSucc 1713353471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 184561632), (Int.ofNat 8052741432), (Int.negSucc 3631034879), (Int.ofNat 2918184624), (Int.ofNat 1713353472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 883078847), (Int.ofNat 553464144)]]

theorem h5n305_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p304).getD 0 []=h5p305.getD 0 [] := by
  decide +kernel

theorem h5n305_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p304).getD 1 []=h5p305.getD 1 [] := by
  decide +kernel

theorem h5n305_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p304).getD 2 []=h5p305.getD 2 [] := by
  decide +kernel

theorem h5n305_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p304).getD 3 []=h5p305.getD 3 [] := by
  decide +kernel

theorem h5n305_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p304).getD 4 []=h5p305.getD 4 [] := by
  decide +kernel

theorem h5n305_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p304).getD 5 []=h5p305.getD 5 [] := by
  decide +kernel

theorem h5n305_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p304).getD 6 []=h5p305.getD 6 [] := by
  decide +kernel

theorem h5n305_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p304).getD 7 []=h5p305.getD 7 [] := by
  decide +kernel

theorem h5n305_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p304).getD 8 []=h5p305.getD 8 [] := by
  decide +kernel

theorem h5n305_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p304).getD 9 []=h5p305.getD 9 [] := by
  decide +kernel

theorem h5n305_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p304).getD 10 []=h5p305.getD 10 [] := by
  decide +kernel

theorem h5n305_arithmetic : BiPoly.mul h5p22 h5p304=h5p305 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p22 h5p304).getD j.val []=h5p305.getD j.val [] :=
      (fun j => Fin.cases h5n305_arithmetic_row0 (fun j => Fin.cases h5n305_arithmetic_row1 (fun j => Fin.cases h5n305_arithmetic_row2 (fun j => Fin.cases h5n305_arithmetic_row3 (fun j => Fin.cases h5n305_arithmetic_row4 (fun j => Fin.cases h5n305_arithmetic_row5 (fun j => Fin.cases h5n305_arithmetic_row6 (fun j => Fin.cases h5n305_arithmetic_row7 (fun j => Fin.cases h5n305_arithmetic_row8 (fun j => Fin.cases h5n305_arithmetic_row9 (fun j => Fin.cases h5n305_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n305 : h5e305.toBi mapPolyEnv=h5p305 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e304.toBi mapPolyEnv)=h5p305
  rw [h5n22, h5n304]
  exact h5n305_arithmetic

#print axioms h5n305_arithmetic
end StackSorting.RationalLift
