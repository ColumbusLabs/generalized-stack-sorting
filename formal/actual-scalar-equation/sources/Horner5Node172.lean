import BivariateRowEquality
import Horner5Base
import Horner5Node171
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p172 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 3226068000), (Int.ofNat 16080904080), (Int.ofNat 17383889520), (Int.ofNat 5782602960), (Int.negSucc 34655551919)], [(Int.ofNat 0), (Int.negSucc 17263048319), (Int.negSucc 79250508863), (Int.negSucc 66573425663), (Int.negSucc 8102214431), (Int.ofNat 140364285696), (Int.negSucc 15613928063)], [(Int.ofNat 0), (Int.ofNat 38831105160), (Int.ofNat 168130905012), (Int.ofNat 130325711256), (Int.ofNat 26462437128), (Int.negSucc 184932099215), (Int.ofNat 4716529812), (Int.negSucc 1658135231)], [(Int.ofNat 0), (Int.negSucc 47498474519), (Int.negSucc 201718187027), (Int.negSucc 198590353883), (Int.negSucc 98643639635), (Int.ofNat 64341071388), (Int.ofNat 89683910712), (Int.negSucc 5986529639)], [(Int.ofNat 0), (Int.ofNat 34059312480), (Int.ofNat 150358760064), (Int.ofNat 240359849244), (Int.ofNat 172762860900), (Int.ofNat 82760640432), (Int.negSucc 115711729931), (Int.ofNat 5200666596)], [(Int.ofNat 0), (Int.negSucc 14299845119), (Int.negSucc 71103581759), (Int.negSucc 199059048155), (Int.negSucc 182435899559), (Int.negSucc 129338992103), (Int.ofNat 12749796324), (Int.ofNat 19335040272)], [(Int.ofNat 0), (Int.ofNat 3255939000), (Int.ofNat 20463456300), (Int.ofNat 101035363500), (Int.ofNat 133042232052), (Int.ofNat 99912906252), (Int.ofNat 51998470320), (Int.negSucc 15891275951)], [(Int.ofNat 0), (Int.negSucc 311056679), (Int.negSucc 3139373099), (Int.negSucc 28369002911), (Int.negSucc 64772529395), (Int.negSucc 54500378831), (Int.negSucc 35861742431), (Int.negSucc 5242350887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 177625296), (Int.ofNat 3562975872), (Int.ofNat 18100397952), (Int.ofNat 20923108272), (Int.ofNat 12449280384), (Int.ofNat 6672747168)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 75958775), (Int.negSucc 2186570303), (Int.negSucc 4798387079), (Int.negSucc 3177469583), (Int.negSucc 1312076879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26167536), (Int.ofNat 463526496), (Int.ofNat 437358960)]]

theorem h5n172_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p171).getD 0 []=h5p172.getD 0 [] := by
  decide +kernel

theorem h5n172_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p171).getD 1 []=h5p172.getD 1 [] := by
  decide +kernel

theorem h5n172_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p171).getD 2 []=h5p172.getD 2 [] := by
  decide +kernel

theorem h5n172_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p171).getD 3 []=h5p172.getD 3 [] := by
  decide +kernel

theorem h5n172_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p171).getD 4 []=h5p172.getD 4 [] := by
  decide +kernel

theorem h5n172_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p171).getD 5 []=h5p172.getD 5 [] := by
  decide +kernel

theorem h5n172_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p171).getD 6 []=h5p172.getD 6 [] := by
  decide +kernel

theorem h5n172_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p171).getD 7 []=h5p172.getD 7 [] := by
  decide +kernel

theorem h5n172_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p171).getD 8 []=h5p172.getD 8 [] := by
  decide +kernel

theorem h5n172_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p171).getD 9 []=h5p172.getD 9 [] := by
  decide +kernel

theorem h5n172_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p171).getD 10 []=h5p172.getD 10 [] := by
  decide +kernel

theorem h5n172_arithmetic : BiPoly.mul h5p6 h5p171=h5p172 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p171).getD j.val []=h5p172.getD j.val [] :=
      (fun j => Fin.cases h5n172_arithmetic_row0 (fun j => Fin.cases h5n172_arithmetic_row1 (fun j => Fin.cases h5n172_arithmetic_row2 (fun j => Fin.cases h5n172_arithmetic_row3 (fun j => Fin.cases h5n172_arithmetic_row4 (fun j => Fin.cases h5n172_arithmetic_row5 (fun j => Fin.cases h5n172_arithmetic_row6 (fun j => Fin.cases h5n172_arithmetic_row7 (fun j => Fin.cases h5n172_arithmetic_row8 (fun j => Fin.cases h5n172_arithmetic_row9 (fun j => Fin.cases h5n172_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n172 : h5e172.toBi mapPolyEnv=h5p172 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e171.toBi mapPolyEnv)=h5p172
  rw [h5n6, h5n171]
  exact h5n172_arithmetic

#print axioms h5n172_arithmetic
end StackSorting.RationalLift
