import BivariateRowEquality
import Horner5Base
import Horner5Node053
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p54 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 338888447), (Int.negSucc 2508614495), (Int.ofNat 13699118304), (Int.ofNat 13931997408), (Int.negSucc 9548348255), (Int.negSucc 7611501311)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1628437248), (Int.ofNat 9952360848), (Int.negSucc 71120284127), (Int.negSucc 41920723871), (Int.ofNat 37296693792), (Int.ofNat 9683931600), (Int.negSucc 2114305919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3108640319), (Int.negSucc 14641799039), (Int.ofNat 143742227616), (Int.ofNat 53401092768), (Int.negSucc 26763819839), (Int.ofNat 452195712), (Int.negSucc 3735803519)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2903946336), (Int.ofNat 8542715760), (Int.negSucc 142651998719), (Int.negSucc 67370624927), (Int.negSucc 32365226879), (Int.ofNat 7123668912), (Int.ofNat 4722413184)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1234612223), (Int.ofNat 571318560), (Int.ofNat 70065199296), (Int.ofNat 92340344160), (Int.ofNat 48771281088), (Int.negSucc 6228531935), (Int.ofNat 1677537216)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 56660544), (Int.negSucc 3163236047), (Int.negSucc 13630248863), (Int.negSucc 74078657567), (Int.negSucc 26491371839), (Int.negSucc 9241011359), (Int.negSucc 1700258687)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 119527488), (Int.ofNat 1511201664), (Int.negSucc 69402527), (Int.ofNat 26543103840), (Int.ofNat 14963634144), (Int.ofNat 8246002176), (Int.ofNat 156422016)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26430623), (Int.negSucc 278363951), (Int.negSucc 166935167), (Int.negSucc 2564107487), (Int.negSucc 7473762431), (Int.negSucc 1520176895)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14416704), (Int.ofNat 132324192), (Int.negSucc 279313919), (Int.ofNat 1363754880)]]

theorem h5n54_arithmetic_row0 :
    (BiPoly.mul h5p3 h5p53).getD 0 []=h5p54.getD 0 [] := by
  decide +kernel

theorem h5n54_arithmetic_row1 :
    (BiPoly.mul h5p3 h5p53).getD 1 []=h5p54.getD 1 [] := by
  decide +kernel

theorem h5n54_arithmetic_row2 :
    (BiPoly.mul h5p3 h5p53).getD 2 []=h5p54.getD 2 [] := by
  decide +kernel

theorem h5n54_arithmetic_row3 :
    (BiPoly.mul h5p3 h5p53).getD 3 []=h5p54.getD 3 [] := by
  decide +kernel

theorem h5n54_arithmetic_row4 :
    (BiPoly.mul h5p3 h5p53).getD 4 []=h5p54.getD 4 [] := by
  decide +kernel

theorem h5n54_arithmetic_row5 :
    (BiPoly.mul h5p3 h5p53).getD 5 []=h5p54.getD 5 [] := by
  decide +kernel

theorem h5n54_arithmetic_row6 :
    (BiPoly.mul h5p3 h5p53).getD 6 []=h5p54.getD 6 [] := by
  decide +kernel

theorem h5n54_arithmetic_row7 :
    (BiPoly.mul h5p3 h5p53).getD 7 []=h5p54.getD 7 [] := by
  decide +kernel

theorem h5n54_arithmetic_row8 :
    (BiPoly.mul h5p3 h5p53).getD 8 []=h5p54.getD 8 [] := by
  decide +kernel

theorem h5n54_arithmetic : BiPoly.mul h5p3 h5p53=h5p54 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<9 at hk
    have hf : ∀ j : Fin 9, (BiPoly.mul h5p3 h5p53).getD j.val []=h5p54.getD j.val [] :=
      (fun j => Fin.cases h5n54_arithmetic_row0 (fun j => Fin.cases h5n54_arithmetic_row1 (fun j => Fin.cases h5n54_arithmetic_row2 (fun j => Fin.cases h5n54_arithmetic_row3 (fun j => Fin.cases h5n54_arithmetic_row4 (fun j => Fin.cases h5n54_arithmetic_row5 (fun j => Fin.cases h5n54_arithmetic_row6 (fun j => Fin.cases h5n54_arithmetic_row7 (fun j => Fin.cases h5n54_arithmetic_row8 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n54 : h5e54.toBi mapPolyEnv=h5p54 := by
  change BiPoly.mul (h5e3.toBi mapPolyEnv) (h5e53.toBi mapPolyEnv)=h5p54
  rw [h5n3, h5n53]
  exact h5n54_arithmetic

#print axioms h5n54_arithmetic
end StackSorting.RationalLift
