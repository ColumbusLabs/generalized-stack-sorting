import BivariateRowEquality
import Horner4Base
import Horner4Node071
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p181 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4250352042), (Int.ofNat 10953141084), (Int.negSucc 22051384109)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 20756526425), (Int.negSucc 60332392619), (Int.ofNat 96738754734), (Int.negSucc 6038658647)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 47880458658), (Int.ofNat 110637038358), (Int.negSucc 147629305439), (Int.ofNat 1056519558), (Int.ofNat 30646440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 66774311162), (Int.negSucc 75397689602), (Int.ofNat 36324313209), (Int.ofNat 36321602139), (Int.negSucc 1112015411)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 58661922897), (Int.ofNat 3621905298), (Int.ofNat 111055907367), (Int.negSucc 53824968953), (Int.negSucc 1862570897)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 31543218944), (Int.ofNat 8885233584), (Int.negSucc 96655611050), (Int.ofNat 5251206357), (Int.ofNat 3396439485)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9674466363), (Int.ofNat 7724246193), (Int.ofNat 20537720118), (Int.ofNat 25650745515), (Int.ofNat 818912430)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1462354037), (Int.negSucc 8426010266), (Int.ofNat 3006444357), (Int.negSucc 12043914839), (Int.negSucc 2247530813)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 69210612), (Int.ofNat 2688623469), (Int.negSucc 1485243593), (Int.ofNat 1301868288), (Int.ofNat 642507552)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 331154567), (Int.ofNat 207549054)]]

theorem h4n181_arithmetic_row0 :
    (BiPoly.mul h4p180 h4p71).getD 0 []=h4p181.getD 0 [] := by
  decide +kernel

theorem h4n181_arithmetic_row1 :
    (BiPoly.mul h4p180 h4p71).getD 1 []=h4p181.getD 1 [] := by
  decide +kernel

theorem h4n181_arithmetic_row2 :
    (BiPoly.mul h4p180 h4p71).getD 2 []=h4p181.getD 2 [] := by
  decide +kernel

theorem h4n181_arithmetic_row3 :
    (BiPoly.mul h4p180 h4p71).getD 3 []=h4p181.getD 3 [] := by
  decide +kernel

theorem h4n181_arithmetic_row4 :
    (BiPoly.mul h4p180 h4p71).getD 4 []=h4p181.getD 4 [] := by
  decide +kernel

theorem h4n181_arithmetic_row5 :
    (BiPoly.mul h4p180 h4p71).getD 5 []=h4p181.getD 5 [] := by
  decide +kernel

theorem h4n181_arithmetic_row6 :
    (BiPoly.mul h4p180 h4p71).getD 6 []=h4p181.getD 6 [] := by
  decide +kernel

theorem h4n181_arithmetic_row7 :
    (BiPoly.mul h4p180 h4p71).getD 7 []=h4p181.getD 7 [] := by
  decide +kernel

theorem h4n181_arithmetic_row8 :
    (BiPoly.mul h4p180 h4p71).getD 8 []=h4p181.getD 8 [] := by
  decide +kernel

theorem h4n181_arithmetic_row9 :
    (BiPoly.mul h4p180 h4p71).getD 9 []=h4p181.getD 9 [] := by
  decide +kernel

theorem h4n181_arithmetic : BiPoly.mul h4p180 h4p71=h4p181 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p180 h4p71).getD j.val []=h4p181.getD j.val [] :=
      (fun j => Fin.cases h4n181_arithmetic_row0 (fun j => Fin.cases h4n181_arithmetic_row1 (fun j => Fin.cases h4n181_arithmetic_row2 (fun j => Fin.cases h4n181_arithmetic_row3 (fun j => Fin.cases h4n181_arithmetic_row4 (fun j => Fin.cases h4n181_arithmetic_row5 (fun j => Fin.cases h4n181_arithmetic_row6 (fun j => Fin.cases h4n181_arithmetic_row7 (fun j => Fin.cases h4n181_arithmetic_row8 (fun j => Fin.cases h4n181_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n181 : h4e181.toBi mapPolyEnv=h4p181 := by
  change BiPoly.mul (h4e180.toBi mapPolyEnv) (h4e71.toBi mapPolyEnv)=h4p181
  rw [h4n180, h4n71]
  exact h4n181_arithmetic

#print axioms h4n181_arithmetic
end StackSorting.RationalLift
