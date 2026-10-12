import BivariateRowEquality
import Horner5Base
import Horner5Node399
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p400 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 2150711999), (Int.negSucc 8569890719), (Int.negSucc 3019368959), (Int.negSucc 5137123679), (Int.ofNat 15402467520)], [(Int.ofNat 0), (Int.ofNat 11508698880), (Int.ofNat 41324973696), (Int.ofNat 3057310080), (Int.ofNat 21060139968), (Int.negSucc 63540714239), (Int.ofNat 6939523584)], [(Int.ofNat 0), (Int.negSucc 25887403439), (Int.negSucc 86199866567), (Int.negSucc 683940935), (Int.negSucc 50016516935), (Int.ofNat 85059299256), (Int.negSucc 2219060303), (Int.ofNat 736948992)], [(Int.ofNat 0), (Int.ofNat 31665649680), (Int.ofNat 102813141672), (Int.ofNat 29580427584), (Int.ofNat 66454465080), (Int.negSucc 22239979391), (Int.negSucc 40057312847), (Int.ofNat 2660679840)], [(Int.ofNat 0), (Int.negSucc 22706208319), (Int.negSucc 77532965055), (Int.negSucc 82706934439), (Int.negSucc 47608256559), (Int.negSucc 60382950159), (Int.ofNat 52699563368), (Int.negSucc 2311407375)], [(Int.ofNat 0), (Int.ofNat 9533230080), (Int.ofNat 37869157760), (Int.ofNat 94836874344), (Int.ofNat 30713568456), (Int.ofNat 74506785608), (Int.negSucc 5004820063), (Int.negSucc 8593351231)], [(Int.ofNat 0), (Int.negSucc 2170625999), (Int.negSucc 11471678199), (Int.negSucc 55885230799), (Int.negSucc 33224332807), (Int.negSucc 36918526191), (Int.negSucc 27152013215), (Int.ofNat 7062789312)], [(Int.ofNat 0), (Int.ofNat 207371120), (Int.ofNat 1885544280), (Int.ofNat 17027124328), (Int.ofNat 26154561936), (Int.ofNat 10415857680), (Int.ofNat 17904493008), (Int.ofNat 2329933728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 118416863), (Int.negSucc 2256900383), (Int.negSucc 9810031583), (Int.negSucc 4138707263), (Int.negSucc 4262091359), (Int.negSucc 2965665407)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 50639184), (Int.ofNat 1407074352), (Int.ofNat 1791850368), (Int.ofNat 326462688), (Int.ofNat 583145280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17445023), (Int.negSucc 291572639)]]

theorem h5n400_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p399).getD 0 []=h5p400.getD 0 [] := by
  decide +kernel

theorem h5n400_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p399).getD 1 []=h5p400.getD 1 [] := by
  decide +kernel

theorem h5n400_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p399).getD 2 []=h5p400.getD 2 [] := by
  decide +kernel

theorem h5n400_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p399).getD 3 []=h5p400.getD 3 [] := by
  decide +kernel

theorem h5n400_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p399).getD 4 []=h5p400.getD 4 [] := by
  decide +kernel

theorem h5n400_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p399).getD 5 []=h5p400.getD 5 [] := by
  decide +kernel

theorem h5n400_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p399).getD 6 []=h5p400.getD 6 [] := by
  decide +kernel

theorem h5n400_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p399).getD 7 []=h5p400.getD 7 [] := by
  decide +kernel

theorem h5n400_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p399).getD 8 []=h5p400.getD 8 [] := by
  decide +kernel

theorem h5n400_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p399).getD 9 []=h5p400.getD 9 [] := by
  decide +kernel

theorem h5n400_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p399).getD 10 []=h5p400.getD 10 [] := by
  decide +kernel

theorem h5n400_arithmetic : BiPoly.mul h5p6 h5p399=h5p400 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p399).getD j.val []=h5p400.getD j.val [] :=
      (fun j => Fin.cases h5n400_arithmetic_row0 (fun j => Fin.cases h5n400_arithmetic_row1 (fun j => Fin.cases h5n400_arithmetic_row2 (fun j => Fin.cases h5n400_arithmetic_row3 (fun j => Fin.cases h5n400_arithmetic_row4 (fun j => Fin.cases h5n400_arithmetic_row5 (fun j => Fin.cases h5n400_arithmetic_row6 (fun j => Fin.cases h5n400_arithmetic_row7 (fun j => Fin.cases h5n400_arithmetic_row8 (fun j => Fin.cases h5n400_arithmetic_row9 (fun j => Fin.cases h5n400_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n400 : h5e400.toBi mapPolyEnv=h5p400 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e399.toBi mapPolyEnv)=h5p400
  rw [h5n6, h5n399]
  exact h5n400_arithmetic

#print axioms h5n400_arithmetic
end StackSorting.RationalLift
