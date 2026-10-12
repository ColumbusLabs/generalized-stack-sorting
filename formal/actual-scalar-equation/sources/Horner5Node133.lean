import BivariateRowEquality
import Horner5Base
import Horner5Node132
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p133 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1858215167999), (Int.negSucc 10307846782079), (Int.ofNat 1500603226560), (Int.ofNat 56050372457280), (Int.ofNat 3265875443520), (Int.negSucc 42834262173119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15963358720320), (Int.ofNat 76273890918624), (Int.negSucc 56384565419519), (Int.negSucc 435544582543487), (Int.ofNat 82214995422528), (Int.ofNat 295510695990048), (Int.negSucc 33161035855103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 61605940841279), (Int.negSucc 248425445131775), (Int.ofNat 339578161516080), (Int.ofNat 1440073006944480), (Int.negSucc 465069881423807), (Int.negSucc 780380149674527), (Int.ofNat 78159209919120), (Int.negSucc 8849515203071)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 140842967009040), (Int.ofNat 465977490728472), (Int.negSucc 960415009451351), (Int.negSucc 2724232830388847), (Int.ofNat 696092207448960), (Int.ofNat 1132975736931384), (Int.ofNat 247748957251848), (Int.negSucc 25589281927391), (Int.negSucc 913076941823)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 211719157629119), (Int.negSucc 550570070601935), (Int.ofNat 1598938946811432), (Int.ofNat 3424532645136960), (Int.ofNat 531314806759344), (Int.negSucc 1283633788492367), (Int.negSucc 1076184989967671), (Int.ofNat 141651620347968), (Int.negSucc 9030117619007), (Int.negSucc 26530163711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 219485469468960), (Int.ofNat 416133465252048), (Int.negSucc 1726515714940343), (Int.negSucc 3323344374130607), (Int.negSucc 3107602462290335), (Int.ofNat 1204890272298144), (Int.ofNat 1469207555118648), (Int.ofNat 32768757530784), (Int.negSucc 2303105334623), (Int.negSucc 613122666623)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 159940106677439), (Int.negSucc 186934039331615), (Int.ofNat 1286021060394048), (Int.ofNat 2923559613028872), (Int.ofNat 4692916397708064), (Int.negSucc 401797976975), (Int.negSucc 969390696552191), (Int.negSucc 617951260244375), (Int.ofNat 69875239059504), (Int.negSucc 2421310511231)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 81835537913280), (Int.ofNat 29815717029120), (Int.negSucc 709384404733559), (Int.negSucc 2435205289656959), (Int.negSucc 4029547974168023), (Int.negSucc 2160911915787671), (Int.ofNat 312360091156224), (Int.ofNat 770046603922224), (Int.negSucc 13886877231863), (Int.ofNat 826998607584)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 28784622795839), (Int.ofNat 18339488811648), (Int.ofNat 323422597831536), (Int.ofNat 1732354465455720), (Int.ofNat 2459994616201536), (Int.ofNat 3165599099872944), (Int.ofNat 333617441448456), (Int.negSucc 254899058367815), (Int.negSucc 179400701606831), (Int.ofNat 12085629463296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6623461717920), (Int.negSucc 14103183912623), (Int.negSucc 134146129723703), (Int.negSucc 947201132533103), (Int.negSucc 1364484987000575), (Int.negSucc 2258253807425279), (Int.negSucc 991183447730015), (Int.negSucc 141834394816703), (Int.ofNat 172859216841072), (Int.negSucc 1361780195903)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 896875580159), (Int.ofNat 4494496910112), (Int.ofNat 48140328146832), (Int.ofNat 375803795381544), (Int.ofNat 764435126557296), (Int.ofNat 953857785144528), (Int.ofNat 1052966274645600), (Int.ofNat 219081126673872), (Int.ofNat 2473613291376), (Int.negSucc 21552328483775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 54123862320), (Int.negSucc 747042392087), (Int.negSucc 12597640624079), (Int.negSucc 103568993499887), (Int.negSucc 357400426309559), (Int.negSucc 311746155344927), (Int.negSucc 549447755825663), (Int.negSucc 219306093395903), (Int.negSucc 65024508683231), (Int.ofNat 11489559830784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 53078502096), (Int.ofNat 1977291333288), (Int.ofNat 18513319651416), (Int.ofNat 112821932229552), (Int.ofNat 121742159702112), (Int.ofNat 141709068048384), (Int.ofNat 147681133779744), (Int.ofNat 35635913312832), (Int.ofNat 5927459565312)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 135524367215), (Int.negSucc 1863521617535), (Int.negSucc 20681116207055), (Int.negSucc 45300315436415), (Int.negSucc 20345872385375), (Int.negSucc 48424297169087), (Int.negSucc 15385425239231), (Int.negSucc 5308215482879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 73506314160), (Int.ofNat 1762565506704), (Int.ofNat 9721071872352), (Int.ofNat 5332801898880), (Int.ofNat 5200647446592), (Int.ofNat 5884319805120), (Int.ofNat 944695353600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 31675878143), (Int.negSucc 845258493887), (Int.negSucc 1569670871615), (Int.ofNat 226886728320), (Int.negSucc 944695353599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8478281664), (Int.ofNat 141704303040)]]

theorem h5n133_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p132).getD 0 []=h5p133.getD 0 [] := by
  decide +kernel

theorem h5n133_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p132).getD 1 []=h5p133.getD 1 [] := by
  decide +kernel

theorem h5n133_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p132).getD 2 []=h5p133.getD 2 [] := by
  decide +kernel

theorem h5n133_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p132).getD 3 []=h5p133.getD 3 [] := by
  decide +kernel

theorem h5n133_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p132).getD 4 []=h5p133.getD 4 [] := by
  decide +kernel

theorem h5n133_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p132).getD 5 []=h5p133.getD 5 [] := by
  decide +kernel

theorem h5n133_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p132).getD 6 []=h5p133.getD 6 [] := by
  decide +kernel

theorem h5n133_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p132).getD 7 []=h5p133.getD 7 [] := by
  decide +kernel

theorem h5n133_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p132).getD 8 []=h5p133.getD 8 [] := by
  decide +kernel

theorem h5n133_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p132).getD 9 []=h5p133.getD 9 [] := by
  decide +kernel

theorem h5n133_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p132).getD 10 []=h5p133.getD 10 [] := by
  decide +kernel

theorem h5n133_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p132).getD 11 []=h5p133.getD 11 [] := by
  decide +kernel

theorem h5n133_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p132).getD 12 []=h5p133.getD 12 [] := by
  decide +kernel

theorem h5n133_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p132).getD 13 []=h5p133.getD 13 [] := by
  decide +kernel

theorem h5n133_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p132).getD 14 []=h5p133.getD 14 [] := by
  decide +kernel

theorem h5n133_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p132).getD 15 []=h5p133.getD 15 [] := by
  decide +kernel

theorem h5n133_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p132).getD 16 []=h5p133.getD 16 [] := by
  decide +kernel

theorem h5n133_arithmetic : BiPoly.mul h5p34 h5p132=h5p133 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p132).getD j.val []=h5p133.getD j.val [] :=
      (fun j => Fin.cases h5n133_arithmetic_row0 (fun j => Fin.cases h5n133_arithmetic_row1 (fun j => Fin.cases h5n133_arithmetic_row2 (fun j => Fin.cases h5n133_arithmetic_row3 (fun j => Fin.cases h5n133_arithmetic_row4 (fun j => Fin.cases h5n133_arithmetic_row5 (fun j => Fin.cases h5n133_arithmetic_row6 (fun j => Fin.cases h5n133_arithmetic_row7 (fun j => Fin.cases h5n133_arithmetic_row8 (fun j => Fin.cases h5n133_arithmetic_row9 (fun j => Fin.cases h5n133_arithmetic_row10 (fun j => Fin.cases h5n133_arithmetic_row11 (fun j => Fin.cases h5n133_arithmetic_row12 (fun j => Fin.cases h5n133_arithmetic_row13 (fun j => Fin.cases h5n133_arithmetic_row14 (fun j => Fin.cases h5n133_arithmetic_row15 (fun j => Fin.cases h5n133_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n133 : h5e133.toBi mapPolyEnv=h5p133 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e132.toBi mapPolyEnv)=h5p133
  rw [h5n34, h5n132]
  exact h5n133_arithmetic

#print axioms h5n133_arithmetic
end StackSorting.RationalLift
