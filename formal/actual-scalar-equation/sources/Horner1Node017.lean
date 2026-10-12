import BivariateRowEquality
import Horner1Base
import Horner1Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p17 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 1858215167999), (Int.negSucc 8449631614079), (Int.ofNat 9950234840640), (Int.ofNat 46100137616640), (Int.negSucc 42834262173119)], [(Int.ofNat 0), (Int.ofNat 14105143552320), (Int.ofNat 53719115752224), (Int.negSucc 100153446331103), (Int.negSucc 289290998595743), (Int.ofNat 328671731845152), (Int.negSucc 33161035855103)], [(Int.ofNat 0), (Int.negSucc 47500797288959), (Int.negSucc 147205532090591), (Int.ofNat 386630247275568), (Int.ofNat 764151761073168), (Int.negSucc 900549910651823), (Int.ofNat 87008725122192), (Int.negSucc 8849515203071)], [(Int.ofNat 0), (Int.ofNat 93342169720080), (Int.ofNat 225429788917800), (Int.negSucc 799214551093583), (Int.negSucc 1160866518222095), (Int.ofNat 956408815019232), (Int.ofNat 263575647034344), (Int.negSucc 24676204985567), (Int.negSucc 913076941823)], [(Int.ofNat 0), (Int.negSucc 118376987909039), (Int.negSucc 206763293775095), (Int.ofNat 1006487689492944), (Int.ofNat 1257178437421920), (Int.ofNat 230545184356656), (Int.negSucc 1250603325814679), (Int.ofNat 149742130861440), (Int.negSucc 9003587455295), (Int.negSucc 26530163711)], [(Int.ofNat 0), (Int.ofNat 101108481559920), (Int.ofNat 108261689917032), (Int.negSucc 828289715364431), (Int.negSucc 1237876221344255), (Int.negSucc 1639181056589423), (Int.ofNat 1593468003072888), (Int.ofNat 25481682907200), (Int.negSucc 1716512831711), (Int.negSucc 613122666623)], [(Int.ofNat 0), (Int.negSucc 58831625117519), (Int.negSucc 19840724297063), (Int.ofNat 477572069326680), (Int.ofNat 1208111322357936), (Int.ofNat 1845624018760704), (Int.negSucc 252557813664791), (Int.negSucc 691351199980199), (Int.ofNat 71683426904112), (Int.negSucc 2421310511231)], [(Int.ofNat 0), (Int.ofNat 23003912795760), (Int.negSucc 13028920063703), (Int.negSucc 218783415343175), (Int.negSucc 1008310551955847), (Int.negSucc 1175613403451471), (Int.negSucc 1237856326000991), (Int.ofNat 858865217177016), (Int.negSucc 17135186350679), (Int.ofNat 826998607584)], [(Int.ofNat 0), (Int.negSucc 5780710000079), (Int.ofNat 11091278748024), (Int.ofNat 93547903740336), (Int.ofNat 630496009759536), (Int.ofNat 653885202990528), (Int.ofNat 1273857570881424), (Int.negSucc 81374912255951), (Int.negSucc 190659332462543), (Int.ofNat 12085629463296)], [(Int.ofNat 0), (Int.ofNat 842751717840), (Int.negSucc 3854656882439), (Int.negSucc 36743569100927), (Int.negSucc 279961553672639), (Int.negSucc 430638230337407), (Int.negSucc 553758006206447), (Int.negSucc 518800353779519), (Int.ofNat 186306626500272), (Int.negSucc 1361780195903)], [(Int.ofNat 0), (Int.negSucc 54123862319), (Int.ofNat 693963889992), (Int.ofNat 10702795155912), (Int.ofNat 85139446552992), (Int.ofNat 248657449666896), (Int.ofNat 151442329271184), (Int.ofNat 382723591594896), (Int.ofNat 22664161579248), (Int.negSucc 21552328483775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 53078502095), (Int.negSucc 1841766966071), (Int.negSucc 16587779980823), (Int.negSucc 92155196661839), (Int.negSucc 68148629411903), (Int.negSucc 98575534818863), (Int.negSucc 98066396997791), (Int.ofNat 11489559830784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 135524367216), (Int.ofNat 1790015303376), (Int.ofNat 18876720264336), (Int.ofNat 34716810025872), (Int.ofNat 8416723203648), (Int.ofNat 41198013578304), (Int.ofNat 5927459565312)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 73506314159), (Int.negSucc 1730889628559), (Int.negSucc 8852615781983), (Int.negSucc 3076533399743), (Int.negSucc 4149750191039), (Int.negSucc 5308215482879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 31675878144), (Int.ofNat 836780212224), (Int.ofNat 1419488286912), (Int.negSucc 368591031359), (Int.ofNat 944695353600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8478281663), (Int.negSucc 141704303039)]]

theorem h1n17_arithmetic_row0 :
    (BiPoly.mul h1p14 h1p16).getD 0 []=h1p17.getD 0 [] := by
  decide +kernel

theorem h1n17_arithmetic_row1 :
    (BiPoly.mul h1p14 h1p16).getD 1 []=h1p17.getD 1 [] := by
  decide +kernel

theorem h1n17_arithmetic_row2 :
    (BiPoly.mul h1p14 h1p16).getD 2 []=h1p17.getD 2 [] := by
  decide +kernel

theorem h1n17_arithmetic_row3 :
    (BiPoly.mul h1p14 h1p16).getD 3 []=h1p17.getD 3 [] := by
  decide +kernel

theorem h1n17_arithmetic_row4 :
    (BiPoly.mul h1p14 h1p16).getD 4 []=h1p17.getD 4 [] := by
  decide +kernel

theorem h1n17_arithmetic_row5 :
    (BiPoly.mul h1p14 h1p16).getD 5 []=h1p17.getD 5 [] := by
  decide +kernel

theorem h1n17_arithmetic_row6 :
    (BiPoly.mul h1p14 h1p16).getD 6 []=h1p17.getD 6 [] := by
  decide +kernel

theorem h1n17_arithmetic_row7 :
    (BiPoly.mul h1p14 h1p16).getD 7 []=h1p17.getD 7 [] := by
  decide +kernel

theorem h1n17_arithmetic_row8 :
    (BiPoly.mul h1p14 h1p16).getD 8 []=h1p17.getD 8 [] := by
  decide +kernel

theorem h1n17_arithmetic_row9 :
    (BiPoly.mul h1p14 h1p16).getD 9 []=h1p17.getD 9 [] := by
  decide +kernel

theorem h1n17_arithmetic_row10 :
    (BiPoly.mul h1p14 h1p16).getD 10 []=h1p17.getD 10 [] := by
  decide +kernel

theorem h1n17_arithmetic_row11 :
    (BiPoly.mul h1p14 h1p16).getD 11 []=h1p17.getD 11 [] := by
  decide +kernel

theorem h1n17_arithmetic_row12 :
    (BiPoly.mul h1p14 h1p16).getD 12 []=h1p17.getD 12 [] := by
  decide +kernel

theorem h1n17_arithmetic_row13 :
    (BiPoly.mul h1p14 h1p16).getD 13 []=h1p17.getD 13 [] := by
  decide +kernel

theorem h1n17_arithmetic_row14 :
    (BiPoly.mul h1p14 h1p16).getD 14 []=h1p17.getD 14 [] := by
  decide +kernel

theorem h1n17_arithmetic_row15 :
    (BiPoly.mul h1p14 h1p16).getD 15 []=h1p17.getD 15 [] := by
  decide +kernel

theorem h1n17_arithmetic : BiPoly.mul h1p14 h1p16=h1p17 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p14 h1p16).getD j.val []=h1p17.getD j.val [] :=
      (fun j => Fin.cases h1n17_arithmetic_row0 (fun j => Fin.cases h1n17_arithmetic_row1 (fun j => Fin.cases h1n17_arithmetic_row2 (fun j => Fin.cases h1n17_arithmetic_row3 (fun j => Fin.cases h1n17_arithmetic_row4 (fun j => Fin.cases h1n17_arithmetic_row5 (fun j => Fin.cases h1n17_arithmetic_row6 (fun j => Fin.cases h1n17_arithmetic_row7 (fun j => Fin.cases h1n17_arithmetic_row8 (fun j => Fin.cases h1n17_arithmetic_row9 (fun j => Fin.cases h1n17_arithmetic_row10 (fun j => Fin.cases h1n17_arithmetic_row11 (fun j => Fin.cases h1n17_arithmetic_row12 (fun j => Fin.cases h1n17_arithmetic_row13 (fun j => Fin.cases h1n17_arithmetic_row14 (fun j => Fin.cases h1n17_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n17 : h1e17.toBi mapPolyEnv=h1p17 := by
  change BiPoly.mul (h1e14.toBi mapPolyEnv) (h1e16.toBi mapPolyEnv)=h1p17
  rw [h1n14, h1n16]
  exact h1n17_arithmetic

#print axioms h1n17_arithmetic
end StackSorting.RationalLift
