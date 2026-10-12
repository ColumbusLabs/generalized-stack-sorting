import BivariateRowEquality
import Horner4Base
import Horner4Node087
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p88 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 20490551119871), (Int.negSucc 108446693040575), (Int.ofNat 891174564959400), (Int.negSucc 2436697533964895), (Int.ofNat 10673361717275376), (Int.negSucc 4509699608667167), (Int.negSucc 15796923026350679), (Int.ofNat 4007555658868608), (Int.ofNat 5587861904183808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 153883382969088), (Int.ofNat 705839643705792), (Int.negSucc 6347385359542343), (Int.ofNat 20175120415506024), (Int.negSucc 96309471709420655), (Int.ofNat 41644711862732976), (Int.ofNat 102310191306017208), (Int.negSucc 32746267076550743), (Int.negSucc 22808247498409343), (Int.ofNat 3104367724546560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 509858088883839), (Int.negSucc 2066111891734447), (Int.ofNat 19157146387283714), (Int.negSucc 65578422047262171), (Int.ofNat 372114455572414550), (Int.negSucc 153358363743494679), (Int.negSucc 279472821293182657), (Int.ofNat 81998877737265828), (Int.ofNat 31604828494365898), (Int.negSucc 3102404979122591), (Int.ofNat 431162183964800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 978010986625920), (Int.ofNat 3660101231602256), (Int.negSucc 31937227138271027), (Int.ofNat 103338606241197348), (Int.negSucc 803064964608617255), (Int.ofNat 243967993790847672), (Int.ofNat 416771102553691692), (Int.negSucc 30337615595751867), (Int.negSucc 18607959196802351), (Int.negSucc 15176100327896783), (Int.ofNat 984012305463680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1196086888191935), (Int.negSucc 4453640465380119), (Int.ofNat 32157250123215402), (Int.negSucc 63792470281050407), (Int.ofNat 1066711705857903264), (Int.negSucc 10896386331250391), (Int.negSucc 379671901173855797), (Int.negSucc 206229689469179247), (Int.ofNat 18433010291590212), (Int.ofNat 29307600672586008), (Int.negSucc 2332764842532159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 964103210324672), (Int.ofNat 3916972995402480), (Int.negSucc 20452111465452255), (Int.negSucc 43005785561860423), (Int.negSucc 917415214308146711), (Int.negSucc 593781009700951735), (Int.ofNat 203675098355193440), (Int.ofNat 396306952628860808), (Int.negSucc 10430772834076143), (Int.negSucc 7596430308250319), (Int.negSucc 2808386079226175)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 505289771589815), (Int.negSucc 2406642348085183), (Int.ofNat 9321143615813676), (Int.ofNat 114824349909761952), (Int.ofNat 544915195818877964), (Int.ofNat 1039593850735704432), (Int.ofNat 64880964125938266), (Int.negSucc 289476206299455683), (Int.negSucc 63697548933698597), (Int.negSucc 15804503479113095), (Int.ofNat 6679640795766912)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 155601565351248), (Int.ofNat 837117876803488), (Int.negSucc 4768796051660471), (Int.negSucc 100596415171408295), (Int.negSucc 264513581410740423), (Int.negSucc 910665438715927223), (Int.negSucc 357407767900908035), (Int.ofNat 33080195399656788), (Int.ofNat 119130115883928480), (Int.ofNat 11501978749208496), (Int.negSucc 640182537098207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14065093334919), (Int.ofNat 38836248479744), (Int.ofNat 3347441272978124), (Int.ofNat 49602332475416040), (Int.ofNat 132464107763495736), (Int.ofNat 475903611606756024), (Int.ofNat 462546883687122270), (Int.ofNat 119893626823843440), (Int.negSucc 64084725916830575), (Int.negSucc 6415652432959775), (Int.negSucc 4643711218500191)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9495625035743), (Int.negSucc 204256706005103), (Int.negSucc 1981935845660663), (Int.negSucc 15360161477290967), (Int.negSucc 63041378642665703), (Int.negSucc 161576124218408519), (Int.negSucc 318604615401917375), (Int.negSucc 138292389091413863), (Int.negSucc 17705858869209743), (Int.ofNat 8045179155338112), (Int.ofNat 1964775365979264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4482599859000), (Int.ofNat 101474838364752), (Int.ofNat 782655937583202), (Int.ofNat 3415163596037244), (Int.ofNat 21220131522118014), (Int.ofNat 42477856869732696), (Int.ofNat 125215574927028912), (Int.ofNat 93946935818314944), (Int.ofNat 36633095647564104), (Int.negSucc 2063193961946399), (Int.ofNat 839594805138432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 863105242031), (Int.negSucc 23688527833871), (Int.negSucc 196706177802899), (Int.negSucc 706498695102779), (Int.negSucc 4146155992687391), (Int.negSucc 10788666426314495), (Int.negSucc 27493612689011327), (Int.negSucc 41442355185020927), (Int.negSucc 18724317193232351), (Int.negSucc 3733749629370431), (Int.negSucc 527754458461823)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 67378268232), (Int.ofNat 2517301286136), (Int.ofNat 29429313607026), (Int.ofNat 135828252953856), (Int.ofNat 419025101026752), (Int.ofNat 2196217822734432), (Int.ofNat 3359806446018960), (Int.ofNat 10440810031848480), (Int.ofNat 5718866236269120), (Int.ofNat 2479041550144512), (Int.ofNat 44796606208128)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 73503565343), (Int.negSucc 2099223477791), (Int.negSucc 15486272945927), (Int.negSucc 30393607287599), (Int.negSucc 209554907720255), (Int.negSucc 359372150788895), (Int.negSucc 1095022342123199), (Int.negSucc 1371302906249087), (Int.negSucc 411131183673599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20046426912), (Int.ofNat 536150013408), (Int.ofNat 3188826844488), (Int.ofNat 136124292096), (Int.ofNat 44033938632000), (Int.negSucc 4107629698559), (Int.ofNat 179381498140800)]]

theorem h4n88_arithmetic_row0 :
    (BiPoly.mul h4p3 h4p87).getD 0 []=h4p88.getD 0 [] := by
  decide +kernel

theorem h4n88_arithmetic_row1 :
    (BiPoly.mul h4p3 h4p87).getD 1 []=h4p88.getD 1 [] := by
  decide +kernel

theorem h4n88_arithmetic_row2 :
    (BiPoly.mul h4p3 h4p87).getD 2 []=h4p88.getD 2 [] := by
  decide +kernel

theorem h4n88_arithmetic_row3 :
    (BiPoly.mul h4p3 h4p87).getD 3 []=h4p88.getD 3 [] := by
  decide +kernel

theorem h4n88_arithmetic_row4 :
    (BiPoly.mul h4p3 h4p87).getD 4 []=h4p88.getD 4 [] := by
  decide +kernel

theorem h4n88_arithmetic_row5 :
    (BiPoly.mul h4p3 h4p87).getD 5 []=h4p88.getD 5 [] := by
  decide +kernel

theorem h4n88_arithmetic_row6 :
    (BiPoly.mul h4p3 h4p87).getD 6 []=h4p88.getD 6 [] := by
  decide +kernel

theorem h4n88_arithmetic_row7 :
    (BiPoly.mul h4p3 h4p87).getD 7 []=h4p88.getD 7 [] := by
  decide +kernel

theorem h4n88_arithmetic_row8 :
    (BiPoly.mul h4p3 h4p87).getD 8 []=h4p88.getD 8 [] := by
  decide +kernel

theorem h4n88_arithmetic_row9 :
    (BiPoly.mul h4p3 h4p87).getD 9 []=h4p88.getD 9 [] := by
  decide +kernel

theorem h4n88_arithmetic_row10 :
    (BiPoly.mul h4p3 h4p87).getD 10 []=h4p88.getD 10 [] := by
  decide +kernel

theorem h4n88_arithmetic_row11 :
    (BiPoly.mul h4p3 h4p87).getD 11 []=h4p88.getD 11 [] := by
  decide +kernel

theorem h4n88_arithmetic_row12 :
    (BiPoly.mul h4p3 h4p87).getD 12 []=h4p88.getD 12 [] := by
  decide +kernel

theorem h4n88_arithmetic_row13 :
    (BiPoly.mul h4p3 h4p87).getD 13 []=h4p88.getD 13 [] := by
  decide +kernel

theorem h4n88_arithmetic_row14 :
    (BiPoly.mul h4p3 h4p87).getD 14 []=h4p88.getD 14 [] := by
  decide +kernel

theorem h4n88_arithmetic : BiPoly.mul h4p3 h4p87=h4p88 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<15 at hk
    have hf : ∀ j : Fin 15, (BiPoly.mul h4p3 h4p87).getD j.val []=h4p88.getD j.val [] :=
      (fun j => Fin.cases h4n88_arithmetic_row0 (fun j => Fin.cases h4n88_arithmetic_row1 (fun j => Fin.cases h4n88_arithmetic_row2 (fun j => Fin.cases h4n88_arithmetic_row3 (fun j => Fin.cases h4n88_arithmetic_row4 (fun j => Fin.cases h4n88_arithmetic_row5 (fun j => Fin.cases h4n88_arithmetic_row6 (fun j => Fin.cases h4n88_arithmetic_row7 (fun j => Fin.cases h4n88_arithmetic_row8 (fun j => Fin.cases h4n88_arithmetic_row9 (fun j => Fin.cases h4n88_arithmetic_row10 (fun j => Fin.cases h4n88_arithmetic_row11 (fun j => Fin.cases h4n88_arithmetic_row12 (fun j => Fin.cases h4n88_arithmetic_row13 (fun j => Fin.cases h4n88_arithmetic_row14 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n88 : h4e88.toBi mapPolyEnv=h4p88 := by
  change BiPoly.mul (h4e3.toBi mapPolyEnv) (h4e87.toBi mapPolyEnv)=h4p88
  rw [h4n3, h4n87]
  exact h4n88_arithmetic

#print axioms h4n88_arithmetic
end StackSorting.RationalLift
