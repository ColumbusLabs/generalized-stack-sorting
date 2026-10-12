import BivariateRowEquality
import Horner1Node020
import Horner1Node051
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p52 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 338659714367999), (Int.negSucc 1911201464682575), (Int.negSucc 2168665182693503), (Int.ofNat 1199068220354400), (Int.ofNat 2952624701899008), (Int.ofNat 1157433049165680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3743820427576320), (Int.ofNat 19780312185129600), (Int.ofNat 19198043417416176), (Int.negSucc 12955592008058399), (Int.negSucc 24620857046423999), (Int.negSucc 8658303061194719), (Int.negSucc 154589682692015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 19066170275884799), (Int.negSucc 95774996119059683), (Int.negSucc 84240125034292439), (Int.ofNat 53134015615165476), (Int.ofNat 95158347750137808), (Int.ofNat 38983987423009476), (Int.ofNat 5330765378005704), (Int.negSucc 397075864152131)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 59263020914238720), (Int.ofNat 289445658814760436), (Int.ofNat 252412922017473408), (Int.negSucc 103371719989391099), (Int.negSucc 232278044925555071), (Int.negSucc 130456604487623939), (Int.negSucc 30799368272198303), (Int.ofNat 2061718158660588), (Int.negSucc 8242356222143)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 125548050395590559), (Int.negSucc 614437402477304087), (Int.negSucc 586387121988242267), (Int.ofNat 50853913335554076), (Int.ofNat 395887904486746740), (Int.ofNat 315138273617749824), (Int.ofNat 96573914290708956), (Int.ofNat 3049955118211500), (Int.negSucc 960201419997203), (Int.ofNat 39252152234592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 191677667506519680), (Int.ofNat 976008662711492850), (Int.ofNat 1100177840289356694), (Int.ofNat 260277941239818678), (Int.negSucc 454560809134935833), (Int.negSucc 538872257820519449), (Int.negSucc 213171118677224189), (Int.negSucc 37143384682201253), (Int.ofNat 4930171707576690), (Int.negSucc 244672707783239), (Int.ofNat 5756424309504)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 217389150003002399), (Int.negSucc 1202794470774826397), (Int.negSucc 1669734011113928819), (Int.negSucc 863385711185908853), (Int.ofNat 239380688855633364), (Int.ofNat 636803053828948170), (Int.ofNat 355574878926807852), (Int.ofNat 106441406408376594), (Int.negSucc 3629418546644819), (Int.negSucc 261742819366079), (Int.ofNat 6735965365008), (Int.negSucc 29665753919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 185977113032401920), (Int.ofNat 1171462241452933692), (Int.ofNat 2037444583108774302), (Int.ofNat 1562894305002245772), (Int.ofNat 286305992024789880), (Int.negSucc 451405648298523473), (Int.negSucc 440987015093196905), (Int.negSucc 173216538017763515), (Int.negSucc 21187123412209523), (Int.ofNat 3006529863061014), (Int.negSucc 115276751229815), (Int.ofNat 1062946485216)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 120552144688153919), (Int.negSucc 906371857791410735), (Int.negSucc 1992356028072713177), (Int.negSucc 2022795877659932393), (Int.negSucc 923425841824155017), (Int.ofNat 9033748371374220), (Int.ofNat 366621602915877378), (Int.ofNat 188950473564568962), (Int.ofNat 61500201466688406), (Int.negSucc 2930220054284087), (Int.negSucc 32482344411155), (Int.ofNat 2598168174624)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 58899542480444160), (Int.ofNat 554044672395008892), (Int.ofNat 1558031463404812476), (Int.ofNat 2007923096927281320), (Int.ofNat 1359351576996602994), (Int.ofNat 459131454951824070), (Int.negSucc 116809000385115599), (Int.negSucc 144102915871148537), (Int.negSucc 75643152821741195), (Int.negSucc 6975853495323947), (Int.ofNat 739292813276526), (Int.negSucc 13547030146703)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21345367521775679), (Int.negSucc 263733695281980503), (Int.negSucc 969160994365271111), (Int.negSucc 1566927454459039415), (Int.negSucc 1398825163550942801), (Int.negSucc 720018785820268655), (Int.negSucc 171083324310861239), (Int.ofNat 58394932389611910), (Int.ofNat 46921560881827482), (Int.ofNat 18030741492632382), (Int.negSucc 402231983262191), (Int.negSucc 22460881023107)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5562863591412480), (Int.ofNat 95502675831679428), (Int.ofNat 473933319899188140), (Int.ofNat 968435333552077260), (Int.ofNat 1092088854147608016), (Int.ofNat 715479051370071204), (Int.ofNat 322770468654716088), (Int.ofNat 37780351922238798), (Int.negSucc 7276267796985539), (Int.negSucc 15377989567561061), (Int.negSucc 1462511648240897), (Int.ofNat 63977574069558)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 985447573420319), (Int.negSucc 25403871593051567), (Int.negSucc 178605024866015975), (Int.negSucc 472382051458737167), (Int.negSucc 661599534874125239), (Int.negSucc 536752558985342831), (Int.negSucc 302722449463741427), (Int.negSucc 97685943384489713), (Int.negSucc 15840619432226009), (Int.ofNat 3063978405334548), (Int.ofNat 2122762024407402), (Int.ofNat 50840458914924)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 106219077494400), (Int.ofNat 4701487036543650), (Int.ofNat 50359393617056766), (Int.ofNat 179400497153684598), (Int.ofNat 311857995143363850), (Int.ofNat 315068446318132206), (Int.ofNat 201289381392663342), (Int.ofNat 96451309319929380), (Int.ofNat 22856847738546114), (Int.ofNat 4844856546106578), (Int.negSucc 743397083639711), (Int.negSucc 126217962109475)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5256857891999), (Int.negSucc 551400236137973), (Int.negSucc 10179341123514011), (Int.negSucc 51821231103683213), (Int.negSucc 113387668506124151), (Int.negSucc 143848391324020073), (Int.negSucc 105048272480458139), (Int.negSucc 60494869179986435), (Int.negSucc 19693021124843837), (Int.negSucc 5449182649021763), (Int.negSucc 476744600157335), (Int.ofNat 12354169816944)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 33770140576380), (Int.ofNat 1381935917755638), (Int.ofNat 11013877731498228), (Int.ofNat 31244581458817128), (Int.ofNat 49854536243559198), (Int.ofNat 44249120978688810), (Int.ofNat 27118770934541778), (Int.ofNat 11826841463820000), (Int.ofNat 3290943975713748), (Int.ofNat 635292829886760), (Int.ofNat 64194857705880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 584829671399), (Int.negSucc 112337788195889), (Int.negSucc 1642287300755777), (Int.negSucc 6389086146532433), (Int.negSucc 12619372912661555), (Int.negSucc 14694266521355273), (Int.negSucc 9296825647699115), (Int.negSucc 5021769004288991), (Int.negSucc 1402846102886975), (Int.negSucc 363852974612087), (Int.negSucc 35909747186255)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4147863033600), (Int.ofNat 157436426951676), (Int.ofNat 951651580594302), (Int.ofNat 2232591551916030), (Int.ofNat 3573087456110256), (Int.ofNat 2593675347172452), (Int.ofNat 1475296465713264), (Int.ofNat 466977863081232), (Int.ofNat 122722434167040), (Int.ofNat 6730101954288)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7560039125159), (Int.negSucc 98860166971577), (Int.negSucc 275407349417387), (Int.negSucc 557968394148551), (Int.negSucc 592097655111407), (Int.negSucc 293778714445199), (Int.negSucc 123830969514047), (Int.negSucc 21312930136031), (Int.negSucc 416344893695)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5649029573040), (Int.ofNat 26586416965788), (Int.ofNat 46058430696552), (Int.ofNat 92936206396152), (Int.ofNat 45181946230272), (Int.ofNat 21231512080128), (Int.ofNat 1399506999552)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1833083143775), (Int.negSucc 2146985265815), (Int.negSucc 6355235131055), (Int.negSucc 6548105238047), (Int.negSucc 1549979318015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 214588160064), (Int.negSucc 100578660335), (Int.ofNat 566817212160)]]

theorem h1n52_arithmetic_row0 :
    (BiPoly.mul h1p20 h1p51).getD 0 []=h1p52.getD 0 [] := by
  decide +kernel

theorem h1n52_arithmetic_row1 :
    (BiPoly.mul h1p20 h1p51).getD 1 []=h1p52.getD 1 [] := by
  decide +kernel

theorem h1n52_arithmetic_row2 :
    (BiPoly.mul h1p20 h1p51).getD 2 []=h1p52.getD 2 [] := by
  decide +kernel

theorem h1n52_arithmetic_row3 :
    (BiPoly.mul h1p20 h1p51).getD 3 []=h1p52.getD 3 [] := by
  decide +kernel

theorem h1n52_arithmetic_row4 :
    (BiPoly.mul h1p20 h1p51).getD 4 []=h1p52.getD 4 [] := by
  decide +kernel

theorem h1n52_arithmetic_row5 :
    (BiPoly.mul h1p20 h1p51).getD 5 []=h1p52.getD 5 [] := by
  decide +kernel

theorem h1n52_arithmetic_row6 :
    (BiPoly.mul h1p20 h1p51).getD 6 []=h1p52.getD 6 [] := by
  decide +kernel

theorem h1n52_arithmetic_row7 :
    (BiPoly.mul h1p20 h1p51).getD 7 []=h1p52.getD 7 [] := by
  decide +kernel

theorem h1n52_arithmetic_row8 :
    (BiPoly.mul h1p20 h1p51).getD 8 []=h1p52.getD 8 [] := by
  decide +kernel

theorem h1n52_arithmetic_row9 :
    (BiPoly.mul h1p20 h1p51).getD 9 []=h1p52.getD 9 [] := by
  decide +kernel

theorem h1n52_arithmetic_row10 :
    (BiPoly.mul h1p20 h1p51).getD 10 []=h1p52.getD 10 [] := by
  decide +kernel

theorem h1n52_arithmetic_row11 :
    (BiPoly.mul h1p20 h1p51).getD 11 []=h1p52.getD 11 [] := by
  decide +kernel

theorem h1n52_arithmetic_row12 :
    (BiPoly.mul h1p20 h1p51).getD 12 []=h1p52.getD 12 [] := by
  decide +kernel

theorem h1n52_arithmetic_row13 :
    (BiPoly.mul h1p20 h1p51).getD 13 []=h1p52.getD 13 [] := by
  decide +kernel

theorem h1n52_arithmetic_row14 :
    (BiPoly.mul h1p20 h1p51).getD 14 []=h1p52.getD 14 [] := by
  decide +kernel

theorem h1n52_arithmetic_row15 :
    (BiPoly.mul h1p20 h1p51).getD 15 []=h1p52.getD 15 [] := by
  decide +kernel

theorem h1n52_arithmetic_row16 :
    (BiPoly.mul h1p20 h1p51).getD 16 []=h1p52.getD 16 [] := by
  decide +kernel

theorem h1n52_arithmetic_row17 :
    (BiPoly.mul h1p20 h1p51).getD 17 []=h1p52.getD 17 [] := by
  decide +kernel

theorem h1n52_arithmetic_row18 :
    (BiPoly.mul h1p20 h1p51).getD 18 []=h1p52.getD 18 [] := by
  decide +kernel

theorem h1n52_arithmetic_row19 :
    (BiPoly.mul h1p20 h1p51).getD 19 []=h1p52.getD 19 [] := by
  decide +kernel

theorem h1n52_arithmetic_row20 :
    (BiPoly.mul h1p20 h1p51).getD 20 []=h1p52.getD 20 [] := by
  decide +kernel

theorem h1n52_arithmetic_row21 :
    (BiPoly.mul h1p20 h1p51).getD 21 []=h1p52.getD 21 [] := by
  decide +kernel

theorem h1n52_arithmetic : BiPoly.mul h1p20 h1p51=h1p52 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p20 h1p51).getD j.val []=h1p52.getD j.val [] :=
      (fun j => Fin.cases h1n52_arithmetic_row0 (fun j => Fin.cases h1n52_arithmetic_row1 (fun j => Fin.cases h1n52_arithmetic_row2 (fun j => Fin.cases h1n52_arithmetic_row3 (fun j => Fin.cases h1n52_arithmetic_row4 (fun j => Fin.cases h1n52_arithmetic_row5 (fun j => Fin.cases h1n52_arithmetic_row6 (fun j => Fin.cases h1n52_arithmetic_row7 (fun j => Fin.cases h1n52_arithmetic_row8 (fun j => Fin.cases h1n52_arithmetic_row9 (fun j => Fin.cases h1n52_arithmetic_row10 (fun j => Fin.cases h1n52_arithmetic_row11 (fun j => Fin.cases h1n52_arithmetic_row12 (fun j => Fin.cases h1n52_arithmetic_row13 (fun j => Fin.cases h1n52_arithmetic_row14 (fun j => Fin.cases h1n52_arithmetic_row15 (fun j => Fin.cases h1n52_arithmetic_row16 (fun j => Fin.cases h1n52_arithmetic_row17 (fun j => Fin.cases h1n52_arithmetic_row18 (fun j => Fin.cases h1n52_arithmetic_row19 (fun j => Fin.cases h1n52_arithmetic_row20 (fun j => Fin.cases h1n52_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n52 : h1e52.toBi mapPolyEnv=h1p52 := by
  change BiPoly.mul (h1e20.toBi mapPolyEnv) (h1e51.toBi mapPolyEnv)=h1p52
  rw [h1n20, h1n51]
  exact h1n52_arithmetic

#print axioms h1n52_arithmetic
end StackSorting.RationalLift
