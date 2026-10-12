import BivariateRowEquality
import Horner0Base
import Horner0Node009
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p130 : BiPoly.Poly := [[(Int.ofNat 1523547190158984000), (Int.ofNat 8473470224594459040), (Int.negSucc 1641493482691854239), (Int.negSucc 37650745919933655839), (Int.ofNat 28303810627109925600)], [(Int.negSucc 14069341517855420159), (Int.negSucc 79013997066626834111), (Int.ofNat 8260087572416932128), (Int.ofNat 331372369742364126720), (Int.negSucc 260102109428644196447), (Int.ofNat 20503028648447913600)], [(Int.ofNat 61245369733168400400), (Int.ofNat 334793485429540626600), (Int.negSucc 16561192275250137647), (Int.negSucc 1266696631557395193311), (Int.ofNat 951548086913320221120), (Int.negSucc 96415370736654502439), (Int.ofNat 4807010716573936896)], [(Int.negSucc 166517434537287751439), (Int.negSucc 852229661884087460039), (Int.negSucc 6827982227774622287), (Int.ofNat 2665350122072772292992), (Int.negSucc 1618168628831979406607), (Int.ofNat 32683403258367366888), (Int.negSucc 1366285219295570639), (Int.ofNat 353125975877503488)], [(Int.ofNat 314804126306428428240), (Int.ofNat 1458273128092504686936), (Int.ofNat 163714353072965874864), (Int.negSucc 3173924780015596954415), (Int.ofNat 635673074859872281152), (Int.ofNat 654516596288913869160), (Int.negSucc 62272972945921815791), (Int.ofNat 1923707684118371616), (Int.negSucc 1882071922199039)], [(Int.negSucc 435123164643461823959), (Int.negSucc 1789208770193500879331), (Int.negSucc 570286344970581573779), (Int.ofNat 1683541924332341761800), (Int.ofNat 2376057317194384266960), (Int.negSucc 1631564590248091001555), (Int.ofNat 96261980424357715164), (Int.negSucc 2684972349889893791), (Int.ofNat 61496522657174592)], [(Int.ofNat 450072092762200293000), (Int.ofNat 1654416190316480091588), (Int.ofNat 1144755245491872277344), (Int.ofNat 735937883393546148528), (Int.negSucc 4461576349097786963927), (Int.ofNat 1222466128891517192076), (Int.ofNat 175721282884816336656), (Int.negSucc 15207290372057506967), (Int.ofNat 366847761812622528)], [(Int.negSucc 351129317540932662839), (Int.negSucc 1209578366857859930891), (Int.negSucc 1549220852843994231179), (Int.negSucc 2007013367684076614687), (Int.ofNat 2969407157668024814280), (Int.ofNat 926000210746072644180), (Int.negSucc 573123419594761550387), (Int.ofNat 21745972483213116960), (Int.ofNat 12144765118956864)], [(Int.ofNat 206047609985625655320), (Int.ofNat 730856452439120862180), (Int.ofNat 1507972054398563637288), (Int.ofNat 1705484106664714842888), (Int.ofNat 240238247047796110104), (Int.negSucc 2329102594866002795051), (Int.ofNat 391273022775722232072), (Int.ofNat 35016168505210865640), (Int.negSucc 1976490268908369455)], [(Int.negSucc 89841877410993057719), (Int.negSucc 373168882430779761995), (Int.negSucc 1091818076919901365071), (Int.negSucc 956021728400297596415), (Int.negSucc 1771513826392760952035), (Int.ofNat 1411371872596690337712), (Int.ofNat 290055101565663039684), (Int.negSucc 81826991084639502983), (Int.negSucc 74599373012952371)], [(Int.ofNat 28434363379598384520), (Int.ofNat 158372592831560458716), (Int.ofNat 595535255108549625660), (Int.ofNat 519991424678445090900), (Int.ofNat 1284409326486919944624), (Int.ofNat 172049409242218128000), (Int.negSucc 549055629588543868979), (Int.ofNat 22181436085634951124), (Int.ofNat 4368571452527140584)], [(Int.negSucc 6275361283079199479), (Int.negSucc 53246191494285016427), (Int.negSucc 243304686518082383867), (Int.negSucc 322066329081366633863), (Int.negSucc 454148078072858576903), (Int.negSucc 670634999126045083055), (Int.ofNat 211978058943618330120), (Int.ofNat 55421673571517808360), (Int.negSucc 1902639229793152487)], [(Int.ofNat 900183540484277400), (Int.ofNat 13342783970437351332), (Int.ofNat 72798161705613514224), (Int.ofNat 173143186030448532024), (Int.ofNat 102473361043675837296), (Int.ofNat 367883193462829847736), (Int.ofNat 93211171715540758896), (Int.negSucc 45646363303345540007), (Int.negSucc 3033442117270649879)], [(Int.negSucc 73188011075561519), (Int.negSucc 2319947949361704527), (Int.negSucc 15352483841626661939), (Int.negSucc 65034119817030346295), (Int.negSucc 36523410383352583907), (Int.negSucc 86406614105638649615), (Int.negSucc 111149069110653889151), (Int.ofNat 894754287824659632), (Int.ofNat 2553830875248901776)], [(Int.ofNat 2392047021054240), (Int.ofNat 250525838477690424), (Int.ofNat 2152049237365788684), (Int.ofNat 15673262172048305172), (Int.ofNat 19261833149810937960), (Int.ofNat 6420809084773512384), (Int.ofNat 38674672187142029040), (Int.ofNat 12614200338065940432), (Int.ofNat 95558749038487584)], [(Int.ofNat 0), (Int.negSucc 12811266214639487), (Int.negSucc 181213349837762735), (Int.negSucc 2244134739302463239), (Int.negSucc 6361811118904547591), (Int.negSucc 138774351113466767), (Int.negSucc 5024099699100310031), (Int.negSucc 5894992746242687807), (Int.negSucc 719997443556768863)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7119842392942560), (Int.ofNat 160645627094526648), (Int.ofNat 1108459748001259368), (Int.ofNat 506960092324444752), (Int.negSucc 211499277925835519), (Int.ofNat 1062364081048753824), (Int.ofNat 268008283931984928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2996129648131199), (Int.negSucc 86125834476660383), (Int.negSucc 160108250625241343), (Int.ofNat 119684299528688544), (Int.negSucc 65132955554876927), (Int.negSucc 31222937192762879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 962833231078272), (Int.ofNat 15489152235268704), (Int.negSucc 10085937600713759)]]

theorem h0n130_arithmetic_row0 :
    (BiPoly.mul h0p37 h0p9).getD 0 []=h0p130.getD 0 [] := by
  decide +kernel

theorem h0n130_arithmetic_row1 :
    (BiPoly.mul h0p37 h0p9).getD 1 []=h0p130.getD 1 [] := by
  decide +kernel

theorem h0n130_arithmetic_row2 :
    (BiPoly.mul h0p37 h0p9).getD 2 []=h0p130.getD 2 [] := by
  decide +kernel

theorem h0n130_arithmetic_row3 :
    (BiPoly.mul h0p37 h0p9).getD 3 []=h0p130.getD 3 [] := by
  decide +kernel

theorem h0n130_arithmetic_row4 :
    (BiPoly.mul h0p37 h0p9).getD 4 []=h0p130.getD 4 [] := by
  decide +kernel

theorem h0n130_arithmetic_row5 :
    (BiPoly.mul h0p37 h0p9).getD 5 []=h0p130.getD 5 [] := by
  decide +kernel

theorem h0n130_arithmetic_row6 :
    (BiPoly.mul h0p37 h0p9).getD 6 []=h0p130.getD 6 [] := by
  decide +kernel

theorem h0n130_arithmetic_row7 :
    (BiPoly.mul h0p37 h0p9).getD 7 []=h0p130.getD 7 [] := by
  decide +kernel

theorem h0n130_arithmetic_row8 :
    (BiPoly.mul h0p37 h0p9).getD 8 []=h0p130.getD 8 [] := by
  decide +kernel

theorem h0n130_arithmetic_row9 :
    (BiPoly.mul h0p37 h0p9).getD 9 []=h0p130.getD 9 [] := by
  decide +kernel

theorem h0n130_arithmetic_row10 :
    (BiPoly.mul h0p37 h0p9).getD 10 []=h0p130.getD 10 [] := by
  decide +kernel

theorem h0n130_arithmetic_row11 :
    (BiPoly.mul h0p37 h0p9).getD 11 []=h0p130.getD 11 [] := by
  decide +kernel

theorem h0n130_arithmetic_row12 :
    (BiPoly.mul h0p37 h0p9).getD 12 []=h0p130.getD 12 [] := by
  decide +kernel

theorem h0n130_arithmetic_row13 :
    (BiPoly.mul h0p37 h0p9).getD 13 []=h0p130.getD 13 [] := by
  decide +kernel

theorem h0n130_arithmetic_row14 :
    (BiPoly.mul h0p37 h0p9).getD 14 []=h0p130.getD 14 [] := by
  decide +kernel

theorem h0n130_arithmetic_row15 :
    (BiPoly.mul h0p37 h0p9).getD 15 []=h0p130.getD 15 [] := by
  decide +kernel

theorem h0n130_arithmetic_row16 :
    (BiPoly.mul h0p37 h0p9).getD 16 []=h0p130.getD 16 [] := by
  decide +kernel

theorem h0n130_arithmetic_row17 :
    (BiPoly.mul h0p37 h0p9).getD 17 []=h0p130.getD 17 [] := by
  decide +kernel

theorem h0n130_arithmetic_row18 :
    (BiPoly.mul h0p37 h0p9).getD 18 []=h0p130.getD 18 [] := by
  decide +kernel

theorem h0n130_arithmetic : BiPoly.mul h0p37 h0p9=h0p130 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p37 h0p9).getD j.val []=h0p130.getD j.val [] :=
      (fun j => Fin.cases h0n130_arithmetic_row0 (fun j => Fin.cases h0n130_arithmetic_row1 (fun j => Fin.cases h0n130_arithmetic_row2 (fun j => Fin.cases h0n130_arithmetic_row3 (fun j => Fin.cases h0n130_arithmetic_row4 (fun j => Fin.cases h0n130_arithmetic_row5 (fun j => Fin.cases h0n130_arithmetic_row6 (fun j => Fin.cases h0n130_arithmetic_row7 (fun j => Fin.cases h0n130_arithmetic_row8 (fun j => Fin.cases h0n130_arithmetic_row9 (fun j => Fin.cases h0n130_arithmetic_row10 (fun j => Fin.cases h0n130_arithmetic_row11 (fun j => Fin.cases h0n130_arithmetic_row12 (fun j => Fin.cases h0n130_arithmetic_row13 (fun j => Fin.cases h0n130_arithmetic_row14 (fun j => Fin.cases h0n130_arithmetic_row15 (fun j => Fin.cases h0n130_arithmetic_row16 (fun j => Fin.cases h0n130_arithmetic_row17 (fun j => Fin.cases h0n130_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n130 : h0e130.toBi mapPolyEnv=h0p130 := by
  change BiPoly.mul (h0e37.toBi mapPolyEnv) (h0e9.toBi mapPolyEnv)=h0p130
  rw [h0n37, h0n9]
  exact h0n130_arithmetic

#print axioms h0n130_arithmetic
end StackSorting.RationalLift
