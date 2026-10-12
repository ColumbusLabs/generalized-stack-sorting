import BivariateRowEquality
import Horner1Base
import Horner1Node062
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p63 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 28221642863999), (Int.negSucc 197119034619839), (Int.negSucc 376982477576639), (Int.negSucc 73383243952319), (Int.ofNat 336813020665920), (Int.ofNat 202111178797440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 311985035631360), (Int.ofNat 2056911550860672), (Int.ofNat 3509726745816576), (Int.ofNat 98943163229376), (Int.negSucc 3084761154136319), (Int.negSucc 1410185249671103), (Int.ofNat 8718837107328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1588847522990399), (Int.negSucc 9979393911835679), (Int.negSucc 15665103116061551), (Int.ofNat 485638103793600), (Int.ofNat 11669146915379904), (Int.ofNat 5340969982285632), (Int.ofNat 840775183487280), (Int.negSucc 73936199083679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4938585076186560), (Int.ofNat 29944550609033184), (Int.ofNat 45483926218573968), (Int.ofNat 1872614317773312), (Int.negSucc 24600859631824031), (Int.negSucc 16678292509406015), (Int.negSucc 5301406304073071), (Int.ofNat 508085343958752), (Int.negSucc 13711429353599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10462337532965879), (Int.negSucc 62354728827422603), (Int.negSucc 97934950640172095), (Int.negSucc 22906672043122475), (Int.ofNat 31262490989883936), (Int.ofNat 40854519494325468), (Int.ofNat 14801521447281312), (Int.ofNat 321292338714684), (Int.negSucc 147476738077991), (Int.ofNat 6540273780480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15973138958876640), (Int.ofNat 95784849726395472), (Int.ofNat 166656074288093136), (Int.ofNat 83117868429672288), (Int.negSucc 17144093147146631), (Int.negSucc 67334633696355839), (Int.negSucc 28772802588265055), (Int.negSucc 7321569089810687), (Int.ofNat 1160071670984760), (Int.negSucc 72189012575375), (Int.ofNat 2214389675520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 18115762500250199), (Int.negSucc 112493074253065451), (Int.negSucc 229291308814211555), (Int.negSucc 180091429602641207), (Int.negSucc 29957617065902843), (Int.ofNat 65270927279562492), (Int.ofNat 47838653345245332), (Int.ofNat 19235056482621936), (Int.negSucc 1151351787106379), (Int.ofNat 6912425274648), (Int.negSucc 2665342588127), (Int.ofNat 178341656064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15498092752700160), (Int.ofNat 103084802311518048), (Int.ofNat 254945492931221280), (Int.ofNat 275005628646022512), (Int.ofNat 110537817909954744), (Int.negSucc 17531702322532703), (Int.negSucc 61239714456202415), (Int.negSucc 26252409374676911), (Int.negSucc 4954563731173655), (Int.ofNat 853871296145856), (Int.negSucc 46223234374655), (Int.ofNat 724948910400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10046012057346159), (Int.negSucc 74357515401722615), (Int.negSucc 226906425582015775), (Int.negSucc 317855863466745323), (Int.negSucc 198242001853338947), (Int.negSucc 54911359742521607), (Int.ofNat 43956103601758784), (Int.ofNat 26380455446116512), (Int.ofNat 13573038079597420), (Int.negSucc 1145787113719539), (Int.ofNat 48699670083576), (Int.negSucc 2105742012127)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4908295206703680), (Int.ofNat 42162995933099904), (Int.ofNat 159754399913340624), (Int.ofNat 286794023811325392), (Int.ofNat 247741453818009192), (Int.ofNat 115778361315007824), (Int.ofNat 5973697174309320), (Int.negSucc 22227443324783615), (Int.negSucc 13573986719601551), (Int.negSucc 1965853285020911), (Int.ofNat 283801865103960), (Int.negSucc 9101801474831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1778780626814639), (Int.negSucc 18581724518337911), (Int.negSucc 87796373987962775), (Int.negSucc 203309729623575263), (Int.negSucc 232578359480391983), (Int.negSucc 142280851105551335), (Int.negSucc 53526005344762607), (Int.ofNat 8288999776526088), (Int.ofNat 6386549659564092), (Int.ofNat 5278675471772148), (Int.negSucc 372772976264171), (Int.ofNat 10924105151928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 463571965951040), (Int.ofNat 6223102577510400), (Int.ofNat 37020638941662400), (Int.ofNat 112148183908142624), (Int.ofNat 168170347780922112), (Int.ofNat 130919593954318240), (Int.ofNat 69699980151572944), (Int.ofNat 12754324111122000), (Int.negSucc 1038518459240439), (Int.negSucc 3620327126427199), (Int.negSucc 492521673212063), (Int.ofNat 39203983123712)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 82120631118359), (Int.negSucc 1525566522162107), (Int.negSucc 11680936666188767), (Int.negSucc 47123605668528467), (Int.negSucc 93801172072485671), (Int.negSucc 94161114726376427), (Int.negSucc 58615320019842719), (Int.negSucc 24709288025374139), (Int.negSucc 2324106468633995), (Int.negSucc 19785004192775), (Int.ofNat 1028161653049968), (Int.negSucc 37159227020447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8851589791200), (Int.ofNat 257202366532272), (Int.ofNat 2652361249267488), (Int.ofNat 14599528533065856), (Int.ofNat 39683044500695496), (Int.ofNat 52674957287188656), (Int.ofNat 38282331995465280), (Int.ofNat 21552900467648688), (Int.ofNat 5240128694013096), (Int.ofNat 1234176442648128), (Int.negSucc 373062461619959), (Int.negSucc 58667336842415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 438071490999), (Int.negSucc 26553695618939), (Int.negSucc 406190198485747), (Int.negSucc 3174939569786791), (Int.negSucc 12298882643347691), (Int.negSucc 22375397860493739), (Int.negSucc 20281463145398771), (Int.negSucc 12487784133437831), (Int.negSucc 5394451970283911), (Int.negSucc 1011978309968807), (Int.negSucc 248310751813631), (Int.ofNat 70848320258400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1261089835200), (Int.ofNat 37161307673040), (Int.ofNat 447165608638320), (Int.ofNat 2637806649673992), (Int.ofNat 6934109834502768), (Int.ofNat 8455817743058544), (Int.ofNat 5643167033916768), (Int.ofNat 3166400606603376), (Int.ofNat 806358954075312), (Int.ofNat 240100837900272), (Int.negSucc 1474576432991)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1510112973599), (Int.negSucc 35006568119507), (Int.negSucc 355415616049811), (Int.negSucc 1472272548237287), (Int.negSucc 2597941335707807), (Int.negSucc 2128677461649263), (Int.negSucc 1210698848499839), (Int.negSucc 503010159687071), (Int.negSucc 97595223268607), (Int.negSucc 23276123127935)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1035264808080), (Int.ofNat 24721251368760), (Int.ofNat 192433214555424), (Int.ofNat 540572253307272), (Int.ofNat 629639118485136), (Int.ofNat 358482482631360), (Int.ofNat 186035756586624), (Int.ofNat 39467529112608), (Int.ofNat 10304755785792)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 480171930119), (Int.negSucc 12330800636327), (Int.negSucc 67402930641119), (Int.negSucc 126694970492255), (Int.negSucc 91946560875551), (Int.negSucc 41087879621855), (Int.negSucc 14195532211775), (Int.negSucc 1677051910655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 157021238448), (Int.ofNat 3914426060784), (Int.ofNat 14532966088992), (Int.ofNat 17459383803552), (Int.ofNat 6923461630464), (Int.ofNat 2714214184128), (Int.ofNat 94469535360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 31754330207), (Int.negSucc 697324176287), (Int.negSucc 1765420878527), (Int.negSucc 1090049228927), (Int.negSucc 188939070719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2826093888), (Int.ofNat 52886955456), (Int.ofNat 94469535360)]]

theorem h1n63_arithmetic_row0 :
    (BiPoly.mul h1p6 h1p62).getD 0 []=h1p63.getD 0 [] := by
  decide +kernel

theorem h1n63_arithmetic_row1 :
    (BiPoly.mul h1p6 h1p62).getD 1 []=h1p63.getD 1 [] := by
  decide +kernel

theorem h1n63_arithmetic_row2 :
    (BiPoly.mul h1p6 h1p62).getD 2 []=h1p63.getD 2 [] := by
  decide +kernel

theorem h1n63_arithmetic_row3 :
    (BiPoly.mul h1p6 h1p62).getD 3 []=h1p63.getD 3 [] := by
  decide +kernel

theorem h1n63_arithmetic_row4 :
    (BiPoly.mul h1p6 h1p62).getD 4 []=h1p63.getD 4 [] := by
  decide +kernel

theorem h1n63_arithmetic_row5 :
    (BiPoly.mul h1p6 h1p62).getD 5 []=h1p63.getD 5 [] := by
  decide +kernel

theorem h1n63_arithmetic_row6 :
    (BiPoly.mul h1p6 h1p62).getD 6 []=h1p63.getD 6 [] := by
  decide +kernel

theorem h1n63_arithmetic_row7 :
    (BiPoly.mul h1p6 h1p62).getD 7 []=h1p63.getD 7 [] := by
  decide +kernel

theorem h1n63_arithmetic_row8 :
    (BiPoly.mul h1p6 h1p62).getD 8 []=h1p63.getD 8 [] := by
  decide +kernel

theorem h1n63_arithmetic_row9 :
    (BiPoly.mul h1p6 h1p62).getD 9 []=h1p63.getD 9 [] := by
  decide +kernel

theorem h1n63_arithmetic_row10 :
    (BiPoly.mul h1p6 h1p62).getD 10 []=h1p63.getD 10 [] := by
  decide +kernel

theorem h1n63_arithmetic_row11 :
    (BiPoly.mul h1p6 h1p62).getD 11 []=h1p63.getD 11 [] := by
  decide +kernel

theorem h1n63_arithmetic_row12 :
    (BiPoly.mul h1p6 h1p62).getD 12 []=h1p63.getD 12 [] := by
  decide +kernel

theorem h1n63_arithmetic_row13 :
    (BiPoly.mul h1p6 h1p62).getD 13 []=h1p63.getD 13 [] := by
  decide +kernel

theorem h1n63_arithmetic_row14 :
    (BiPoly.mul h1p6 h1p62).getD 14 []=h1p63.getD 14 [] := by
  decide +kernel

theorem h1n63_arithmetic_row15 :
    (BiPoly.mul h1p6 h1p62).getD 15 []=h1p63.getD 15 [] := by
  decide +kernel

theorem h1n63_arithmetic_row16 :
    (BiPoly.mul h1p6 h1p62).getD 16 []=h1p63.getD 16 [] := by
  decide +kernel

theorem h1n63_arithmetic_row17 :
    (BiPoly.mul h1p6 h1p62).getD 17 []=h1p63.getD 17 [] := by
  decide +kernel

theorem h1n63_arithmetic_row18 :
    (BiPoly.mul h1p6 h1p62).getD 18 []=h1p63.getD 18 [] := by
  decide +kernel

theorem h1n63_arithmetic_row19 :
    (BiPoly.mul h1p6 h1p62).getD 19 []=h1p63.getD 19 [] := by
  decide +kernel

theorem h1n63_arithmetic_row20 :
    (BiPoly.mul h1p6 h1p62).getD 20 []=h1p63.getD 20 [] := by
  decide +kernel

theorem h1n63_arithmetic_row21 :
    (BiPoly.mul h1p6 h1p62).getD 21 []=h1p63.getD 21 [] := by
  decide +kernel

theorem h1n63_arithmetic : BiPoly.mul h1p6 h1p62=h1p63 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p6 h1p62).getD j.val []=h1p63.getD j.val [] :=
      (fun j => Fin.cases h1n63_arithmetic_row0 (fun j => Fin.cases h1n63_arithmetic_row1 (fun j => Fin.cases h1n63_arithmetic_row2 (fun j => Fin.cases h1n63_arithmetic_row3 (fun j => Fin.cases h1n63_arithmetic_row4 (fun j => Fin.cases h1n63_arithmetic_row5 (fun j => Fin.cases h1n63_arithmetic_row6 (fun j => Fin.cases h1n63_arithmetic_row7 (fun j => Fin.cases h1n63_arithmetic_row8 (fun j => Fin.cases h1n63_arithmetic_row9 (fun j => Fin.cases h1n63_arithmetic_row10 (fun j => Fin.cases h1n63_arithmetic_row11 (fun j => Fin.cases h1n63_arithmetic_row12 (fun j => Fin.cases h1n63_arithmetic_row13 (fun j => Fin.cases h1n63_arithmetic_row14 (fun j => Fin.cases h1n63_arithmetic_row15 (fun j => Fin.cases h1n63_arithmetic_row16 (fun j => Fin.cases h1n63_arithmetic_row17 (fun j => Fin.cases h1n63_arithmetic_row18 (fun j => Fin.cases h1n63_arithmetic_row19 (fun j => Fin.cases h1n63_arithmetic_row20 (fun j => Fin.cases h1n63_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n63 : h1e63.toBi mapPolyEnv=h1p63 := by
  change BiPoly.mul (h1e6.toBi mapPolyEnv) (h1e62.toBi mapPolyEnv)=h1p63
  rw [h1n6, h1n62]
  exact h1n63_arithmetic

#print axioms h1n63_arithmetic
end StackSorting.RationalLift
