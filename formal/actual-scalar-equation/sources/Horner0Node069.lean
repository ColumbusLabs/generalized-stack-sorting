import BivariateRowEquality
import Horner0Base
import Horner0Node068
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p69 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 14624107462656), (Int.ofNat 13016090133504), (Int.ofNat 134845135368192), (Int.ofNat 206976244488192), (Int.negSucc 189200196513791), (Int.negSucc 437284390910975), (Int.negSucc 177561102606335)], [(Int.ofNat 0), (Int.negSucc 181462371323903), (Int.negSucc 112974093633023), (Int.negSucc 1911253637509631), (Int.negSucc 2663039777338367), (Int.ofNat 1962507638191104), (Int.ofNat 4088158445136384), (Int.ofNat 1465370124774912), (Int.ofNat 23017179967488)], [(Int.ofNat 0), (Int.ofNat 1045836108638208), (Int.ofNat 484800808055040), (Int.ofNat 12628817725552128), (Int.ofNat 15719764698180864), (Int.negSucc 8740057779366911), (Int.negSucc 17461180173268223), (Int.negSucc 6766442196244991), (Int.negSucc 804580856379647), (Int.ofNat 60952902506496)], [(Int.ofNat 0), (Int.negSucc 3714712631691263), (Int.negSucc 1622568230909567), (Int.negSucc 51161553171372671), (Int.negSucc 57567726421637759), (Int.ofNat 18801270960227712), (Int.ofNat 44992383292082304), (Int.ofNat 23394130928945280), (Int.ofNat 5151934257925248), (Int.negSucc 371775370732415), (Int.ofNat 1525683151872)], [(Int.ofNat 0), (Int.ofNat 9098060247467520), (Int.ofNat 5205781942811520), (Int.ofNat 141496098105196800), (Int.ofNat 150598171126433664), (Int.negSucc 4763411556424703), (Int.negSucc 77550463783073663), (Int.negSucc 60889636238866175), (Int.negSucc 17130963115917695), (Int.negSucc 110128564804607), (Int.ofNat 134231489935872), (Int.negSucc 6003501182975)], [(Int.ofNat 0), (Int.negSucc 16288358853727999), (Int.negSucc 14776998939885055), (Int.negSucc 282800850055774719), (Int.negSucc 308046672474733439), (Int.negSucc 90913798407676799), (Int.ofNat 88416929239658496), (Int.ofNat 112149068688763648), (Int.ofNat 39567096906322048), (Int.ofNat 5562445777280384), (Int.negSucc 833476436411647), (Int.ofNat 42656181770752), (Int.negSucc 909621391359)], [(Int.ofNat 0), (Int.ofNat 22048400525041920), (Int.ofNat 32825061437469184), (Int.ofNat 423342912754443008), (Int.ofNat 519593595478235520), (Int.ofNat 301200981691570176), (Int.negSucc 37688561700246527), (Int.negSucc 137038583493953279), (Int.negSucc 71748907752830335), (Int.negSucc 18650383886288127), (Int.ofNat 1219856231259648), (Int.negSucc 14263676132863), (Int.ofNat 937036795904)], [(Int.ofNat 0), (Int.negSucc 23022444609579263), (Int.negSucc 54683814035927167), (Int.negSucc 487489337315165055), (Int.negSucc 732814167887233151), (Int.negSucc 567486534786221183), (Int.negSucc 110280328234492031), (Int.ofNat 93508949185039488), (Int.ofNat 99216454918024960), (Int.ofNat 33372773918044160), (Int.ofNat 2341658384747136), (Int.negSucc 413927192777599), (Int.ofNat 13739693677568)], [(Int.ofNat 0), (Int.ofNat 18750786757643520), (Int.ofNat 68229772510300288), (Int.ofNat 442620510319555328), (Int.ofNat 851818391372201344), (Int.ofNat 768928548802007296), (Int.ofNat 334526597151215744), (Int.ofNat 13331649286559488), (Int.negSucc 89600311328491263), (Int.negSucc 40869852435468799), (Int.negSucc 10500802338030463), (Int.ofNat 839347684194560), (Int.negSucc 21887515056127)], [(Int.ofNat 0), (Int.negSucc 11963724152944127), (Int.negSucc 64223236232943103), (Int.negSucc 325721679499496703), (Int.negSucc 797980056325028735), (Int.negSucc 822845620878260863), (Int.negSucc 526166058338025471), (Int.negSucc 139267426140370175), (Int.ofNat 28588633866083072), (Int.ofNat 37425516189620224), (Int.ofNat 15696879616740096), (Int.ofNat 355719506722304), (Int.negSucc 61670611298815)], [(Int.ofNat 0), (Int.ofNat 5969756221653504), (Int.ofNat 45810525264457984), (Int.ofNat 200247008387077376), (Int.ofNat 592413412347000192), (Int.ofNat 726565566917880064), (Int.ofNat 572974831712272640), (Int.ofNat 236972004310637568), (Int.ofNat 47609982600235520), (Int.negSucc 20776269848066815), (Int.negSucc 12103399854258431), (Int.negSucc 2956760632583679), (Int.ofNat 152729423934976)], [(Int.ofNat 0), (Int.negSucc 2310558439881215), (Int.negSucc 24722419743889279), (Int.negSucc 105241740986122623), (Int.negSucc 346258704657395071), (Int.negSucc 531003893863324287), (Int.negSucc 472778518215536767), (Int.negSucc 267698199089525887), (Int.negSucc 91263082263443327), (Int.negSucc 5428369886444159), (Int.ofNat 4438850796131200), (Int.ofNat 3737565920561280), (Int.ofNat 18052025974272)], [(Int.ofNat 0), (Int.ofNat 682079162105856), (Int.ofNat 9999980524713088), (Int.ofNat 47199637462511360), (Int.ofNat 160214897635307136), (Int.ofNat 313319172593967104), (Int.ofNat 313293035809667968), (Int.ofNat 222377314760759040), (Int.ofNat 93240203227640448), (Int.ofNat 25135620483670272), (Int.ofNat 1194136508958336), (Int.negSucc 1608829527197951), (Int.negSucc 329762141084159)], [(Int.ofNat 0), (Int.negSucc 148981243097855), (Int.negSucc 2973479360622079), (Int.negSucc 17445426573346815), (Int.negSucc 59740571949938303), (Int.negSucc 144515279640180351), (Int.negSucc 172006168376740351), (Int.negSucc 139248426381407999), (Int.negSucc 71407444291549055), (Int.negSucc 27057792418929791), (Int.negSucc 4197970526450687), (Int.negSucc 549864159978239), (Int.ofNat 328977928820736)], [(Int.ofNat 0), (Int.ofNat 22786247959808), (Int.ofNat 628158785915904), (Int.ofNat 5009816775093504), (Int.ofNat 18329607946486912), (Int.ofNat 50857844300261376), (Int.ofNat 77268566641807872), (Int.ofNat 67857423210696960), (Int.ofNat 42974543367089280), (Int.ofNat 17921613005708544), (Int.ofNat 4853478621298176), (Int.ofNat 950724883104768), (Int.negSucc 47510567414783)], [(Int.ofNat 0), (Int.negSucc 2186337404159), (Int.negSucc 88817490997631), (Int.negSucc 1038579771904127), (Int.negSucc 4607034396211583), (Int.negSucc 13567893889732991), (Int.negSucc 27000910771673471), (Int.negSucc 26827552326063743), (Int.negSucc 19714215108105215), (Int.negSucc 8913151287638783), (Int.negSucc 3326195578664447), (Int.negSucc 575304041175551), (Int.negSucc 107339249240063)], [(Int.ofNat 0), (Int.ofNat 99261676800), (Int.ofNat 7493973091200), (Int.ofNat 141198169459968), (Int.ofNat 891911584126080), (Int.ofNat 2790192734611200), (Int.ofNat 6894313358177664), (Int.ofNat 8691881156584704), (Int.ofNat 6754752401628672), (Int.ofNat 3630639082337280), (Int.ofNat 1400019629842944), (Int.ofNat 299680646593536), (Int.ofNat 67109843589120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 283208140799), (Int.negSucc 10735897151231), (Int.negSucc 116803912629887), (Int.negSucc 450255211526015), (Int.negSucc 1221289157910527), (Int.negSucc 2165096717662463), (Int.negSucc 1783227561329663), (Int.negSucc 1148088145646591), (Int.negSucc 397572722122751), (Int.negSucc 126100668533759), (Int.negSucc 13321382363135)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 312073585920), (Int.ofNat 8214873448320), (Int.ofNat 53338408471296), (Int.ofNat 148337884472832), (Int.ofNat 364320797082624), (Int.ofNat 382797259278336), (Int.ofNat 247977554706432), (Int.ofNat 95561093910528), (Int.ofNat 27461608132608), (Int.ofNat 855135055872)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 165503761919), (Int.negSucc 3520050068735), (Int.negSucc 13179691574783), (Int.negSucc 34712828785151), (Int.negSucc 62018072506367), (Int.negSucc 35686789208063), (Int.negSucc 18421257904127), (Int.negSucc 2103031517183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 42212109312), (Int.ofNat 793450971648), (Int.ofNat 1597003527168), (Int.ofNat 5405814982656), (Int.ofNat 4352480759808), (Int.ofNat 1640657866752)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4152010751), (Int.negSucc 72937884671), (Int.negSucc 71448625151), (Int.negSucc 392761405439)]]

theorem h0n69_arithmetic_row0 :
    (BiPoly.mul h0p5 h0p68).getD 0 []=h0p69.getD 0 [] := by
  decide +kernel

theorem h0n69_arithmetic_row1 :
    (BiPoly.mul h0p5 h0p68).getD 1 []=h0p69.getD 1 [] := by
  decide +kernel

theorem h0n69_arithmetic_row2 :
    (BiPoly.mul h0p5 h0p68).getD 2 []=h0p69.getD 2 [] := by
  decide +kernel

theorem h0n69_arithmetic_row3 :
    (BiPoly.mul h0p5 h0p68).getD 3 []=h0p69.getD 3 [] := by
  decide +kernel

theorem h0n69_arithmetic_row4 :
    (BiPoly.mul h0p5 h0p68).getD 4 []=h0p69.getD 4 [] := by
  decide +kernel

theorem h0n69_arithmetic_row5 :
    (BiPoly.mul h0p5 h0p68).getD 5 []=h0p69.getD 5 [] := by
  decide +kernel

theorem h0n69_arithmetic_row6 :
    (BiPoly.mul h0p5 h0p68).getD 6 []=h0p69.getD 6 [] := by
  decide +kernel

theorem h0n69_arithmetic_row7 :
    (BiPoly.mul h0p5 h0p68).getD 7 []=h0p69.getD 7 [] := by
  decide +kernel

theorem h0n69_arithmetic_row8 :
    (BiPoly.mul h0p5 h0p68).getD 8 []=h0p69.getD 8 [] := by
  decide +kernel

theorem h0n69_arithmetic_row9 :
    (BiPoly.mul h0p5 h0p68).getD 9 []=h0p69.getD 9 [] := by
  decide +kernel

theorem h0n69_arithmetic_row10 :
    (BiPoly.mul h0p5 h0p68).getD 10 []=h0p69.getD 10 [] := by
  decide +kernel

theorem h0n69_arithmetic_row11 :
    (BiPoly.mul h0p5 h0p68).getD 11 []=h0p69.getD 11 [] := by
  decide +kernel

theorem h0n69_arithmetic_row12 :
    (BiPoly.mul h0p5 h0p68).getD 12 []=h0p69.getD 12 [] := by
  decide +kernel

theorem h0n69_arithmetic_row13 :
    (BiPoly.mul h0p5 h0p68).getD 13 []=h0p69.getD 13 [] := by
  decide +kernel

theorem h0n69_arithmetic_row14 :
    (BiPoly.mul h0p5 h0p68).getD 14 []=h0p69.getD 14 [] := by
  decide +kernel

theorem h0n69_arithmetic_row15 :
    (BiPoly.mul h0p5 h0p68).getD 15 []=h0p69.getD 15 [] := by
  decide +kernel

theorem h0n69_arithmetic_row16 :
    (BiPoly.mul h0p5 h0p68).getD 16 []=h0p69.getD 16 [] := by
  decide +kernel

theorem h0n69_arithmetic_row17 :
    (BiPoly.mul h0p5 h0p68).getD 17 []=h0p69.getD 17 [] := by
  decide +kernel

theorem h0n69_arithmetic_row18 :
    (BiPoly.mul h0p5 h0p68).getD 18 []=h0p69.getD 18 [] := by
  decide +kernel

theorem h0n69_arithmetic_row19 :
    (BiPoly.mul h0p5 h0p68).getD 19 []=h0p69.getD 19 [] := by
  decide +kernel

theorem h0n69_arithmetic_row20 :
    (BiPoly.mul h0p5 h0p68).getD 20 []=h0p69.getD 20 [] := by
  decide +kernel

theorem h0n69_arithmetic_row21 :
    (BiPoly.mul h0p5 h0p68).getD 21 []=h0p69.getD 21 [] := by
  decide +kernel

theorem h0n69_arithmetic : BiPoly.mul h0p5 h0p68=h0p69 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h0p5 h0p68).getD j.val []=h0p69.getD j.val [] :=
      (fun j => Fin.cases h0n69_arithmetic_row0 (fun j => Fin.cases h0n69_arithmetic_row1 (fun j => Fin.cases h0n69_arithmetic_row2 (fun j => Fin.cases h0n69_arithmetic_row3 (fun j => Fin.cases h0n69_arithmetic_row4 (fun j => Fin.cases h0n69_arithmetic_row5 (fun j => Fin.cases h0n69_arithmetic_row6 (fun j => Fin.cases h0n69_arithmetic_row7 (fun j => Fin.cases h0n69_arithmetic_row8 (fun j => Fin.cases h0n69_arithmetic_row9 (fun j => Fin.cases h0n69_arithmetic_row10 (fun j => Fin.cases h0n69_arithmetic_row11 (fun j => Fin.cases h0n69_arithmetic_row12 (fun j => Fin.cases h0n69_arithmetic_row13 (fun j => Fin.cases h0n69_arithmetic_row14 (fun j => Fin.cases h0n69_arithmetic_row15 (fun j => Fin.cases h0n69_arithmetic_row16 (fun j => Fin.cases h0n69_arithmetic_row17 (fun j => Fin.cases h0n69_arithmetic_row18 (fun j => Fin.cases h0n69_arithmetic_row19 (fun j => Fin.cases h0n69_arithmetic_row20 (fun j => Fin.cases h0n69_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n69 : h0e69.toBi mapPolyEnv=h0p69 := by
  change BiPoly.mul (h0e5.toBi mapPolyEnv) (h0e68.toBi mapPolyEnv)=h0p69
  rw [h0n5, h0n68]
  exact h0n69_arithmetic

#print axioms h0n69_arithmetic
end StackSorting.RationalLift
