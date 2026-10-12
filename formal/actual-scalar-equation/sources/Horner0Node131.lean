import BivariateRowEquality
import Horner0Base
import Horner0Node014
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p131 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 1338184628217301464), (Int.ofNat 6896993418176813856), (Int.negSucc 4998591952275630383), (Int.negSucc 35782506852489744479), (Int.ofNat 36019521567908184600)], [(Int.ofNat 0), (Int.negSucc 13070006589566823983), (Int.negSucc 71671566004283706047), (Int.ofNat 30822917397206690016), (Int.ofNat 350272528550437985280), (Int.negSucc 325831958384026010543), (Int.ofNat 19727523163884634560)], [(Int.ofNat 0), (Int.ofNat 62063037017117784648), (Int.ofNat 332885730742859008656), (Int.negSucc 97695634702677555743), (Int.negSucc 1446422639193824945471), (Int.ofNat 1231207858411461332280), (Int.negSucc 89945831360498240303), (Int.ofNat 2601022624220522304)], [(Int.ofNat 0), (Int.negSucc 189280938552381917207), (Int.negSucc 924005691240560784071), (Int.ofNat 269953460901483528816), (Int.ofNat 3187188659553220937808), (Int.negSucc 2284717800423943149623), (Int.ofNat 26476849390094112888), (Int.ofNat 3126846883434712992), (Int.negSucc 27416798509098239)], [(Int.ofNat 0), (Int.ofNat 412089739060131908088), (Int.ofNat 1710952137213750353832), (Int.negSucc 651091502957192321255), (Int.negSucc 3734964282815748870095), (Int.ofNat 1447428162100999073088), (Int.ofNat 648204211752588155784), (Int.negSucc 42933729278084200535), (Int.ofNat 999623710759430592), (Int.ofNat 69570687753600)], [(Int.ofNat 0), (Int.negSucc 673906990062538994231), (Int.negSucc 2210357374689197037935), (Int.ofNat 1005717576517106225856), (Int.ofNat 1481342945616054811920), (Int.ofNat 2182513139656066728264), (Int.negSucc 1673023233477085589951), (Int.ofNat 40534131869803600224), (Int.ofNat 1657139500711427136), (Int.negSucc 5048787200434559)], [(Int.ofNat 0), (Int.ofNat 849483205210281333678), (Int.ofNat 2008248375093641884476), (Int.negSucc 614509914451351241261), (Int.ofNat 1630967539662944072184), (Int.negSucc 5096006468724108532181), (Int.ofNat 1420859724768724446300), (Int.ofNat 165858001441863300174), (Int.negSucc 9558149081341233983), (Int.ofNat 83141921628364704)], [(Int.ofNat 0), (Int.negSucc 834731425151571130259), (Int.negSucc 1262975711675070852323), (Int.negSucc 674040082822787174735), (Int.negSucc 2254731158808265683479), (Int.ofNat 3477338615917904257140), (Int.ofNat 631501424789180289684), (Int.negSucc 395719127302775030471), (Int.negSucc 1332320176137371807), (Int.ofNat 322266121986572352)], [(Int.ofNat 0), (Int.ofNat 640111520345873069346), (Int.ofNat 550066793707980718860), (Int.ofNat 1762299583559983716588), (Int.ofNat 729090370715979969540), (Int.ofNat 459999923018653010106), (Int.negSucc 2120568224162675974619), (Int.ofNat 209077667518836859512), (Int.ofNat 34518651028271138820), (Int.negSucc 298846092971234135)], [(Int.ofNat 0), (Int.negSucc 380421697613403642599), (Int.negSucc 217015807484527023479), (Int.negSucc 1695269963848543497215), (Int.ofNat 199018708525353646848), (Int.negSucc 2082601429108440115583), (Int.ofNat 1335885737853636822960), (Int.ofNat 235055360292464614536), (Int.negSucc 29332941334523211287), (Int.negSucc 1082315763415834199)], [(Int.ofNat 0), (Int.ofNat 172736540736662500002), (Int.ofNat 151711528159704283632), (Int.ofNat 890177563029579233496), (Int.ofNat 83959065577679562468), (Int.ofNat 1167497950098751885122), (Int.ofNat 145350351479838926076), (Int.negSucc 334580199706256228885), (Int.negSucc 20969043746573098499), (Int.ofNat 1001718163075539366)], [(Int.ofNat 0), (Int.negSucc 58602933545316906203), (Int.negSucc 127092637159620158435), (Int.negSucc 245713963844752356515), (Int.negSucc 396742431051644180483), (Int.negSucc 181235063430059598623), (Int.negSucc 575944693289898420047), (Int.ofNat 87502905894592732308), (Int.ofNat 38032090471874733516), (Int.ofNat 926384251610897496)], [(Int.ofNat 0), (Int.ofNat 14368152723695741742), (Int.ofNat 75200178449611368420), (Int.ofNat 20973996905989025682), (Int.ofNat 290122932807827867316), (Int.negSucc 34198482828689584523), (Int.ofNat 280621321239450483912), (Int.ofNat 76121239719022031130), (Int.negSucc 10179367807252120559), (Int.negSucc 1258519923632586671)], [(Int.ofNat 0), (Int.negSucc 2419351176157284167), (Int.negSucc 29101005264807406895), (Int.ofNat 1332204839928362928), (Int.negSucc 96837237077038151399), (Int.negSucc 11892444899531925263), (Int.negSucc 47976859304253827783), (Int.negSucc 61233960674747643119), (Int.negSucc 8847125320926933431), (Int.ofNat 50623273871240400)], [(Int.ofNat 0), (Int.ofNat 257602282071718056), (Int.ofNat 7305642711275092188), (Int.ofNat 4360483867458691770), (Int.ofNat 12481214713583997708), (Int.ofNat 21078322004426822514), (Int.negSucc 3185491980526439327), (Int.ofNat 16570228413517300656), (Int.ofNat 6609775341507485760), (Int.ofNat 452126637132062616)], [(Int.ofNat 0), (Int.negSucc 14994135989726111), (Int.negSucc 1143501102654943319), (Int.negSucc 3085086252218192027), (Int.ofNat 1875928254888684060), (Int.negSucc 7873083488105389511), (Int.ofNat 2281215404630338992), (Int.negSucc 1517012199342498239), (Int.negSucc 1579895604947303423), (Int.negSucc 213934151310771455)], [(Int.ofNat 0), (Int.ofNat 354822875067744), (Int.ofNat 99310591917629424), (Int.ofNat 888645193133473638), (Int.negSucc 984824581514510447), (Int.ofNat 1371860494574694624), (Int.negSucc 290600546279779583), (Int.negSucc 84936681531280943), (Int.ofNat 123920030629527552), (Int.ofNat 30578959583483904)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3395468195240831), (Int.negSucc 129775606865777087), (Int.ofNat 155535771599849736), (Int.negSucc 109537856799970319), (Int.ofNat 8508477153733632), (Int.ofNat 19755827348956416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8123210956093824), (Int.negSucc 10182343306100543), (Int.ofNat 3190859986392216)]]

theorem h0n131_arithmetic_row0 :
    (BiPoly.mul h0p45 h0p14).getD 0 []=h0p131.getD 0 [] := by
  decide +kernel

theorem h0n131_arithmetic_row1 :
    (BiPoly.mul h0p45 h0p14).getD 1 []=h0p131.getD 1 [] := by
  decide +kernel

theorem h0n131_arithmetic_row2 :
    (BiPoly.mul h0p45 h0p14).getD 2 []=h0p131.getD 2 [] := by
  decide +kernel

theorem h0n131_arithmetic_row3 :
    (BiPoly.mul h0p45 h0p14).getD 3 []=h0p131.getD 3 [] := by
  decide +kernel

theorem h0n131_arithmetic_row4 :
    (BiPoly.mul h0p45 h0p14).getD 4 []=h0p131.getD 4 [] := by
  decide +kernel

theorem h0n131_arithmetic_row5 :
    (BiPoly.mul h0p45 h0p14).getD 5 []=h0p131.getD 5 [] := by
  decide +kernel

theorem h0n131_arithmetic_row6 :
    (BiPoly.mul h0p45 h0p14).getD 6 []=h0p131.getD 6 [] := by
  decide +kernel

theorem h0n131_arithmetic_row7 :
    (BiPoly.mul h0p45 h0p14).getD 7 []=h0p131.getD 7 [] := by
  decide +kernel

theorem h0n131_arithmetic_row8 :
    (BiPoly.mul h0p45 h0p14).getD 8 []=h0p131.getD 8 [] := by
  decide +kernel

theorem h0n131_arithmetic_row9 :
    (BiPoly.mul h0p45 h0p14).getD 9 []=h0p131.getD 9 [] := by
  decide +kernel

theorem h0n131_arithmetic_row10 :
    (BiPoly.mul h0p45 h0p14).getD 10 []=h0p131.getD 10 [] := by
  decide +kernel

theorem h0n131_arithmetic_row11 :
    (BiPoly.mul h0p45 h0p14).getD 11 []=h0p131.getD 11 [] := by
  decide +kernel

theorem h0n131_arithmetic_row12 :
    (BiPoly.mul h0p45 h0p14).getD 12 []=h0p131.getD 12 [] := by
  decide +kernel

theorem h0n131_arithmetic_row13 :
    (BiPoly.mul h0p45 h0p14).getD 13 []=h0p131.getD 13 [] := by
  decide +kernel

theorem h0n131_arithmetic_row14 :
    (BiPoly.mul h0p45 h0p14).getD 14 []=h0p131.getD 14 [] := by
  decide +kernel

theorem h0n131_arithmetic_row15 :
    (BiPoly.mul h0p45 h0p14).getD 15 []=h0p131.getD 15 [] := by
  decide +kernel

theorem h0n131_arithmetic_row16 :
    (BiPoly.mul h0p45 h0p14).getD 16 []=h0p131.getD 16 [] := by
  decide +kernel

theorem h0n131_arithmetic_row17 :
    (BiPoly.mul h0p45 h0p14).getD 17 []=h0p131.getD 17 [] := by
  decide +kernel

theorem h0n131_arithmetic_row18 :
    (BiPoly.mul h0p45 h0p14).getD 18 []=h0p131.getD 18 [] := by
  decide +kernel

theorem h0n131_arithmetic : BiPoly.mul h0p45 h0p14=h0p131 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p45 h0p14).getD j.val []=h0p131.getD j.val [] :=
      (fun j => Fin.cases h0n131_arithmetic_row0 (fun j => Fin.cases h0n131_arithmetic_row1 (fun j => Fin.cases h0n131_arithmetic_row2 (fun j => Fin.cases h0n131_arithmetic_row3 (fun j => Fin.cases h0n131_arithmetic_row4 (fun j => Fin.cases h0n131_arithmetic_row5 (fun j => Fin.cases h0n131_arithmetic_row6 (fun j => Fin.cases h0n131_arithmetic_row7 (fun j => Fin.cases h0n131_arithmetic_row8 (fun j => Fin.cases h0n131_arithmetic_row9 (fun j => Fin.cases h0n131_arithmetic_row10 (fun j => Fin.cases h0n131_arithmetic_row11 (fun j => Fin.cases h0n131_arithmetic_row12 (fun j => Fin.cases h0n131_arithmetic_row13 (fun j => Fin.cases h0n131_arithmetic_row14 (fun j => Fin.cases h0n131_arithmetic_row15 (fun j => Fin.cases h0n131_arithmetic_row16 (fun j => Fin.cases h0n131_arithmetic_row17 (fun j => Fin.cases h0n131_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n131 : h0e131.toBi mapPolyEnv=h0p131 := by
  change BiPoly.mul (h0e45.toBi mapPolyEnv) (h0e14.toBi mapPolyEnv)=h0p131
  rw [h0n45, h0n14]
  exact h0n131_arithmetic

#print axioms h0n131_arithmetic
end StackSorting.RationalLift
