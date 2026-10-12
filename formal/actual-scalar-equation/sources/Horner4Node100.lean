import BivariateRowEquality
import Horner4Base
import Horner4Node099
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p100 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 2601878685156000000), (Int.ofNat 13246209505916244000), (Int.negSucc 8165439497526726959), (Int.negSucc 53152805129642004239), (Int.ofNat 89837432182117586160), (Int.negSucc 42455715940664888399)], [(Int.ofNat 0), (Int.negSucc 22642126513490879999), (Int.negSucc 108289626372103858559), (Int.ofNat 96169738461872987808), (Int.ofNat 442518575247007792848), (Int.negSucc 812401332218417537279), (Int.ofNat 420214791626138354832), (Int.negSucc 30754542972671870399)], [(Int.ofNat 0), (Int.ofNat 89252970493181385600), (Int.ofNat 403217926273548968040), (Int.negSucc 416382149605647756635), (Int.negSucc 1591228469855642555735), (Int.ofNat 3012165339036144792048), (Int.negSucc 1571979246832045869695), (Int.ofNat 154587554239250678076), (Int.negSucc 7210516074860905343)], [(Int.ofNat 0), (Int.negSucc 210640209197080694399), (Int.negSucc 904501225964421527399), (Int.ofNat 905506725314831428044), (Int.ofNat 3267360098531284901688), (Int.negSucc 5688729338381729860319), (Int.ofNat 2465533366171039900440), (Int.negSucc 56438440526854812059), (Int.ofNat 3487761397434019896), (Int.negSucc 529688963816255231)], [(Int.ofNat 0), (Int.ofNat 331353352528790605200), (Int.ofNat 1360407497948148956760), (Int.negSucc 995984192858584042367), (Int.negSucc 4179760146445530648743), (Int.ofNat 4935345669765579492720), (Int.ofNat 20630479412098176912), (Int.negSucc 1103947494094267007543), (Int.ofNat 98066107044781343208), (Int.negSucc 2809188958188677039), (Int.ofNat 2823107883298560)], [(Int.ofNat 0), (Int.negSucc 365912130175591953599), (Int.negSucc 1441316173359017098619), (Int.ofNat 211143213482675722470), (Int.ofNat 3218899666781663222814), (Int.ofNat 967574899742361376212), (Int.negSucc 5796930620312307877607), (Int.ofNat 2652738352573469112558), (Int.negSucc 159418824073361272025), (Int.ofNat 4578929397806856048), (Int.negSucc 92244783985761887)], [(Int.ofNat 0), (Int.ofNat 290810428792352092800), (Int.ofNat 1095572899651871145780), (Int.ofNat 953583767100369740106), (Int.negSucc 897832670374691017847), (Int.negSucc 6939053851749160319423), (Int.ofNat 8080956755339694367428), (Int.negSucc 1516195656624172566185), (Int.negSucc 298480443884239975055), (Int.ofNat 23327372227674380148), (Int.negSucc 550271642718933791)], [(Int.ofNat 0), (Int.negSucc 167594561195672635199), (Int.negSucc 592826658881274729899), (Int.negSucc 1496809664229165660413), (Int.negSucc 1108582754432638053725), (Int.ofNat 7043743600165902792816), (Int.negSucc 2771056596015905577803), (Int.negSucc 2451770784948420357245), (Int.ofNat 946783043178595775982), (Int.negSucc 36129739625478229247), (Int.negSucc 18217147678435295)], [(Int.ofNat 0), (Int.ofNat 69520803105328754400), (Int.ofNat 218149172288893551420), (Int.ofNat 1161743379700990410162), (Int.ofNat 1695345916535006353308), (Int.negSucc 2529717077107961821007), (Int.negSucc 3885989714147929629347), (Int.ofNat 4192287025915448606718), (Int.negSucc 529373000993712443171), (Int.negSucc 56739610570044132215), (Int.ofNat 2964735403362554184)], [(Int.ofNat 0), (Int.negSucc 20250684413498779199), (Int.negSucc 46899236949188706539), (Int.negSucc 532309991954918295581), (Int.negSucc 1161515319500886151895), (Int.negSucc 1109662414635779278847), (Int.ofNat 4856696316046266640038), (Int.negSucc 1545231202252105547735), (Int.negSucc 673971993556940183093), (Int.ofNat 134094998809452124332), (Int.ofNat 111899059519428558)], [(Int.ofNat 0), (Int.ofNat 3934101484707897600), (Int.ofNat 1551152587195036980), (Int.ofNat 131233929948065416518), (Int.ofNat 447105603894634276254), (Int.ofNat 1658062820427289580898), (Int.negSucc 1795776624536977879271), (Int.negSucc 1334494657711342212407), (Int.ofNat 940346059944397823118), (Int.negSucc 26350163297932998077), (Int.negSucc 6552857178790710875)], [(Int.ofNat 0), (Int.negSucc 458012658724948799), (Int.ofNat 2285970015249524340), (Int.negSucc 3752082663990310061), (Int.negSucc 72410390999568901205), (Int.negSucc 776218719674254049315), (Int.negSucc 390211252615354065731), (Int.ofNat 1481616279187077653064), (Int.negSucc 188782443792698156315), (Int.negSucc 103815464660207551403), (Int.ofNat 2853958844689728732)], [(Int.ofNat 0), (Int.ofNat 24189064543155600), (Int.negSucc 676474923470378579), (Int.negSucc 8258320754343608705), (Int.negSucc 15499420288836145631), (Int.ofNat 142454866775300567136), (Int.ofNat 594339933485881621080), (Int.negSucc 412821769703382373139), (Int.negSucc 291563476389528070679), (Int.ofNat 72217477209691738620), (Int.ofNat 4550163175905974820)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 82156249184453640), (Int.ofNat 2617957984980788280), (Int.ofNat 10972557779536800414), (Int.ofNat 18758674542655950948), (Int.negSucc 209866436619319946681), (Int.negSucc 102997146454228523735), (Int.ofNat 195986401780806514368), (Int.ofNat 10074635535783804696), (Int.negSucc 3830746312873352663)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3588070531581359), (Int.negSucc 356087328932051891), (Int.negSucc 2470766109393729473), (Int.negSucc 14880362602518891053), (Int.ofNat 22723961512561318548), (Int.ofNat 93760599604644473472), (Int.negSucc 27171085025387955239), (Int.negSucc 25458322979483211815), (Int.negSucc 143338123557731375)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19216899321959232), (Int.ofNat 261004131285275016), (Int.ofNat 2952685702461264012), (Int.ofNat 4551039733207688748), (Int.negSucc 21747164020238927015), (Int.negSucc 13210477631601524999), (Int.ofNat 8057472104294859744), (Int.ofNat 1079996165335153296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10679763589413839), (Int.negSucc 237201998565140099), (Int.negSucc 1501381392969023675), (Int.ofNat 1298220303679801560), (Int.ofNat 5403716596360828224), (Int.ofNat 25406366261218128), (Int.negSucc 402012425897977391)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4494194472196800), (Int.ofNat 128194924712242608), (Int.ofNat 196279368700423680), (Int.negSucc 664453136175639983), (Int.negSucc 388698193624255487), (Int.ofNat 46834405789144320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1444249846617407), (Int.negSucc 23062543367825231), (Int.ofNat 20851209566431920), (Int.ofNat 47820714973070400)]]

theorem h4n100_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p99).getD 0 []=h4p100.getD 0 [] := by
  decide +kernel

theorem h4n100_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p99).getD 1 []=h4p100.getD 1 [] := by
  decide +kernel

theorem h4n100_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p99).getD 2 []=h4p100.getD 2 [] := by
  decide +kernel

theorem h4n100_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p99).getD 3 []=h4p100.getD 3 [] := by
  decide +kernel

theorem h4n100_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p99).getD 4 []=h4p100.getD 4 [] := by
  decide +kernel

theorem h4n100_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p99).getD 5 []=h4p100.getD 5 [] := by
  decide +kernel

theorem h4n100_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p99).getD 6 []=h4p100.getD 6 [] := by
  decide +kernel

theorem h4n100_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p99).getD 7 []=h4p100.getD 7 [] := by
  decide +kernel

theorem h4n100_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p99).getD 8 []=h4p100.getD 8 [] := by
  decide +kernel

theorem h4n100_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p99).getD 9 []=h4p100.getD 9 [] := by
  decide +kernel

theorem h4n100_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p99).getD 10 []=h4p100.getD 10 [] := by
  decide +kernel

theorem h4n100_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p99).getD 11 []=h4p100.getD 11 [] := by
  decide +kernel

theorem h4n100_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p99).getD 12 []=h4p100.getD 12 [] := by
  decide +kernel

theorem h4n100_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p99).getD 13 []=h4p100.getD 13 [] := by
  decide +kernel

theorem h4n100_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p99).getD 14 []=h4p100.getD 14 [] := by
  decide +kernel

theorem h4n100_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p99).getD 15 []=h4p100.getD 15 [] := by
  decide +kernel

theorem h4n100_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p99).getD 16 []=h4p100.getD 16 [] := by
  decide +kernel

theorem h4n100_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p99).getD 17 []=h4p100.getD 17 [] := by
  decide +kernel

theorem h4n100_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p99).getD 18 []=h4p100.getD 18 [] := by
  decide +kernel

theorem h4n100_arithmetic : BiPoly.mul h4p13 h4p99=h4p100 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p99).getD j.val []=h4p100.getD j.val [] :=
      (fun j => Fin.cases h4n100_arithmetic_row0 (fun j => Fin.cases h4n100_arithmetic_row1 (fun j => Fin.cases h4n100_arithmetic_row2 (fun j => Fin.cases h4n100_arithmetic_row3 (fun j => Fin.cases h4n100_arithmetic_row4 (fun j => Fin.cases h4n100_arithmetic_row5 (fun j => Fin.cases h4n100_arithmetic_row6 (fun j => Fin.cases h4n100_arithmetic_row7 (fun j => Fin.cases h4n100_arithmetic_row8 (fun j => Fin.cases h4n100_arithmetic_row9 (fun j => Fin.cases h4n100_arithmetic_row10 (fun j => Fin.cases h4n100_arithmetic_row11 (fun j => Fin.cases h4n100_arithmetic_row12 (fun j => Fin.cases h4n100_arithmetic_row13 (fun j => Fin.cases h4n100_arithmetic_row14 (fun j => Fin.cases h4n100_arithmetic_row15 (fun j => Fin.cases h4n100_arithmetic_row16 (fun j => Fin.cases h4n100_arithmetic_row17 (fun j => Fin.cases h4n100_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n100 : h4e100.toBi mapPolyEnv=h4p100 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e99.toBi mapPolyEnv)=h4p100
  rw [h4n13, h4n99]
  exact h4n100_arithmetic

#print axioms h4n100_arithmetic
end StackSorting.RationalLift
