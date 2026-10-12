import BivariateRowEquality
import Horner1Base
import Horner1Node066
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p75 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 133791492096000), (Int.ofNat 742164968309760), (Int.negSucc 108043432312319), (Int.negSucc 4035626816924159), (Int.negSucc 235143031933439), (Int.ofNat 3084066876464640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1464019596311039), (Int.negSucc 7155420733847807), (Int.ofNat 4658320825125120), (Int.ofNat 40288668082569216), (Int.negSucc 7248927372788735), (Int.negSucc 25969195618603775), (Int.ofNat 1759358736361728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7373304531751680), (Int.ofNat 31466279787739776), (Int.negSucc 36166805615586815), (Int.negSucc 178101971217745919), (Int.ofNat 57232782125849088), (Int.ofNat 86396739297899904), (Int.ofNat 1294051565875968), (Int.negSucc 268020661390847)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 22641245323770239), (Int.negSucc 83591195647133375), (Int.ofNat 136751414345540352), (Int.ofNat 469866436507385280), (Int.negSucc 147941026482741119), (Int.negSucc 161255683130803775), (Int.negSucc 69749264880534527), (Int.ofNat 9623071573128000), (Int.negSucc 388292589305855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 47330390880936000), (Int.ofNat 149844602628426528), (Int.negSucc 315268143765898175), (Int.negSucc 850350227180283359), (Int.ofNat 74804390316538560), (Int.ofNat 244171385097706080), (Int.ofNat 270238480016001984), (Int.negSucc 29896487908046495), (Int.ofNat 2150473556671488), (Int.negSucc 98010216456191)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 71211303953740799), (Int.negSucc 191945227113699839), (Int.ofNat 488660475278787648), (Int.ofNat 1172276122677230400), (Int.ofNat 463445958403729152), (Int.negSucc 385450327017992063), (Int.negSucc 466324479169248191), (Int.negSucc 37326108045409727), (Int.ofNat 8156513217153408), (Int.negSucc 228404283839999), (Int.negSucc 9316972498943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 79474353231856320), (Int.ofNat 181795979630489184), (Int.negSucc 538078829412172703), (Int.negSucc 1351690852128433727), (Int.negSucc 1363104780538805279), (Int.ofNat 404934139308490080), (Int.ofNat 437874180746509344), (Int.ofNat 302548002567794688), (Int.negSucc 43331795661929759), (Int.ofNat 3052956635587584), (Int.negSucc 95460291907583), (Int.negSucc 259406045183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 66795625049392639), (Int.negSucc 130272797736021247), (Int.ofNat 439330516461689280), (Int.ofNat 1381190075458723200), (Int.ofNat 2029203354236116416), (Int.ofNat 128737513045120512), (Int.negSucc 289072260329665855), (Int.negSucc 533730523889003839), (Int.ofNat 11602850012094528), (Int.ofNat 1764713734611520), (Int.ofNat 54146327841280), (Int.negSucc 6053933104127)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 42458664288782720), (Int.ofNat 71926763800211648), (Int.negSucc 280488131026468671), (Int.negSucc 1245576465373932319), (Int.negSucc 2052901403636320735), (Int.negSucc 1134964989395476735), (Int.ofNat 170688529112777664), (Int.ofNat 382550250590352960), (Int.ofNat 178072432864918368), (Int.negSucc 25176248148997087), (Int.ofNat 1418951197459072), (Int.negSucc 23693335963135)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 20301040793299199), (Int.negSucc 31097164853128063), (Int.ofNat 151825434593407936), (Int.ofNat 951803828373730752), (Int.ofNat 1620717445719520320), (Int.ofNat 1806586305204594624), (Int.ofNat 140336261742107136), (Int.negSucc 39086878622892415), (Int.negSucc 314717226084914239), (Int.ofNat 15211480070931264), (Int.negSucc 190697833885951), (Int.ofNat 33558159048448)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7183544709731200), (Int.ofNat 10650809041307840), (Int.negSucc 75781366661934847), (Int.negSucc 594901627987523455), (Int.negSucc 1114350230158512127), (Int.negSucc 1646592377570712767), (Int.negSucc 671817266970367167), (Int.negSucc 117236240288891135), (Int.ofNat 167094879564378016), (Int.ofNat 62920105620991520), (Int.negSucc 7108585767958751), (Int.ofNat 237783125116288)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1823351676158079), (Int.negSucc 2879300905048895), (Int.ofNat 35015274673166784), (Int.ofNat 298779029228505216), (Int.ofNat 698291850441634752), (Int.ofNat 1032505931045429184), (Int.ofNat 943029345374651520), (Int.ofNat 167766617292475840), (Int.ofNat 59698587802228480), (Int.negSucc 100055084304450687), (Int.ofNat 3986862935178624), (Int.negSucc 47729976648959)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 313715052432960), (Int.ofNat 592991087400992), (Int.negSucc 13651121373862143), (Int.negSucc 119399071131246623), (Int.negSucc 380472353727831487), (Int.negSucc 518522721665029471), (Int.negSucc 726766416508349759), (Int.negSucc 263710898862870815), (Int.negSucc 111875838605493599), (Int.ofNat 31833286333069056), (Int.ofNat 13038892266254592), (Int.negSucc 819482627334143)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 32741373159679), (Int.negSucc 85625413767551), (Int.ofNat 4014640803937280), (Int.ofNat 37343195384568704), (Int.ofNat 165763499688622464), (Int.ofNat 244805284678178752), (Int.ofNat 351103670182178112), (Int.ofNat 280489110594898560), (Int.ofNat 72571151936692800), (Int.ofNat 33179795920490496), (Int.negSucc 15457295153464127), (Int.ofNat 230130198458112)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1563578244800), (Int.ofNat 7412208555616), (Int.negSucc 805302243217759), (Int.negSucc 8811184322863167), (Int.negSucc 53729221904708255), (Int.negSucc 109491720840947039), (Int.negSucc 122032794469252511), (Int.negSucc 170031899128839935), (Int.negSucc 57221659484084159), (Int.negSucc 31295866976158271), (Int.ofNat 958768383710592), (Int.ofNat 1164580139206656)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 270749794559), (Int.ofNat 96917990689920), (Int.ofNat 1462827952008000), (Int.ofNat 12152215930341504), (Int.ofNat 39416245290813696), (Int.ofNat 40446716024894208), (Int.ofNat 58880314286237184), (Int.ofNat 43527190568169600), (Int.ofNat 12343968072321408), (Int.ofNat 6046932697937280), (Int.negSucc 793286744984063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5251440890879), (Int.negSucc 150223128434399), (Int.negSucc 1766493333653663), (Int.negSucc 9727302800585855), (Int.negSucc 14460406666107263), (Int.negSucc 12633192709877375), (Int.negSucc 19076875430752511), (Int.negSucc 5687051892344063), (Int.negSucc 3227755314544127), (Int.negSucc 210967152500735)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7065622666368), (Int.ofNat 142532811276480), (Int.ofNat 1438341359652864), (Int.ofNat 4070970298097856), (Int.ofNat 2723664283824384), (Int.ofNat 4089372544101888), (Int.ofNat 2985712786003968), (Int.ofNat 720147164265216), (Int.ofNat 318468583996416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4449486333887), (Int.negSucc 103522005453887), (Int.negSucc 665827269312383), (Int.negSucc 805180401054719), (Int.negSucc 387027641445119), (Int.negSucc 821629020172031), (Int.negSucc 182741892258815), (Int.negSucc 90330288445439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1888841255040), (Int.ofNat 47699950260096), (Int.ofNat 156211329074688), (Int.ofNat 50865758666496), (Int.ofNat 75360162295296), (Int.ofNat 59670496488960), (Int.ofNat 7557562828800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 536016413951), (Int.negSucc 11598588474623), (Int.negSucc 14446757680127), (Int.ofNat 1815093826560), (Int.negSucc 7557562828799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 67826253312), (Int.ofNat 1133634424320)]]

theorem h1n75_arithmetic_row0 :
    (BiPoly.mul h1p74 h1p66).getD 0 []=h1p75.getD 0 [] := by
  decide +kernel

theorem h1n75_arithmetic_row1 :
    (BiPoly.mul h1p74 h1p66).getD 1 []=h1p75.getD 1 [] := by
  decide +kernel

theorem h1n75_arithmetic_row2 :
    (BiPoly.mul h1p74 h1p66).getD 2 []=h1p75.getD 2 [] := by
  decide +kernel

theorem h1n75_arithmetic_row3 :
    (BiPoly.mul h1p74 h1p66).getD 3 []=h1p75.getD 3 [] := by
  decide +kernel

theorem h1n75_arithmetic_row4 :
    (BiPoly.mul h1p74 h1p66).getD 4 []=h1p75.getD 4 [] := by
  decide +kernel

theorem h1n75_arithmetic_row5 :
    (BiPoly.mul h1p74 h1p66).getD 5 []=h1p75.getD 5 [] := by
  decide +kernel

theorem h1n75_arithmetic_row6 :
    (BiPoly.mul h1p74 h1p66).getD 6 []=h1p75.getD 6 [] := by
  decide +kernel

theorem h1n75_arithmetic_row7 :
    (BiPoly.mul h1p74 h1p66).getD 7 []=h1p75.getD 7 [] := by
  decide +kernel

theorem h1n75_arithmetic_row8 :
    (BiPoly.mul h1p74 h1p66).getD 8 []=h1p75.getD 8 [] := by
  decide +kernel

theorem h1n75_arithmetic_row9 :
    (BiPoly.mul h1p74 h1p66).getD 9 []=h1p75.getD 9 [] := by
  decide +kernel

theorem h1n75_arithmetic_row10 :
    (BiPoly.mul h1p74 h1p66).getD 10 []=h1p75.getD 10 [] := by
  decide +kernel

theorem h1n75_arithmetic_row11 :
    (BiPoly.mul h1p74 h1p66).getD 11 []=h1p75.getD 11 [] := by
  decide +kernel

theorem h1n75_arithmetic_row12 :
    (BiPoly.mul h1p74 h1p66).getD 12 []=h1p75.getD 12 [] := by
  decide +kernel

theorem h1n75_arithmetic_row13 :
    (BiPoly.mul h1p74 h1p66).getD 13 []=h1p75.getD 13 [] := by
  decide +kernel

theorem h1n75_arithmetic_row14 :
    (BiPoly.mul h1p74 h1p66).getD 14 []=h1p75.getD 14 [] := by
  decide +kernel

theorem h1n75_arithmetic_row15 :
    (BiPoly.mul h1p74 h1p66).getD 15 []=h1p75.getD 15 [] := by
  decide +kernel

theorem h1n75_arithmetic_row16 :
    (BiPoly.mul h1p74 h1p66).getD 16 []=h1p75.getD 16 [] := by
  decide +kernel

theorem h1n75_arithmetic_row17 :
    (BiPoly.mul h1p74 h1p66).getD 17 []=h1p75.getD 17 [] := by
  decide +kernel

theorem h1n75_arithmetic_row18 :
    (BiPoly.mul h1p74 h1p66).getD 18 []=h1p75.getD 18 [] := by
  decide +kernel

theorem h1n75_arithmetic_row19 :
    (BiPoly.mul h1p74 h1p66).getD 19 []=h1p75.getD 19 [] := by
  decide +kernel

theorem h1n75_arithmetic_row20 :
    (BiPoly.mul h1p74 h1p66).getD 20 []=h1p75.getD 20 [] := by
  decide +kernel

theorem h1n75_arithmetic_row21 :
    (BiPoly.mul h1p74 h1p66).getD 21 []=h1p75.getD 21 [] := by
  decide +kernel

theorem h1n75_arithmetic : BiPoly.mul h1p74 h1p66=h1p75 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p74 h1p66).getD j.val []=h1p75.getD j.val [] :=
      (fun j => Fin.cases h1n75_arithmetic_row0 (fun j => Fin.cases h1n75_arithmetic_row1 (fun j => Fin.cases h1n75_arithmetic_row2 (fun j => Fin.cases h1n75_arithmetic_row3 (fun j => Fin.cases h1n75_arithmetic_row4 (fun j => Fin.cases h1n75_arithmetic_row5 (fun j => Fin.cases h1n75_arithmetic_row6 (fun j => Fin.cases h1n75_arithmetic_row7 (fun j => Fin.cases h1n75_arithmetic_row8 (fun j => Fin.cases h1n75_arithmetic_row9 (fun j => Fin.cases h1n75_arithmetic_row10 (fun j => Fin.cases h1n75_arithmetic_row11 (fun j => Fin.cases h1n75_arithmetic_row12 (fun j => Fin.cases h1n75_arithmetic_row13 (fun j => Fin.cases h1n75_arithmetic_row14 (fun j => Fin.cases h1n75_arithmetic_row15 (fun j => Fin.cases h1n75_arithmetic_row16 (fun j => Fin.cases h1n75_arithmetic_row17 (fun j => Fin.cases h1n75_arithmetic_row18 (fun j => Fin.cases h1n75_arithmetic_row19 (fun j => Fin.cases h1n75_arithmetic_row20 (fun j => Fin.cases h1n75_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n75 : h1e75.toBi mapPolyEnv=h1p75 := by
  change BiPoly.mul (h1e74.toBi mapPolyEnv) (h1e66.toBi mapPolyEnv)=h1p75
  rw [h1n74, h1n66]
  exact h1n75_arithmetic

#print axioms h1n75_arithmetic
end StackSorting.RationalLift
