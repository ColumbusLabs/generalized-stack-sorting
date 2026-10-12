import BivariateRowEquality
import Horner1Node020
import Horner1Node124
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p125 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 84664928592000), (Int.ofNat 483997379447880), (Int.ofNat 570530001928320), (Int.negSucc 293781600442799), (Int.negSucc 786488331839039), (Int.negSucc 321509180323799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 935955106894079), (Int.negSucc 5016884002670015), (Int.negSucc 5118175242630935), (Int.ofNat 3202527421123344), (Int.ofNat 6603369512635872), (Int.ofNat 2406537323183088), (Int.ofNat 42941578525560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4766542568971200), (Int.ofNat 24336932633342730), (Int.ofNat 22712799603630636), (Int.negSucc 13223099157824681), (Int.negSucc 25615857984909767), (Int.negSucc 10682594848108889), (Int.negSucc 1493090860404419), (Int.ofNat 110298851153370)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14815755228559679), (Int.negSucc 73712445074102321), (Int.negSucc 68331645458657999), (Int.ofNat 25772461232808294), (Int.ofNat 62205203463869088), (Int.ofNat 35311466218774842), (Int.ofNat 8641203585383232), (Int.negSucc 574984726742429), (Int.ofNat 2289543395040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 31387012598897640), (Int.ofNat 156867038323198632), (Int.ofNat 157860363957670494), (Int.negSucc 11711748973901129), (Int.negSucc 104376708154973897), (Int.negSucc 85104544578400187), (Int.negSucc 26759976340274909), (Int.negSucc 872334234220121), (Int.ofNat 267812662295970), (Int.negSucc 10903375620719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 47919416876629919), (Int.negSucc 249833993483645060), (Int.negSucc 292611978745662830), (Int.negSucc 70579425759486926), (Int.ofNat 117112188985285665), (Int.ofNat 145551265266863145), (Int.ofNat 57894211469702883), (Int.ofNat 10517060151948903), (Int.negSucc 1381708175562380), (Int.ofNat 68333705996820), (Int.negSucc 1599006752639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 54347287500750600), (Int.ofNat 308689058797707871), (Int.ofNat 438225599650841966), (Int.ofNat 230977694556815247), (Int.negSucc 58777168825546901), (Int.negSucc 170567695350222836), (Int.negSucc 95468665569112601), (Int.negSucc 29759640107009788), (Int.ofNat 1009553432176238), (Int.ofNat 72247253143440), (Int.negSucc 1841377880935), (Int.ofNat 8240487200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 46494278258100479), (Int.negSucc 301376639245997893), (Int.negSucc 529034075534997586), (Int.negSucc 416314270275717981), (Int.negSucc 78329576264490627), (Int.ofNat 117146825157288053), (Int.ofNat 118570420336201937), (Int.ofNat 47216847370525302), (Int.ofNat 6031506084040554), (Int.negSucc 842911468988590), (Int.ofNat 32142144604460), (Int.negSucc 295262912559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 30138036172038480), (Int.ofNat 233681463401937328), (Int.ofNat 513973749017546377), (Int.ofNat 534852751310814013), (Int.ofNat 244496495967264493), (Int.ofNat 3208203506001538), (Int.negSucc 98622455716590652), (Int.negSucc 50126514361536444), (Int.negSucc 17278499860346394), (Int.ofNat 822242105260520), (Int.ofNat 8671916445522), (Int.negSucc 721713381839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14724885620111039), (Int.negSucc 143119162714271621), (Int.negSucc 401099321321129397), (Int.negSucc 525532800458662259), (Int.negSucc 359464406379773980), (Int.negSucc 125210235953513334), (Int.ofNat 29785618321092960), (Int.ofNat 37942092427713913), (Int.ofNat 20660315283604510), (Int.ofNat 1985795876341326), (Int.negSucc 206876081711506), (Int.ofNat 3763063929640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5336341880443920), (Int.ofNat 68251305378980596), (Int.ofNat 249962038170837916), (Int.ofNat 405986414669793980), (Int.ofNat 369578848741676277), (Int.ofNat 190545661293173184), (Int.ofNat 48600257840787916), (Int.negSucc 15612039024925310), (Int.negSucc 12122468080586708), (Int.negSucc 5071578474982350), (Int.ofNat 113551790653708), (Int.ofNat 6239133617530)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1390715897853119), (Int.negSucc 24763201515819289), (Int.negSucc 122838570532959229), (Int.negSucc 249246234673159981), (Int.negSucc 286828392852195591), (Int.negSucc 188163560662304745), (Int.negSucc 87586377345660219), (Int.negSucc 10387273169325274), (Int.ofNat 1460474616822610), (Int.ofNat 4186309824637975), (Int.ofNat 412787232809757), (Int.negSucc 17771548352654)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 246361893355080), (Int.ofNat 6602855911428084), (Int.ofNat 46626411525113996), (Int.ofNat 121481558724365052), (Int.ofNat 171981946802552332), (Int.ofNat 141302298356545780), (Int.ofNat 80142398678746170), (Int.ofNat 26792896165153105), (Int.ofNat 4309646124928413), (Int.negSucc 676648234832897), (Int.negSucc 595849322394352), (Int.negSucc 14122349698589)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26554769373599), (Int.negSucc 1226135558945500), (Int.negSucc 13264266157393186), (Int.negSucc 46415870504135598), (Int.negSucc 80234741227811704), (Int.negSucc 82745653061108122), (Int.negSucc 52699659331775258), (Int.negSucc 26035845654248825), (Int.negSucc 6114784231943780), (Int.negSucc 1403081617229396), (Int.ofNat 196721300426184), (Int.ofNat 35060545030410)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1314214473000), (Int.ofNat 144607548048235), (Int.ofNat 2709316392127714), (Int.ofNat 13573029956568763), (Int.ofNat 29040459959493960), (Int.ofNat 37411649776477605), (Int.ofNat 27512061378716946), (Int.ofNat 15977564237226474), (Int.ofNat 5325265170123723), (Int.ofNat 1466372694960018), (Int.ofNat 144237108975660), (Int.negSucc 3431713838039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8960231326149), (Int.negSucc 372324712264574), (Int.negSucc 2933448030094049), (Int.negSucc 8051706423757675), (Int.negSucc 12791800307981906), (Int.negSucc 11586180543518672), (Int.negSucc 7062420149412452), (Int.negSucc 3170910424780511), (Int.negSucc 874011416678801), (Int.negSucc 176715993262931), (Int.negSucc 17831904918299)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 162452686500), (Int.ofNat 30701570174325), (Int.ofNat 445528802819169), (Int.ofNat 1677598507912833), (Int.ofNat 3208919136352578), (Int.ofNat 3808684711691793), (Int.ofNat 2419004392291566), (Int.ofNat 1318263904718928), (Int.ofNat 375353279406720), (Int.ofNat 97190916870924), (Int.ofNat 9974929773960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1152184175999), (Int.negSucc 43387252550549), (Int.negSucc 256797420691994), (Int.negSucc 571120396293266), (Int.negSucc 910421389628351), (Int.negSucc 674791475524073), (Int.negSucc 381658210313111), (Int.negSucc 123996881208167), (Int.negSucc 32372105748767), (Int.negSucc 1869472765079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2100010868100), (Int.ofNat 27301100182065), (Int.ofNat 72711889246134), (Int.ofNat 140103881567172), (Int.ofNat 152014592092824), (Int.ofNat 75870302374728), (Int.ofNat 32171323822272), (Int.ofNat 5640749719344), (Int.ofNat 115651359360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1569174881399), (Int.negSucc 7332775411013), (Int.negSucc 11593880665523), (Int.negSucc 23371546580747), (Int.negSucc 11618878632479), (Int.negSucc 5453145675071), (Int.negSucc 373007021759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 509189762160), (Int.ofNat 585800019324), (Int.ofNat 1554071253336), (Int.ofNat 1652988172752), (Int.ofNat 399059965440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 59607822239), (Int.ofNat 28880548056), (Int.negSucc 141704303039)]]

theorem h1n125_arithmetic_row0 :
    (BiPoly.mul h1p20 h1p124).getD 0 []=h1p125.getD 0 [] := by
  decide +kernel

theorem h1n125_arithmetic_row1 :
    (BiPoly.mul h1p20 h1p124).getD 1 []=h1p125.getD 1 [] := by
  decide +kernel

theorem h1n125_arithmetic_row2 :
    (BiPoly.mul h1p20 h1p124).getD 2 []=h1p125.getD 2 [] := by
  decide +kernel

theorem h1n125_arithmetic_row3 :
    (BiPoly.mul h1p20 h1p124).getD 3 []=h1p125.getD 3 [] := by
  decide +kernel

theorem h1n125_arithmetic_row4 :
    (BiPoly.mul h1p20 h1p124).getD 4 []=h1p125.getD 4 [] := by
  decide +kernel

theorem h1n125_arithmetic_row5 :
    (BiPoly.mul h1p20 h1p124).getD 5 []=h1p125.getD 5 [] := by
  decide +kernel

theorem h1n125_arithmetic_row6 :
    (BiPoly.mul h1p20 h1p124).getD 6 []=h1p125.getD 6 [] := by
  decide +kernel

theorem h1n125_arithmetic_row7 :
    (BiPoly.mul h1p20 h1p124).getD 7 []=h1p125.getD 7 [] := by
  decide +kernel

theorem h1n125_arithmetic_row8 :
    (BiPoly.mul h1p20 h1p124).getD 8 []=h1p125.getD 8 [] := by
  decide +kernel

theorem h1n125_arithmetic_row9 :
    (BiPoly.mul h1p20 h1p124).getD 9 []=h1p125.getD 9 [] := by
  decide +kernel

theorem h1n125_arithmetic_row10 :
    (BiPoly.mul h1p20 h1p124).getD 10 []=h1p125.getD 10 [] := by
  decide +kernel

theorem h1n125_arithmetic_row11 :
    (BiPoly.mul h1p20 h1p124).getD 11 []=h1p125.getD 11 [] := by
  decide +kernel

theorem h1n125_arithmetic_row12 :
    (BiPoly.mul h1p20 h1p124).getD 12 []=h1p125.getD 12 [] := by
  decide +kernel

theorem h1n125_arithmetic_row13 :
    (BiPoly.mul h1p20 h1p124).getD 13 []=h1p125.getD 13 [] := by
  decide +kernel

theorem h1n125_arithmetic_row14 :
    (BiPoly.mul h1p20 h1p124).getD 14 []=h1p125.getD 14 [] := by
  decide +kernel

theorem h1n125_arithmetic_row15 :
    (BiPoly.mul h1p20 h1p124).getD 15 []=h1p125.getD 15 [] := by
  decide +kernel

theorem h1n125_arithmetic_row16 :
    (BiPoly.mul h1p20 h1p124).getD 16 []=h1p125.getD 16 [] := by
  decide +kernel

theorem h1n125_arithmetic_row17 :
    (BiPoly.mul h1p20 h1p124).getD 17 []=h1p125.getD 17 [] := by
  decide +kernel

theorem h1n125_arithmetic_row18 :
    (BiPoly.mul h1p20 h1p124).getD 18 []=h1p125.getD 18 [] := by
  decide +kernel

theorem h1n125_arithmetic_row19 :
    (BiPoly.mul h1p20 h1p124).getD 19 []=h1p125.getD 19 [] := by
  decide +kernel

theorem h1n125_arithmetic_row20 :
    (BiPoly.mul h1p20 h1p124).getD 20 []=h1p125.getD 20 [] := by
  decide +kernel

theorem h1n125_arithmetic_row21 :
    (BiPoly.mul h1p20 h1p124).getD 21 []=h1p125.getD 21 [] := by
  decide +kernel

theorem h1n125_arithmetic : BiPoly.mul h1p20 h1p124=h1p125 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p20 h1p124).getD j.val []=h1p125.getD j.val [] :=
      (fun j => Fin.cases h1n125_arithmetic_row0 (fun j => Fin.cases h1n125_arithmetic_row1 (fun j => Fin.cases h1n125_arithmetic_row2 (fun j => Fin.cases h1n125_arithmetic_row3 (fun j => Fin.cases h1n125_arithmetic_row4 (fun j => Fin.cases h1n125_arithmetic_row5 (fun j => Fin.cases h1n125_arithmetic_row6 (fun j => Fin.cases h1n125_arithmetic_row7 (fun j => Fin.cases h1n125_arithmetic_row8 (fun j => Fin.cases h1n125_arithmetic_row9 (fun j => Fin.cases h1n125_arithmetic_row10 (fun j => Fin.cases h1n125_arithmetic_row11 (fun j => Fin.cases h1n125_arithmetic_row12 (fun j => Fin.cases h1n125_arithmetic_row13 (fun j => Fin.cases h1n125_arithmetic_row14 (fun j => Fin.cases h1n125_arithmetic_row15 (fun j => Fin.cases h1n125_arithmetic_row16 (fun j => Fin.cases h1n125_arithmetic_row17 (fun j => Fin.cases h1n125_arithmetic_row18 (fun j => Fin.cases h1n125_arithmetic_row19 (fun j => Fin.cases h1n125_arithmetic_row20 (fun j => Fin.cases h1n125_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n125 : h1e125.toBi mapPolyEnv=h1p125 := by
  change BiPoly.mul (h1e20.toBi mapPolyEnv) (h1e124.toBi mapPolyEnv)=h1p125
  rw [h1n20, h1n124]
  exact h1n125_arithmetic

#print axioms h1n125_arithmetic
end StackSorting.RationalLift
