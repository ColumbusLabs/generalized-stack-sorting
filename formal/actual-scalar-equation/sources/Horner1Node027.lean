import BivariateRowEquality
import Horner1Node020
import Horner1Node026
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p27 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 677319428736000), (Int.ofNat 3673674610711488), (Int.ofNat 3656601415268352), (Int.negSucc 2541787352207999), (Int.negSucc 4745277651055103), (Int.negSucc 1543244065554239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7487640855152639), (Int.negSucc 37837281416956415), (Int.negSucc 30748141516186943), (Int.ofNat 26784077957506944), (Int.ofNat 38485988068131072), (Int.ofNat 11509528733163648), (Int.ofNat 206119576922688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 38132340551769600), (Int.ofNat 182113585752251952), (Int.ofNat 128813809787204256), (Int.negSucc 107717745133531439), (Int.negSucc 146486190363268031), (Int.negSucc 55489623029462447), (Int.negSucc 6811942374339551), (Int.ofNat 529434485536176)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 118526041828477439), (Int.negSucc 546466588739627759), (Int.negSucc 379343885131995263), (Int.ofNat 208434690327729744), (Int.ofNat 365299476271582464), (Int.ofNat 196177646650395312), (Int.ofNat 39006060128388864), (Int.negSucc 2694111827466383), (Int.ofNat 10989808296192)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 251096100791181120), (Int.ofNat 1150690300061665536), (Int.ofNat 902448240921846288), (Int.negSucc 125749331310805487), (Int.negSucc 662062240174600367), (Int.negSucc 478597119060394079), (Int.negSucc 130351882159073807), (Int.negSucc 3463619324409071), (Int.ofNat 1254107464874352), (Int.negSucc 52336202979455)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 383355335013039359), (Int.negSucc 1812053458084461335), (Int.negSucc 1778735232418945607), (Int.negSucc 388317311690863175), (Int.ofNat 825793937432630712), (Int.ofNat 817747696159440120), (Int.ofNat 315907874144924328), (Int.ofNat 44737633810836360), (Int.negSucc 6280377447116375), (Int.ofNat 317372718342240), (Int.negSucc 7675232412671)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 434778300006004800), (Int.ofNat 2213818355053622280), (Int.ofNat 2840457697291223376), (Int.ofNat 1363621020123704904), (Int.negSucc 504393459031941263), (Int.negSucc 1000799742226237271), (Int.negSucc 553351057755760367), (Int.negSucc 137299888698777815), (Int.ofNat 4806066000928848), (Int.ofNat 360008479486080), (Int.negSucc 9694653777599), (Int.ofNat 39554338560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 371954226064803839), (Int.negSucc 2138658589719520079), (Int.negSucc 3602738852030252327), (Int.negSucc 2511611953400734607), (Int.negSucc 410538105850543967), (Int.ofNat 799721382613274520), (Int.ofNat 682206032676728760), (Int.ofNat 252527967249500880), (Int.ofNat 24740841280702896), (Int.negSucc 3822363648761927), (Int.ofNat 150802539331488), (Int.negSucc 1417261980287)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 241104289376307840), (Int.ofNat 1642619740684790016), (Int.ofNat 3603478248160592376), (Int.ofNat 3345900989819922840), (Int.ofNat 1519490831378892312), (Int.negSucc 149266871115030671), (Int.negSucc 566033886128843351), (Int.negSucc 308567443839677015), (Int.negSucc 77317615085193767), (Int.ofNat 3707949908020224), (Int.ofNat 51732760596720), (Int.negSucc 3464224232831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 117799084960888319), (Int.negSucc 997497474017552207), (Int.negSucc 2837867995531394255), (Int.negSucc 3450597564410356319), (Int.negSucc 2247666862858248407), (Int.negSucc 668005976730272519), (Int.ofNat 219617163374693760), (Int.ofNat 242213108704054392), (Int.ofNat 109297655767421328), (Int.ofNat 8147726930399760), (Int.negSucc 949316545136039), (Int.ofNat 18062706862272)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 42690735043551360), (Int.ofNat 471838233160309728), (Int.ofNat 1754199038822058912), (Int.ofNat 2791745683597259808), (Int.ofNat 2320708938607311768), (Int.ofNat 1187054415525992832), (Int.ofNat 202260406307979936), (Int.negSucc 92470522518687815), (Int.negSucc 84433253120538839), (Int.negSucc 22528048541482631), (Int.ofNat 492612890408544), (Int.ofNat 29947841364144)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11125727182824959), (Int.negSucc 169704570273772463), (Int.negSucc 843340866402483599), (Int.negSucc 1765573036260778511), (Int.negSucc 1852829404728169919), (Int.negSucc 1207906955065255727), (Int.negSucc 480090692941883423), (Int.negSucc 52948259314103783), (Int.ofNat 23158751572141680), (Int.ofNat 22552480749177096), (Int.ofNat 1793199598493016), (Int.negSucc 85303432092743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1970895146840640), (Int.ofNat 44762430870138528), (Int.ofNat 309806322325391904), (Int.ofNat 863499002285136096), (Int.ofNat 1165229555731745952), (Int.ofNat 902765311325643936), (Int.ofNat 498362027420023344), (Int.ofNat 138458039112243192), (Int.ofNat 23293448459526168), (Int.negSucc 8272269606686831), (Int.negSucc 2681712457794743), (Int.negSucc 67787278553231)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 212438154988799), (Int.negSucc 8184642877657175), (Int.negSucc 84532761159017639), (Int.negSucc 321223085130222407), (Int.negSucc 569230171679429879), (Int.negSucc 534651897078462695), (Int.negSucc 345523227178700519), (Int.negSucc 146750178857463215), (Int.negSucc 36099960341718167), (Int.negSucc 5084893555347095), (Int.ofNat 1225865458889280), (Int.ofNat 168290616145968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10513715784000), (Int.ofNat 940620735946152), (Int.ofNat 16411135577046960), (Int.ofNat 88817129871815400), (Int.ofNat 210130309021138176), (Int.ofNat 252907535956698072), (Int.ofNat 180096706754458416), (Int.ofNat 100497411746456112), (Int.ofNat 29737804915781352), (Int.ofNat 8400516513133680), (Int.ofNat 352266185842848), (Int.negSucc 16472226422591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 55115572783439), (Int.negSucc 2119694247695303), (Int.negSucc 17708269129728623), (Int.negSucc 56715697500352799), (Int.negSucc 91833082556907815), (Int.negSucc 75924634785062327), (Int.negSucc 47452083890435351), (Int.negSucc 18512881515827711), (Int.negSucc 5351277805418735), (Int.negSucc 841158800783711), (Int.negSucc 85593143607839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 779772895200), (Int.ofNat 161864621383320), (Int.ofNat 2445607138386168), (Int.ofNat 10850324982351480), (Int.ofNat 23940924028830576), (Int.ofNat 26145699090239160), (Int.ofNat 16318499766595344), (Int.ofNat 8535818321057664), (Int.ofNat 2214290117334528), (Int.ofNat 578241791994528), (Int.ofNat 47879662915008)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5530484044799), (Int.negSucc 218197354400207), (Int.negSucc 1450074548146535), (Int.negSucc 4153842904289831), (Int.negSucc 6734586297801599), (Int.negSucc 4554407364801839), (Int.negSucc 2642574678191423), (Int.negSucc 759897755653823), (Int.negSucc 204848935365887), (Int.negSucc 8973469272383)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10080052166880), (Int.ofNat 135654931403064), (Int.ofNat 458173453431888), (Int.ofNat 1101253995576288), (Int.ofNat 1088431030663488), (Int.ofNat 529342458568128), (Int.ofNat 218535984377856), (Int.ofNat 35125447824000), (Int.ofNat 555126524928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7532039430719), (Int.negSucc 36704725861967), (Int.negSucc 90214309599839), (Int.negSucc 182572533231263), (Int.negSucc 82602482662655), (Int.negSucc 38976600439295), (Int.negSucc 2243887474175)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2444110858368), (Int.ofNat 3116681662752), (Int.ofNat 13544170968384), (Int.ofNat 12713125758336), (Int.ofNat 2822395373568)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 286117546751), (Int.ofNat 111496129344), (Int.negSucc 1133634424319)]]

theorem h1n27_arithmetic_row0 :
    (BiPoly.mul h1p20 h1p26).getD 0 []=h1p27.getD 0 [] := by
  decide +kernel

theorem h1n27_arithmetic_row1 :
    (BiPoly.mul h1p20 h1p26).getD 1 []=h1p27.getD 1 [] := by
  decide +kernel

theorem h1n27_arithmetic_row2 :
    (BiPoly.mul h1p20 h1p26).getD 2 []=h1p27.getD 2 [] := by
  decide +kernel

theorem h1n27_arithmetic_row3 :
    (BiPoly.mul h1p20 h1p26).getD 3 []=h1p27.getD 3 [] := by
  decide +kernel

theorem h1n27_arithmetic_row4 :
    (BiPoly.mul h1p20 h1p26).getD 4 []=h1p27.getD 4 [] := by
  decide +kernel

theorem h1n27_arithmetic_row5 :
    (BiPoly.mul h1p20 h1p26).getD 5 []=h1p27.getD 5 [] := by
  decide +kernel

theorem h1n27_arithmetic_row6 :
    (BiPoly.mul h1p20 h1p26).getD 6 []=h1p27.getD 6 [] := by
  decide +kernel

theorem h1n27_arithmetic_row7 :
    (BiPoly.mul h1p20 h1p26).getD 7 []=h1p27.getD 7 [] := by
  decide +kernel

theorem h1n27_arithmetic_row8 :
    (BiPoly.mul h1p20 h1p26).getD 8 []=h1p27.getD 8 [] := by
  decide +kernel

theorem h1n27_arithmetic_row9 :
    (BiPoly.mul h1p20 h1p26).getD 9 []=h1p27.getD 9 [] := by
  decide +kernel

theorem h1n27_arithmetic_row10 :
    (BiPoly.mul h1p20 h1p26).getD 10 []=h1p27.getD 10 [] := by
  decide +kernel

theorem h1n27_arithmetic_row11 :
    (BiPoly.mul h1p20 h1p26).getD 11 []=h1p27.getD 11 [] := by
  decide +kernel

theorem h1n27_arithmetic_row12 :
    (BiPoly.mul h1p20 h1p26).getD 12 []=h1p27.getD 12 [] := by
  decide +kernel

theorem h1n27_arithmetic_row13 :
    (BiPoly.mul h1p20 h1p26).getD 13 []=h1p27.getD 13 [] := by
  decide +kernel

theorem h1n27_arithmetic_row14 :
    (BiPoly.mul h1p20 h1p26).getD 14 []=h1p27.getD 14 [] := by
  decide +kernel

theorem h1n27_arithmetic_row15 :
    (BiPoly.mul h1p20 h1p26).getD 15 []=h1p27.getD 15 [] := by
  decide +kernel

theorem h1n27_arithmetic_row16 :
    (BiPoly.mul h1p20 h1p26).getD 16 []=h1p27.getD 16 [] := by
  decide +kernel

theorem h1n27_arithmetic_row17 :
    (BiPoly.mul h1p20 h1p26).getD 17 []=h1p27.getD 17 [] := by
  decide +kernel

theorem h1n27_arithmetic_row18 :
    (BiPoly.mul h1p20 h1p26).getD 18 []=h1p27.getD 18 [] := by
  decide +kernel

theorem h1n27_arithmetic_row19 :
    (BiPoly.mul h1p20 h1p26).getD 19 []=h1p27.getD 19 [] := by
  decide +kernel

theorem h1n27_arithmetic_row20 :
    (BiPoly.mul h1p20 h1p26).getD 20 []=h1p27.getD 20 [] := by
  decide +kernel

theorem h1n27_arithmetic_row21 :
    (BiPoly.mul h1p20 h1p26).getD 21 []=h1p27.getD 21 [] := by
  decide +kernel

theorem h1n27_arithmetic : BiPoly.mul h1p20 h1p26=h1p27 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p20 h1p26).getD j.val []=h1p27.getD j.val [] :=
      (fun j => Fin.cases h1n27_arithmetic_row0 (fun j => Fin.cases h1n27_arithmetic_row1 (fun j => Fin.cases h1n27_arithmetic_row2 (fun j => Fin.cases h1n27_arithmetic_row3 (fun j => Fin.cases h1n27_arithmetic_row4 (fun j => Fin.cases h1n27_arithmetic_row5 (fun j => Fin.cases h1n27_arithmetic_row6 (fun j => Fin.cases h1n27_arithmetic_row7 (fun j => Fin.cases h1n27_arithmetic_row8 (fun j => Fin.cases h1n27_arithmetic_row9 (fun j => Fin.cases h1n27_arithmetic_row10 (fun j => Fin.cases h1n27_arithmetic_row11 (fun j => Fin.cases h1n27_arithmetic_row12 (fun j => Fin.cases h1n27_arithmetic_row13 (fun j => Fin.cases h1n27_arithmetic_row14 (fun j => Fin.cases h1n27_arithmetic_row15 (fun j => Fin.cases h1n27_arithmetic_row16 (fun j => Fin.cases h1n27_arithmetic_row17 (fun j => Fin.cases h1n27_arithmetic_row18 (fun j => Fin.cases h1n27_arithmetic_row19 (fun j => Fin.cases h1n27_arithmetic_row20 (fun j => Fin.cases h1n27_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n27 : h1e27.toBi mapPolyEnv=h1p27 := by
  change BiPoly.mul (h1e20.toBi mapPolyEnv) (h1e26.toBi mapPolyEnv)=h1p27
  rw [h1n20, h1n26]
  exact h1n27_arithmetic

#print axioms h1n27_arithmetic
end StackSorting.RationalLift
