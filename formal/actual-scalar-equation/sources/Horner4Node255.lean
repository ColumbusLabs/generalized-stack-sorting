import BivariateRowEquality
import Horner4Base
import Horner4Node254
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p255 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 2031396253545312000), (Int.ofNat 15360752806549902720), (Int.ofNat 20407262621996085120), (Int.negSucc 54578310513756485759), (Int.negSucc 62663574950343181439), (Int.ofNat 75476828338959801600)], [(Int.ofNat 0), (Int.negSucc 18759122023807226879), (Int.negSucc 142870240136450232575), (Int.negSucc 199690542081115648127), (Int.ofNat 463856726516263987968), (Int.ofNat 536856840074778742656), (Int.negSucc 666268253611787305727), (Int.ofNat 54674743062527769600)], [(Int.ofNat 0), (Int.ofNat 81660492977557867200), (Int.ofNat 609712299861169903200), (Int.ofNat 870701038111774820736), (Int.negSucc 1733092021477193958143), (Int.negSucc 2109126901601960220671), (Int.ofNat 2408907737453314586400), (Int.negSucc 250698307675646757311), (Int.ofNat 12818695244197165056)], [(Int.ofNat 0), (Int.negSucc 222023246049717001919), (Int.negSucc 1580352707944883950559), (Int.negSucc 2281716407994599389823), (Int.ofNat 3535592210156297397888), (Int.ofNat 4950042153751420239168), (Int.negSucc 4271538472540788595103), (Int.ofNat 85334028396585550848), (Int.negSucc 3172592616951517055), (Int.ofNat 941669269006675968)], [(Int.ofNat 0), (Int.ofNat 419738835075237904320), (Int.ofNat 2783841840940482057888), (Int.ofNat 4107014145677300331648), (Int.negSucc 3795328098492886939583), (Int.negSucc 7616235313561762170239), (Int.ofNat 2567816994678211241952), (Int.ofNat 1662346959509207896704), (Int.negSucc 163496317610300346623), (Int.ofNat 5127377728419392256), (Int.negSucc 5018858459197439)], [(Int.ofNat 0), (Int.negSucc 580164219524615765279), (Int.negSucc 3545940132640566036335), (Int.negSucc 5531605180476777776591), (Int.ofNat 723958979188238152320), (Int.ofNat 7657521554478757054080), (Int.ofNat 4160733392187570043152), (Int.negSucc 4222489600095765717263), (Int.ofNat 253118651331767382048), (Int.negSucc 7077930902830150655), (Int.ofNat 163990727085798912)], [(Int.ofNat 0), (Int.ofNat 600096123682933724000), (Int.ofNat 3406080501121174236784), (Int.ofNat 5938116834833109947360), (Int.ofNat 4033931165836387604288), (Int.negSucc 3986267443080926222495), (Int.negSucc 10267582092405408981039), (Int.ofNat 3494204720890467627744), (Int.ofNat 448313700530100221792), (Int.negSucc 40063643976403188543), (Int.ofNat 978260698166993408)], [(Int.ofNat 0), (Int.negSucc 468172423387910217119), (Int.negSucc 2549116002586300342095), (Int.negSucc 5291170115412952123951), (Int.negSucc 6807273431162753436063), (Int.negSucc 1392826103600171220127), (Int.ofNat 9153086034776163030320), (Int.ofNat 1705169335863178317296), (Int.negSucc 1499334488941746645087), (Int.ofNat 58005452975393587712), (Int.ofNat 32386040317218304)], [(Int.ofNat 0), (Int.ofNat 274730146647500873760), (Int.ofNat 1523935563213829563760), (Int.ofNat 3959579945702407148864), (Int.ofNat 6295237620615789489952), (Int.ofNat 4868275280502967727840), (Int.negSucc 2464834801027214099791), (Int.negSucc 5689242889275044477375), (Int.ofNat 1090082952075540439712), (Int.ofNat 90741128988684482432), (Int.negSucc 5270640717088985215)], [(Int.ofNat 0), (Int.negSucc 119789169881324076959), (Int.negSucc 737136849670354503247), (Int.negSucc 2450874455708614518751), (Int.negSucc 4186210509653467102079), (Int.negSucc 4911409710924474859823), (Int.negSucc 2842207706918442088479), (Int.ofNat 4150398462345391620144), (Int.ofNat 664377616062248768512), (Int.negSucc 218304775389722611119), (Int.negSucc 198931661367872991)], [(Int.ofNat 0), (Int.ofNat 37912484506131179360), (Int.ofNat 286988426121009637008), (Int.ofNat 1216373921028894057456), (Int.ofNat 2281415913194059122960), (Int.ofNat 3099189567791746835232), (Int.ofNat 3654490749621410689664), (Int.negSucc 273275748138810150639), (Int.negSucc 1434573097455270382447), (Int.ofNat 64975258165062723776), (Int.ofNat 11649523873405708224)], [(Int.ofNat 0), (Int.negSucc 8367148377438932639), (Int.negSucc 87729218747257887183), (Int.negSucc 466396092675536555631), (Int.negSucc 1078234269490041868799), (Int.negSucc 1464374314980789126175), (Int.negSucc 2105241540362349649151), (Int.negSucc 1505722585744629114655), (Int.ofNat 639170388611672624800), (Int.ofNat 145254277217656618976), (Int.negSucc 5073704612781739967)], [(Int.ofNat 0), (Int.ofNat 1200244720645703200), (Int.ofNat 20190868068541208176), (Int.ofNat 132644972861984289184), (Int.ofNat 424986012588900747296), (Int.ofNat 598346310806097201792), (Int.ofNat 763773220733575363104), (Int.ofNat 1105303411521600605824), (Int.ofNat 187701306836981303712), (Int.negSucc 125768224965282306527), (Int.negSucc 8089178979388399679)], [(Int.ofNat 0), (Int.negSucc 97584014767415359), (Int.negSucc 3288431962017103423), (Int.negSucc 26656506320466761327), (Int.negSucc 127652116667044893567), (Int.negSucc 222122200023217701999), (Int.negSucc 212604579829791756575), (Int.negSucc 378616396429241584511), (Int.negSucc 295204511911310824895), (Int.ofNat 5791119267864294720), (Int.ofNat 6810215667330404736)], [(Int.ofNat 0), (Int.ofNat 3189396028072320), (Int.ofNat 340413243359731872), (Int.ofNat 3537467885761559376), (Int.ofNat 26636480862373176720), (Int.ofNat 67477809991876731072), (Int.ofNat 59925967179193851072), (Int.ofNat 68688387142252071744), (Int.ofNat 119951392949799998016), (Int.ofNat 33765279233560491264), (Int.ofNat 254823330769300224)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17081688286185983), (Int.negSucc 275781176356055615), (Int.negSucc 3475415251970651615), (Int.negSucc 14466774130012632095), (Int.negSucc 17149862118563415935), (Int.negSucc 7068864535102991423), (Int.negSucc 21257589525924410495), (Int.negSucc 16679977248056192639), (Int.negSucc 1919993182818050303)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9493123190590080), (Int.ofNat 233180415840549024), (Int.ofNat 1906334669587083552), (Int.ofNat 3631839451102617984), (Int.ofNat 1069894542297405312), (Int.ofNat 852487366929443712), (Int.ofNat 3190315261372656768), (Int.ofNat 714688757151959808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3994839530841599), (Int.negSucc 122824125030563711), (Int.negSucc 443146559438082815), (Int.negSucc 267376268962392191), (Int.ofNat 232314191336666880), (Int.negSucc 215318464403355647), (Int.negSucc 83261165847367679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1283777641437696), (Int.ofNat 23219758263233664), (Int.ofNat 27856489159764864), (Int.negSucc 26895833601903359)]]

theorem h4n255_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p254).getD 0 []=h4p255.getD 0 [] := by
  decide +kernel

theorem h4n255_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p254).getD 1 []=h4p255.getD 1 [] := by
  decide +kernel

theorem h4n255_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p254).getD 2 []=h4p255.getD 2 [] := by
  decide +kernel

theorem h4n255_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p254).getD 3 []=h4p255.getD 3 [] := by
  decide +kernel

theorem h4n255_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p254).getD 4 []=h4p255.getD 4 [] := by
  decide +kernel

theorem h4n255_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p254).getD 5 []=h4p255.getD 5 [] := by
  decide +kernel

theorem h4n255_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p254).getD 6 []=h4p255.getD 6 [] := by
  decide +kernel

theorem h4n255_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p254).getD 7 []=h4p255.getD 7 [] := by
  decide +kernel

theorem h4n255_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p254).getD 8 []=h4p255.getD 8 [] := by
  decide +kernel

theorem h4n255_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p254).getD 9 []=h4p255.getD 9 [] := by
  decide +kernel

theorem h4n255_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p254).getD 10 []=h4p255.getD 10 [] := by
  decide +kernel

theorem h4n255_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p254).getD 11 []=h4p255.getD 11 [] := by
  decide +kernel

theorem h4n255_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p254).getD 12 []=h4p255.getD 12 [] := by
  decide +kernel

theorem h4n255_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p254).getD 13 []=h4p255.getD 13 [] := by
  decide +kernel

theorem h4n255_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p254).getD 14 []=h4p255.getD 14 [] := by
  decide +kernel

theorem h4n255_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p254).getD 15 []=h4p255.getD 15 [] := by
  decide +kernel

theorem h4n255_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p254).getD 16 []=h4p255.getD 16 [] := by
  decide +kernel

theorem h4n255_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p254).getD 17 []=h4p255.getD 17 [] := by
  decide +kernel

theorem h4n255_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p254).getD 18 []=h4p255.getD 18 [] := by
  decide +kernel

theorem h4n255_arithmetic : BiPoly.mul h4p13 h4p254=h4p255 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p254).getD j.val []=h4p255.getD j.val [] :=
      (fun j => Fin.cases h4n255_arithmetic_row0 (fun j => Fin.cases h4n255_arithmetic_row1 (fun j => Fin.cases h4n255_arithmetic_row2 (fun j => Fin.cases h4n255_arithmetic_row3 (fun j => Fin.cases h4n255_arithmetic_row4 (fun j => Fin.cases h4n255_arithmetic_row5 (fun j => Fin.cases h4n255_arithmetic_row6 (fun j => Fin.cases h4n255_arithmetic_row7 (fun j => Fin.cases h4n255_arithmetic_row8 (fun j => Fin.cases h4n255_arithmetic_row9 (fun j => Fin.cases h4n255_arithmetic_row10 (fun j => Fin.cases h4n255_arithmetic_row11 (fun j => Fin.cases h4n255_arithmetic_row12 (fun j => Fin.cases h4n255_arithmetic_row13 (fun j => Fin.cases h4n255_arithmetic_row14 (fun j => Fin.cases h4n255_arithmetic_row15 (fun j => Fin.cases h4n255_arithmetic_row16 (fun j => Fin.cases h4n255_arithmetic_row17 (fun j => Fin.cases h4n255_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n255 : h4e255.toBi mapPolyEnv=h4p255 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e254.toBi mapPolyEnv)=h4p255
  rw [h4n13, h4n254]
  exact h4n255_arithmetic

#print axioms h4n255_arithmetic
end StackSorting.RationalLift
