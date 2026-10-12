import BivariateRowEquality
import Horner1Base
import Horner1Node065
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p66 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8361968255999), (Int.negSucc 46385310519359), (Int.ofNat 6752714519520), (Int.ofNat 252226676057760), (Int.ofNat 14696439495840), (Int.negSucc 192754179779039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 91501224769440), (Int.ofNat 447213795865488), (Int.negSucc 291145051570319), (Int.negSucc 2518041755160575), (Int.ofNat 453057960799296), (Int.ofNat 1623074726162736), (Int.negSucc 109959921022607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 460831533234479), (Int.negSucc 1966642486733735), (Int.ofNat 2260425350974176), (Int.ofNat 11131373201109120), (Int.negSucc 3577048882865567), (Int.negSucc 5399796206118743), (Int.negSucc 80878222867247), (Int.ofNat 16751291336928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1415077832735640), (Int.ofNat 5224449727945836), (Int.negSucc 8546963396596271), (Int.negSucc 29366652281711579), (Int.ofNat 9246314155171320), (Int.ofNat 10078480195675236), (Int.ofNat 4359329055033408), (Int.negSucc 601441973320499), (Int.ofNat 24268286831616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2958149430058499), (Int.negSucc 9365287664276657), (Int.ofNat 19704258985368636), (Int.ofNat 53146889198767710), (Int.negSucc 4675274394783659), (Int.negSucc 15260711568606629), (Int.negSucc 16889905001000123), (Int.ofNat 1868530494252906), (Int.negSucc 134404597291967), (Int.ofNat 6125638528512)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4450706497108800), (Int.ofNat 11996576694606240), (Int.negSucc 30541279704924227), (Int.negSucc 73267257667326899), (Int.negSucc 28965372400233071), (Int.ofNat 24090645438624504), (Int.ofNat 29145279948078012), (Int.ofNat 2332881752838108), (Int.negSucc 509782076072087), (Int.ofNat 14275267740000), (Int.ofNat 582310781184)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4967147076991019), (Int.negSucc 11362248726905573), (Int.ofNat 33629926838260794), (Int.ofNat 84480678258027108), (Int.ofNat 85194048783675330), (Int.negSucc 25308383706780629), (Int.negSucc 27367136296656833), (Int.negSucc 18909250160487167), (Int.ofNat 2708237228870610), (Int.negSucc 190809789724223), (Int.ofNat 5966268244224), (Int.ofNat 16212877824)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4174726565587040), (Int.ofNat 8142049858501328), (Int.negSucc 27458157278855579), (Int.negSucc 86324379716170199), (Int.negSucc 126825209639757275), (Int.negSucc 8046094565320031), (Int.ofNat 18067016270604116), (Int.ofNat 33358157743062740), (Int.negSucc 725178125755907), (Int.negSucc 110294608413219), (Int.negSucc 3384145490079), (Int.ofNat 378370819008)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2653666518048919), (Int.negSucc 4495422737513227), (Int.ofNat 17530508189154292), (Int.ofNat 77848529085870770), (Int.ofNat 128306337727270046), (Int.ofNat 70935311837217296), (Int.negSucc 10668033069548603), (Int.negSucc 23909390661897059), (Int.negSucc 11129527054057397), (Int.ofNat 1573515509312318), (Int.negSucc 88684449841191), (Int.ofNat 1480833497696)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1268815049581200), (Int.ofNat 1943572803320504), (Int.negSucc 9489089662087995), (Int.negSucc 59487739273358171), (Int.negSucc 101294840357470019), (Int.negSucc 112911644075287163), (Int.negSucc 8771016358881695), (Int.ofNat 2442929913930776), (Int.ofNat 19669826630307140), (Int.negSucc 950717504433203), (Int.ofNat 11918614617872), (Int.negSucc 2097384940527)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 448971544358199), (Int.negSucc 665675565081739), (Int.ofNat 4736335416370928), (Int.ofNat 37181351749220216), (Int.ofNat 69646889384907008), (Int.ofNat 102912023598169548), (Int.ofNat 41988579185647948), (Int.ofNat 7327265018055696), (Int.negSucc 10443429972773625), (Int.negSucc 3932506601311969), (Int.ofNat 444286610497422), (Int.negSucc 14861445319767)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 113959479759880), (Int.ofNat 179956306565556), (Int.negSucc 2188454667072923), (Int.negSucc 18673689326781575), (Int.negSucc 43643240652602171), (Int.negSucc 64531620690339323), (Int.negSucc 58939334085915719), (Int.negSucc 10485413580779739), (Int.negSucc 3731161737639279), (Int.ofNat 6253442769028168), (Int.negSucc 249178933448663), (Int.ofNat 2983123540560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 19607190777059), (Int.negSucc 37061942962561), (Int.ofNat 853195085866384), (Int.ofNat 7462441945702914), (Int.ofNat 23779522107989468), (Int.ofNat 32407670104064342), (Int.ofNat 45422901031771860), (Int.ofNat 16481931178929426), (Int.ofNat 6992239912843350), (Int.negSucc 1989580395816815), (Int.negSucc 814930766640911), (Int.ofNat 51217664208384)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2046335822480), (Int.ofNat 5351588360472), (Int.negSucc 250915050246079), (Int.negSucc 2333949711535543), (Int.negSucc 10360218730538903), (Int.negSucc 15300330292386171), (Int.negSucc 21943979386386131), (Int.negSucc 17530569412181159), (Int.negSucc 4535696996043299), (Int.negSucc 2073737245030655), (Int.ofNat 966080947091508), (Int.negSucc 14383137403631)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 97723640299), (Int.negSucc 463263034725), (Int.ofNat 50331390201110), (Int.ofNat 550699020178948), (Int.ofNat 3358076369044266), (Int.ofNat 6843232552559190), (Int.ofNat 7627049654328282), (Int.ofNat 10626993695552496), (Int.ofNat 3576353717755260), (Int.ofNat 1955991686009892), (Int.negSucc 59923023981911), (Int.negSucc 72786258700415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 16921862160), (Int.negSucc 6057374418119), (Int.negSucc 91426747000499), (Int.negSucc 759513495646343), (Int.negSucc 2463515330675855), (Int.negSucc 2527919751555887), (Int.negSucc 3680019642889823), (Int.negSucc 2720449410510599), (Int.negSucc 771498004520087), (Int.negSucc 377933293621079), (Int.ofNat 49580421561504)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 328215055680), (Int.ofNat 9388945527150), (Int.ofNat 110405833353354), (Int.ofNat 607956425036616), (Int.ofNat 903775416631704), (Int.ofNat 789574544367336), (Int.ofNat 1192304714422032), (Int.ofNat 355440743271504), (Int.ofNat 201734707159008), (Int.ofNat 13185447031296)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 441601416647), (Int.negSucc 8908300704779), (Int.negSucc 89896334978303), (Int.negSucc 254435643631115), (Int.negSucc 170229017739023), (Int.negSucc 255585784006367), (Int.negSucc 186607049125247), (Int.negSucc 45009197766575), (Int.negSucc 19904286499775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 278092895868), (Int.ofNat 6470125340868), (Int.ofNat 41614204332024), (Int.ofNat 50323775065920), (Int.ofNat 24189227590320), (Int.ofNat 51351813760752), (Int.ofNat 11421368266176), (Int.ofNat 5645643027840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 118052578439), (Int.negSucc 2981246891255), (Int.negSucc 9763208067167), (Int.negSucc 3179109916655), (Int.negSucc 4710010143455), (Int.negSucc 3729406030559), (Int.negSucc 472347676799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 33501025872), (Int.ofNat 724911779664), (Int.ofNat 902922355008), (Int.negSucc 113443364159), (Int.ofNat 472347676800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4239140831), (Int.negSucc 70852151519)]]

theorem h1n66_arithmetic_row0 :
    (BiPoly.mul h1p4 h1p65).getD 0 []=h1p66.getD 0 [] := by
  decide +kernel

theorem h1n66_arithmetic_row1 :
    (BiPoly.mul h1p4 h1p65).getD 1 []=h1p66.getD 1 [] := by
  decide +kernel

theorem h1n66_arithmetic_row2 :
    (BiPoly.mul h1p4 h1p65).getD 2 []=h1p66.getD 2 [] := by
  decide +kernel

theorem h1n66_arithmetic_row3 :
    (BiPoly.mul h1p4 h1p65).getD 3 []=h1p66.getD 3 [] := by
  decide +kernel

theorem h1n66_arithmetic_row4 :
    (BiPoly.mul h1p4 h1p65).getD 4 []=h1p66.getD 4 [] := by
  decide +kernel

theorem h1n66_arithmetic_row5 :
    (BiPoly.mul h1p4 h1p65).getD 5 []=h1p66.getD 5 [] := by
  decide +kernel

theorem h1n66_arithmetic_row6 :
    (BiPoly.mul h1p4 h1p65).getD 6 []=h1p66.getD 6 [] := by
  decide +kernel

theorem h1n66_arithmetic_row7 :
    (BiPoly.mul h1p4 h1p65).getD 7 []=h1p66.getD 7 [] := by
  decide +kernel

theorem h1n66_arithmetic_row8 :
    (BiPoly.mul h1p4 h1p65).getD 8 []=h1p66.getD 8 [] := by
  decide +kernel

theorem h1n66_arithmetic_row9 :
    (BiPoly.mul h1p4 h1p65).getD 9 []=h1p66.getD 9 [] := by
  decide +kernel

theorem h1n66_arithmetic_row10 :
    (BiPoly.mul h1p4 h1p65).getD 10 []=h1p66.getD 10 [] := by
  decide +kernel

theorem h1n66_arithmetic_row11 :
    (BiPoly.mul h1p4 h1p65).getD 11 []=h1p66.getD 11 [] := by
  decide +kernel

theorem h1n66_arithmetic_row12 :
    (BiPoly.mul h1p4 h1p65).getD 12 []=h1p66.getD 12 [] := by
  decide +kernel

theorem h1n66_arithmetic_row13 :
    (BiPoly.mul h1p4 h1p65).getD 13 []=h1p66.getD 13 [] := by
  decide +kernel

theorem h1n66_arithmetic_row14 :
    (BiPoly.mul h1p4 h1p65).getD 14 []=h1p66.getD 14 [] := by
  decide +kernel

theorem h1n66_arithmetic_row15 :
    (BiPoly.mul h1p4 h1p65).getD 15 []=h1p66.getD 15 [] := by
  decide +kernel

theorem h1n66_arithmetic_row16 :
    (BiPoly.mul h1p4 h1p65).getD 16 []=h1p66.getD 16 [] := by
  decide +kernel

theorem h1n66_arithmetic_row17 :
    (BiPoly.mul h1p4 h1p65).getD 17 []=h1p66.getD 17 [] := by
  decide +kernel

theorem h1n66_arithmetic_row18 :
    (BiPoly.mul h1p4 h1p65).getD 18 []=h1p66.getD 18 [] := by
  decide +kernel

theorem h1n66_arithmetic_row19 :
    (BiPoly.mul h1p4 h1p65).getD 19 []=h1p66.getD 19 [] := by
  decide +kernel

theorem h1n66_arithmetic_row20 :
    (BiPoly.mul h1p4 h1p65).getD 20 []=h1p66.getD 20 [] := by
  decide +kernel

theorem h1n66_arithmetic_row21 :
    (BiPoly.mul h1p4 h1p65).getD 21 []=h1p66.getD 21 [] := by
  decide +kernel

theorem h1n66_arithmetic : BiPoly.mul h1p4 h1p65=h1p66 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p4 h1p65).getD j.val []=h1p66.getD j.val [] :=
      (fun j => Fin.cases h1n66_arithmetic_row0 (fun j => Fin.cases h1n66_arithmetic_row1 (fun j => Fin.cases h1n66_arithmetic_row2 (fun j => Fin.cases h1n66_arithmetic_row3 (fun j => Fin.cases h1n66_arithmetic_row4 (fun j => Fin.cases h1n66_arithmetic_row5 (fun j => Fin.cases h1n66_arithmetic_row6 (fun j => Fin.cases h1n66_arithmetic_row7 (fun j => Fin.cases h1n66_arithmetic_row8 (fun j => Fin.cases h1n66_arithmetic_row9 (fun j => Fin.cases h1n66_arithmetic_row10 (fun j => Fin.cases h1n66_arithmetic_row11 (fun j => Fin.cases h1n66_arithmetic_row12 (fun j => Fin.cases h1n66_arithmetic_row13 (fun j => Fin.cases h1n66_arithmetic_row14 (fun j => Fin.cases h1n66_arithmetic_row15 (fun j => Fin.cases h1n66_arithmetic_row16 (fun j => Fin.cases h1n66_arithmetic_row17 (fun j => Fin.cases h1n66_arithmetic_row18 (fun j => Fin.cases h1n66_arithmetic_row19 (fun j => Fin.cases h1n66_arithmetic_row20 (fun j => Fin.cases h1n66_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n66 : h1e66.toBi mapPolyEnv=h1p66 := by
  change BiPoly.mul (h1e4.toBi mapPolyEnv) (h1e65.toBi mapPolyEnv)=h1p66
  rw [h1n4, h1n65]
  exact h1n66_arithmetic

#print axioms h1n66_arithmetic
end StackSorting.RationalLift
