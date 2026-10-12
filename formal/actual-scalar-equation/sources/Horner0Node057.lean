import BivariateRowEquality
import Horner0Base
import Horner0Node054
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p57 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 24376755042543744000), (Int.ofNat 173664203347485944640), (Int.ofNat 28647499305416456160), (Int.negSucc 1516216704919464130559), (Int.negSucc 319333849247321599679), (Int.ofNat 4585622095430914691520), (Int.negSucc 2915292494592322336799)], [(Int.ofNat 0), (Int.negSucc 304079993642260726559), (Int.negSucc 2068877622365325166031), (Int.ofNat 76665220813484633808), (Int.ofNat 18131327724662521792416), (Int.ofNat 1363567220193494662848), (Int.negSucc 51920327345085257530319), (Int.ofNat 37138889773144831046544), (Int.negSucc 3055272305027132620799)], [(Int.ofNat 0), (Int.ofNat 1801361389410818883360), (Int.ofNat 11488077878606637570432), (Int.negSucc 3384770145122649674087), (Int.negSucc 100126985023058930291591), (Int.ofNat 5535717558369609608784), (Int.ofNat 260497754901775834880688), (Int.negSucc 193485458540326649056775), (Int.ofNat 22383114036864826247640), (Int.negSucc 1216294806258192521087)], [(Int.ofNat 0), (Int.negSucc 6734970421039109058119), (Int.negSucc 39317373014206764774995), (Int.ofNat 23933170703373980019984), (Int.ofNat 335959174931824008008892), (Int.negSucc 55149291406426000349591), (Int.negSucc 752973779952789149752955), (Int.ofNat 516969184386651278197248), (Int.negSucc 36819817702410078159083), (Int.ofNat 2545351734390322791888), (Int.negSucc 223943037599111307263)], [(Int.ofNat 0), (Int.ofNat 17795773966138128176400), (Int.ofNat 92415686632142940626760), (Int.negSucc 90667376445546775912103), (Int.negSucc 761619414406145392283759), (Int.ofNat 167792678715026582841816), (Int.ofNat 1362234544864966311987672), (Int.negSucc 635036871732865692598439), (Int.negSucc 151025484996452817500975), (Int.ofNat 22974829429094475279624), (Int.negSucc 892359980734440368447), (Int.negSucc 17986360076695531007)], [(Int.ofNat 0), (Int.negSucc 35228362861815940685159), (Int.negSucc 157362388088328815720075), (Int.ofNat 223165021432620668362224), (Int.ofNat 1234408027871210369575248), (Int.negSucc 208383999608492422224575), (Int.negSucc 1556568236021299679914427), (Int.negSucc 220667006814636129991823), (Int.ofNat 794545068964263266334312), (Int.negSucc 94800850673839477795175), (Int.ofNat 6117642332111317240416), (Int.negSucc 226676467561306631807), (Int.negSucc 408098903763369983)], [(Int.ofNat 0), (Int.ofNat 54008970765647198407860), (Int.ofNat 199494216588821266639878), (Int.negSucc 386548601653289484065981), (Int.negSucc 1492250702669963490249305), (Int.negSucc 124685479425984286771445), (Int.ofNat 1042834251687553403540034), (Int.ofNat 2032326459215158462312350), (Int.negSucc 1447481710610969714315189), (Int.ofNat 33450722457672601122234), (Int.ofNat 4521453234795479703264), (Int.negSucc 43820799016282548671), (Int.negSucc 13622952423369760895), (Int.ofNat 2509429229598720)], [(Int.ofNat 0), (Int.negSucc 65363313342728274240559), (Int.negSucc 190431562262341783682627), (Int.ofNat 491786805880243044307562), (Int.ofNat 1420404766508559890799636), (Int.ofNat 933095695358868436936302), (Int.negSucc 250149565473003103800107), (Int.negSucc 3190241256755545332444217), (Int.ofNat 817975567394431205793312), (Int.ofNat 467917028663215993176410), (Int.negSucc 59771601604179909935347), (Int.ofNat 3164548761558028776768), (Int.negSucc 76142799580006763199), (Int.negSucc 33061493565724415)], [(Int.ofNat 0), (Int.ofNat 63084012965217999112140), (Int.ofNat 136661522998683388400894), (Int.negSucc 472397855204355144118325), (Int.negSucc 1169473761816496113698657), (Int.negSucc 1795229621633863343210107), (Int.negSucc 291036456497768863468555), (Int.ofNat 2283782425709023605350482), (Int.ofNat 1333871301038835499178334), (Int.negSucc 1090228928307609908648659), (Int.ofNat 64710709506135066778474), (Int.negSucc 996712271433262052119), (Int.ofNat 32776223971933663616), (Int.negSucc 2027813636659666815)], [(Int.ofNat 0), (Int.negSucc 48741150232985552285399), (Int.negSucc 72654819236930279836855), (Int.ofNat 351125613022406262161254), (Int.ofNat 940027184507646695195076), (Int.ofNat 2118261607322365850520040), (Int.ofNat 668659994910523566313224), (Int.negSucc 245488063607990710569129), (Int.negSucc 2929062398816452830492843), (Int.ofNat 785583778140122015203564), (Int.ofNat 151320972389005741545692), (Int.negSucc 18327484068716178343175), (Int.ofNat 727037301534953648080), (Int.negSucc 11635047867648324223)], [(Int.ofNat 0), (Int.ofNat 30111297513148548094280), (Int.ofNat 27803657511579070324688), (Int.negSucc 209225990195514587696821), (Int.negSucc 766807062924263038165087), (Int.negSucc 1782311751441087457891655), (Int.negSucc 1127865401167274512776515), (Int.negSucc 954011811368759961208953), (Int.ofNat 2157812652050121976247522), (Int.ofNat 572793446526763085268946), (Int.negSucc 418350220633282662461397), (Int.ofNat 21814570791124306551350), (Int.negSucc 141980983459219017423), (Int.negSucc 5729780553121831231)], [(Int.ofNat 0), (Int.negSucc 14785216728427328150359), (Int.negSucc 7484993905443396982499), (Int.ofNat 106470507447412466119964), (Int.ofNat 582875233958938141604910), (Int.ofNat 1172756945233014846252554), (Int.ofNat 1440765674850574337583510), (Int.ofNat 936088362290695410897496), (Int.negSucc 152719175664983144846069), (Int.negSucc 1487008805219086114124267), (Int.ofNat 281427826030057093782986), (Int.ofNat 34237558915528286969962), (Int.negSucc 3106158981623160153175), (Int.ofNat 73110446047252274384)], [(Int.ofNat 0), (Int.ofNat 5706186979507875078360), (Int.ofNat 1706386479511866483180), (Int.negSucc 50487163224808607298727), (Int.negSucc 375607691932308260111275), (Int.negSucc 671945834268397717100295), (Int.negSucc 1291384622159183836861897), (Int.negSucc 654325356062278296739785), (Int.negSucc 910142339849219948377955), (Int.ofNat 983701610255732891095532), (Int.ofNat 201331848016868754207614), (Int.negSucc 85978040929940631411075), (Int.ofNat 2146068976030113858086), (Int.ofNat 60091196273839141992)], [(Int.ofNat 0), (Int.negSucc 1700539339836554387079), (Int.negSucc 696976148068952424979), (Int.ofNat 23335071016030483472488), (Int.ofNat 196529229915644778287584), (Int.ofNat 371952195505384939037840), (Int.ofNat 814800449514500053435294), (Int.ofNat 580900316112046119761428), (Int.ofNat 728416450367020186510968), (Int.ofNat 26710952355052876100892), (Int.negSucc 427060203085018659158053), (Int.ofNat 38351760904410238429566), (Int.ofNat 5614683441450652549904), (Int.negSucc 227248241657402476655)], [(Int.ofNat 0), (Int.ofNat 380848869711280832500), (Int.ofNat 407486761728778946318), (Int.negSucc 9951249112368506198733), (Int.negSucc 82908113035197751029429), (Int.negSucc 200726204101514668313733), (Int.negSucc 376186901409350251845099), (Int.negSucc 499112674143837795183987), (Int.negSucc 307733753803659651781131), (Int.negSucc 423200355564240515875275), (Int.ofNat 210259235560995950507698), (Int.ofNat 49789372143789454467564), (Int.negSucc 7823292274095111684143), (Int.negSucc 90757039397329476479)], [(Int.ofNat 0), (Int.negSucc 61438189753165097519), (Int.negSucc 174851406042376404531), (Int.ofNat 3546421011182489287102), (Int.ofNat 28409991372234186166088), (Int.ofNat 96691627179940962744578), (Int.ofNat 140488189545476178916742), (Int.ofNat 300422108866156893725346), (Int.ofNat 144828137386248156104250), (Int.ofNat 266840928501588441130794), (Int.ofNat 49920849563742803600988), (Int.negSucc 62298060315367676749235), (Int.negSucc 236832622815044778683), (Int.ofNat 398463129720381009168)], [(Int.ofNat 0), (Int.ofNat 6654652283843520460), (Int.ofNat 49032715035525099534), (Int.negSucc 975558960415264130025), (Int.negSucc 7962291485982292630645), (Int.negSucc 38003228800112828834615), (Int.negSucc 51418095817740699695457), (Int.negSucc 117762430726678329376211), (Int.negSucc 102687064370400613751849), (Int.negSucc 78597302033877411270563), (Int.negSucc 100458969934223970322295), (Int.ofNat 15318493392384303952104), (Int.ofNat 5861394460066601376600), (Int.negSucc 83615220456784449407)], [(Int.ofNat 0), (Int.negSucc 424307440652980759), (Int.negSucc 8768791814094525783), (Int.ofNat 195047801517761172098), (Int.ofNat 1812756633110383527628), (Int.ofNat 11525552075526375264492), (Int.ofNat 20242725245553986421282), (Int.ofNat 30350817694417178912058), (Int.ofNat 56078791133116528678416), (Int.ofNat 18749607306286040011692), (Int.ofNat 45260199432692628397692), (Int.ofNat 13313274106575335979096), (Int.negSucc 3210474956157365675255), (Int.negSucc 265253645927795501663)], [(Int.ofNat 0), (Int.ofNat 11561560601762160), (Int.ofNat 922686852208999452), (Int.negSucc 26512415357744405621), (Int.negSucc 324796948338852271991), (Int.negSucc 2595197235144323094947), (Int.negSucc 7230534667968464655089), (Int.negSucc 6141407123710567735907), (Int.negSucc 18069428255188333673471), (Int.negSucc 9909672657819648452063), (Int.negSucc 8688730441655904580007), (Int.negSucc 10903760016490695934871), (Int.negSucc 500562690552885524543), (Int.ofNat 168534561699602514432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 43980767379517391), (Int.ofNat 2189522220940903068), (Int.ofNat 42876487426330334730), (Int.ofNat 416281064362294380438), (Int.ofNat 1938779126947340239260), (Int.ofNat 1631984847373444472388), (Int.ofNat 3095117049804601326588), (Int.ofNat 4752017688157491146112), (Int.ofNat 739661471763736308336), (Int.ofNat 3135701877377323698288), (Int.ofNat 1073713591623998406672), (Int.ofNat 21846858336817934400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 83200348233395279), (Int.negSucc 3687183504299953691), (Int.negSucc 44708973930704203811), (Int.negSucc 350816337545851402487), (Int.negSucc 530120012990485976423), (Int.negSucc 214468523158389031799), (Int.negSucc 1180842500754786237263), (Int.negSucc 275012089050408080543), (Int.negSucc 321563299784826508127), (Int.negSucc 405479905765775064575), (Int.negSucc 50964315332217814655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 154218920579523792), (Int.ofNat 2865407007628600164), (Int.ofNat 38917962532316254356), (Int.ofNat 122177932355620924056), (Int.ofNat 11879734370829087816), (Int.ofNat 119670834328751028672), (Int.ofNat 132409332363908401344), (Int.negSucc 17617819364450414207), (Int.ofNat 62118067677299903520), (Int.ofNat 17079631026087507840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 81895859947255391), (Int.negSucc 2201890958758764503), (Int.negSucc 15901184484608992055), (Int.negSucc 9072046206615794687), (Int.ofNat 4667941636519049856), (Int.negSucc 24985477761345859679), (Int.ofNat 5414068108670873184), (Int.negSucc 3064958029088017919), (Int.negSucc 1873376231565772799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34186416066267840), (Int.ofNat 935591480684059248), (Int.ofNat 2051834229205065936), (Int.negSucc 1901548941878588543), (Int.ofNat 1787866049329286112), (Int.negSucc 324149821307959679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8665499079704447), (Int.negSucc 139402370117418335), (Int.ofNat 90773438406423840)]]

theorem h0n57_arithmetic_row0 :
    (BiPoly.mul h0p36 h0p54).getD 0 []=h0p57.getD 0 [] := by
  decide +kernel

theorem h0n57_arithmetic_row1 :
    (BiPoly.mul h0p36 h0p54).getD 1 []=h0p57.getD 1 [] := by
  decide +kernel

theorem h0n57_arithmetic_row2 :
    (BiPoly.mul h0p36 h0p54).getD 2 []=h0p57.getD 2 [] := by
  decide +kernel

theorem h0n57_arithmetic_row3 :
    (BiPoly.mul h0p36 h0p54).getD 3 []=h0p57.getD 3 [] := by
  decide +kernel

theorem h0n57_arithmetic_row4 :
    (BiPoly.mul h0p36 h0p54).getD 4 []=h0p57.getD 4 [] := by
  decide +kernel

theorem h0n57_arithmetic_row5 :
    (BiPoly.mul h0p36 h0p54).getD 5 []=h0p57.getD 5 [] := by
  decide +kernel

theorem h0n57_arithmetic_row6 :
    (BiPoly.mul h0p36 h0p54).getD 6 []=h0p57.getD 6 [] := by
  decide +kernel

theorem h0n57_arithmetic_row7 :
    (BiPoly.mul h0p36 h0p54).getD 7 []=h0p57.getD 7 [] := by
  decide +kernel

theorem h0n57_arithmetic_row8 :
    (BiPoly.mul h0p36 h0p54).getD 8 []=h0p57.getD 8 [] := by
  decide +kernel

theorem h0n57_arithmetic_row9 :
    (BiPoly.mul h0p36 h0p54).getD 9 []=h0p57.getD 9 [] := by
  decide +kernel

theorem h0n57_arithmetic_row10 :
    (BiPoly.mul h0p36 h0p54).getD 10 []=h0p57.getD 10 [] := by
  decide +kernel

theorem h0n57_arithmetic_row11 :
    (BiPoly.mul h0p36 h0p54).getD 11 []=h0p57.getD 11 [] := by
  decide +kernel

theorem h0n57_arithmetic_row12 :
    (BiPoly.mul h0p36 h0p54).getD 12 []=h0p57.getD 12 [] := by
  decide +kernel

theorem h0n57_arithmetic_row13 :
    (BiPoly.mul h0p36 h0p54).getD 13 []=h0p57.getD 13 [] := by
  decide +kernel

theorem h0n57_arithmetic_row14 :
    (BiPoly.mul h0p36 h0p54).getD 14 []=h0p57.getD 14 [] := by
  decide +kernel

theorem h0n57_arithmetic_row15 :
    (BiPoly.mul h0p36 h0p54).getD 15 []=h0p57.getD 15 [] := by
  decide +kernel

theorem h0n57_arithmetic_row16 :
    (BiPoly.mul h0p36 h0p54).getD 16 []=h0p57.getD 16 [] := by
  decide +kernel

theorem h0n57_arithmetic_row17 :
    (BiPoly.mul h0p36 h0p54).getD 17 []=h0p57.getD 17 [] := by
  decide +kernel

theorem h0n57_arithmetic_row18 :
    (BiPoly.mul h0p36 h0p54).getD 18 []=h0p57.getD 18 [] := by
  decide +kernel

theorem h0n57_arithmetic_row19 :
    (BiPoly.mul h0p36 h0p54).getD 19 []=h0p57.getD 19 [] := by
  decide +kernel

theorem h0n57_arithmetic_row20 :
    (BiPoly.mul h0p36 h0p54).getD 20 []=h0p57.getD 20 [] := by
  decide +kernel

theorem h0n57_arithmetic_row21 :
    (BiPoly.mul h0p36 h0p54).getD 21 []=h0p57.getD 21 [] := by
  decide +kernel

theorem h0n57_arithmetic_row22 :
    (BiPoly.mul h0p36 h0p54).getD 22 []=h0p57.getD 22 [] := by
  decide +kernel

theorem h0n57_arithmetic_row23 :
    (BiPoly.mul h0p36 h0p54).getD 23 []=h0p57.getD 23 [] := by
  decide +kernel

theorem h0n57_arithmetic_row24 :
    (BiPoly.mul h0p36 h0p54).getD 24 []=h0p57.getD 24 [] := by
  decide +kernel

theorem h0n57_arithmetic : BiPoly.mul h0p36 h0p54=h0p57 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p36 h0p54).getD j.val []=h0p57.getD j.val [] :=
      (fun j => Fin.cases h0n57_arithmetic_row0 (fun j => Fin.cases h0n57_arithmetic_row1 (fun j => Fin.cases h0n57_arithmetic_row2 (fun j => Fin.cases h0n57_arithmetic_row3 (fun j => Fin.cases h0n57_arithmetic_row4 (fun j => Fin.cases h0n57_arithmetic_row5 (fun j => Fin.cases h0n57_arithmetic_row6 (fun j => Fin.cases h0n57_arithmetic_row7 (fun j => Fin.cases h0n57_arithmetic_row8 (fun j => Fin.cases h0n57_arithmetic_row9 (fun j => Fin.cases h0n57_arithmetic_row10 (fun j => Fin.cases h0n57_arithmetic_row11 (fun j => Fin.cases h0n57_arithmetic_row12 (fun j => Fin.cases h0n57_arithmetic_row13 (fun j => Fin.cases h0n57_arithmetic_row14 (fun j => Fin.cases h0n57_arithmetic_row15 (fun j => Fin.cases h0n57_arithmetic_row16 (fun j => Fin.cases h0n57_arithmetic_row17 (fun j => Fin.cases h0n57_arithmetic_row18 (fun j => Fin.cases h0n57_arithmetic_row19 (fun j => Fin.cases h0n57_arithmetic_row20 (fun j => Fin.cases h0n57_arithmetic_row21 (fun j => Fin.cases h0n57_arithmetic_row22 (fun j => Fin.cases h0n57_arithmetic_row23 (fun j => Fin.cases h0n57_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n57 : h0e57.toBi mapPolyEnv=h0p57 := by
  change BiPoly.mul (h0e36.toBi mapPolyEnv) (h0e54.toBi mapPolyEnv)=h0p57
  rw [h0n36, h0n54]
  exact h0n57_arithmetic

#print axioms h0n57_arithmetic
end StackSorting.RationalLift
