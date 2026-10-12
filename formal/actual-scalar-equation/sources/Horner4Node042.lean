import BivariateRowEquality
import Horner4Base
import Horner4Node041
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p42 : BiPoly.Poly := [[(Int.ofNat 12188377521271872000), (Int.ofNat 55599384275483800320), (Int.negSucc 80919709658290506239), (Int.negSucc 288074019497934412799), (Int.ofNat 527636452376348651520), (Int.negSucc 226430485016879404799)], [(Int.negSucc 112554732142843361279), (Int.negSucc 519557244390171311615), (Int.ofNat 698192677112350129920), (Int.ofNat 2584898257359577556736), (Int.negSucc 4731795833368066585343), (Int.ofNat 2244841104616736880384), (Int.negSucc 164024229187583308799)], [(Int.ofNat 489962957865347203200), (Int.ofNat 2188384925570977809600), (Int.negSucc 2810837421638326113983), (Int.negSucc 10001083514257160445311), (Int.ofNat 17745957747765723315456), (Int.negSucc 8383707661199797788479), (Int.ofNat 809779051625827514688), (Int.negSucc 38456085732591495167)], [(Int.negSucc 1332139476298302011519), (Int.negSucc 5485697818774397668799), (Int.ofNat 6763213437250502702016), (Int.ofNat 21377424834404375322240), (Int.negSucc 34268150007238013596799), (Int.ofNat 13206816256722774187968), (Int.negSucc 272397507821303500223), (Int.ofNat 13755289561384593024), (Int.negSucc 2825007807020027903)], [(Int.ofNat 2518433010451427425920), (Int.ofNat 9147752014288610069568), (Int.negSucc 10356470200156310496575), (Int.negSucc 26701113064708502634239), (Int.ofNat 30476782839003753884544), (Int.ofNat 150748171432332704064), (Int.negSucc 5734316553878685479615), (Int.ofNat 513573445040321499264), (Int.negSucc 15404718048324565247), (Int.ofNat 15056575377592320)], [(Int.negSucc 3480985317147694591679), (Int.negSucc 10832684844400312442975), (Int.ofNat 9751379401783354444416), (Int.ofNat 18030626154423386684640), (Int.ofNat 5540123142896340041280), (Int.negSucc 32060975259539802148127), (Int.ofNat 13822612565379589733760), (Int.negSucc 791575622193980871647), (Int.ofNat 21971750980376547072), (Int.negSucc 491972181257396735)], [(Int.ofNat 3600576742097602344000), (Int.ofNat 9634752780434238388704), (Int.negSucc 4077287558596862513951), (Int.negSucc 3270538896786609030527), (Int.negSucc 41580113859930664899647), (Int.ofNat 45472339823914433248032), (Int.negSucc 8373958768053606843359), (Int.negSucc 1527428586054990748991), (Int.ofNat 124593105070961035968), (Int.negSucc 2934782094500980223)], [(Int.negSucc 2809034540327461302719), (Int.negSucc 6867592394535418144415), (Int.negSucc 2717139887889074402303), (Int.negSucc 3662340118720659068063), (Int.ofNat 39811364202816811431744), (Int.negSucc 16347255575375617360799), (Int.negSucc 11992989042726673556543), (Int.ofNat 4758955136623797338784), (Int.negSucc 173870621744753280767), (Int.negSucc 97158120951654911)], [(Int.ofNat 1648380879885005242560), (Int.ofNat 4198470739627961654880), (Int.ofNat 6216924815675542200864), (Int.ofNat 1580096418129209644800), (Int.negSucc 11721966876935349862271), (Int.negSucc 20554726735310391241247), (Int.ofNat 21763004941133800216992), (Int.negSucc 2850054834164090931455), (Int.negSucc 295941270192953880767), (Int.ofNat 15811922151266955648)], [(Int.negSucc 718735019287944461759), (Int.negSucc 2266616040158293634207), (Int.negSucc 5749193555912972824607), (Int.ofNat 1086370788156830149248), (Int.negSucc 6523936783939706844959), (Int.ofNat 25463085591915610317984), (Int.negSucc 8970534168248218384223), (Int.negSucc 2975056741202420341343), (Int.ofNat 654019133693012404896), (Int.ofNat 596794984103618976)], [(Int.ofNat 227474907036787076160), (Int.ofNat 1039505835615696593568), (Int.ofNat 3497301298215913335552), (Int.negSucc 604350643440836278079), (Int.ofNat 6115343214467798829792), (Int.negSucc 8898879337957614532991), (Int.negSucc 5768840310646095975839), (Int.ofNat 4569896525393430560832), (Int.negSucc 142502917064862484319), (Int.negSucc 34948571620217124671)], [(Int.negSucc 50202890264633595839), (Int.negSucc 375766641689646535583), (Int.negSucc 1520467960190378939519), (Int.negSucc 630093140506273999967), (Int.negSucc 1056653991931935544319), (Int.negSucc 1731895368425492049215), (Int.ofNat 7060904464557307305408), (Int.negSucc 1252451082976804174079), (Int.negSucc 458594502410487686783), (Int.ofNat 15221113838345219904)], [(Int.ofNat 7201468323874219200), (Int.ofNat 99540803439624591456), (Int.ofNat 475643021881409303136), (Int.ofNat 802760194598680142400), (Int.negSucc 565358599894181557823), (Int.ofNat 2123278659353232083520), (Int.negSucc 2197376173978312710719), (Int.negSucc 1110860280151090391231), (Int.ofNat 340903369488599121024), (Int.ofNat 24267536938165199040)], [(Int.negSucc 585504088604492159), (Int.negSucc 17974079506289144063), (Int.negSucc 104260287138119659295), (Int.negSucc 397453087803229474847), (Int.ofNat 228085675469422099104), (Int.negSucc 399065629778288525663), (Int.negSucc 197939640040121916287), (Int.ofNat 896350587187828390272), (Int.ofNat 13272612699393937152), (Int.negSucc 20430647001991214207)], [(Int.ofNat 19136376168433920), (Int.ofNat 1985070331653089472), (Int.ofNat 15212187191104786080), (Int.ofNat 108169703477460131904), (Int.ofNat 28708567822101062304), (Int.negSucc 102728192520299404607), (Int.ofNat 258030904818948133248), (Int.negSucc 208483774792608708863), (Int.negSucc 100149132712219622783), (Int.negSucc 764469992307900671)], [(Int.ofNat 0), (Int.negSucc 102490129717115903), (Int.negSucc 1347216668984985983), (Int.negSucc 16503371115717604031), (Int.negSucc 32941411036816674815), (Int.ofNat 49784294142328646592), (Int.negSucc 39082602783894746111), (Int.negSucc 6967144377139022207), (Int.ofNat 41399962421487351552), (Int.ofNat 5759979548454150912)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 56958739143540480), (Int.ofNat 1228206277612672704), (Int.ofNat 7582512967253861760), (Int.negSucc 4811997245414516927), (Int.negSucc 5747674962002242175), (Int.ofNat 10190906871796714752), (Int.negSucc 6354846376934151167), (Int.negSucc 2144066271455879423)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 23969037185049599), (Int.negSucc 665037638628233471), (Int.negSucc 591859329188647679), (Int.ofNat 2238340401231439104), (Int.negSucc 1478538040668523775), (Int.ofNat 271280146896912384), (Int.ofNat 249783497542103040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7702665848626176), (Int.ofNat 116210552033523456), (Int.negSucc 204600718687859711), (Int.ofNat 80687500805710080)]]

theorem h4n42_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p41).getD 0 []=h4p42.getD 0 [] := by
  decide +kernel

theorem h4n42_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p41).getD 1 []=h4p42.getD 1 [] := by
  decide +kernel

theorem h4n42_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p41).getD 2 []=h4p42.getD 2 [] := by
  decide +kernel

theorem h4n42_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p41).getD 3 []=h4p42.getD 3 [] := by
  decide +kernel

theorem h4n42_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p41).getD 4 []=h4p42.getD 4 [] := by
  decide +kernel

theorem h4n42_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p41).getD 5 []=h4p42.getD 5 [] := by
  decide +kernel

theorem h4n42_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p41).getD 6 []=h4p42.getD 6 [] := by
  decide +kernel

theorem h4n42_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p41).getD 7 []=h4p42.getD 7 [] := by
  decide +kernel

theorem h4n42_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p41).getD 8 []=h4p42.getD 8 [] := by
  decide +kernel

theorem h4n42_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p41).getD 9 []=h4p42.getD 9 [] := by
  decide +kernel

theorem h4n42_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p41).getD 10 []=h4p42.getD 10 [] := by
  decide +kernel

theorem h4n42_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p41).getD 11 []=h4p42.getD 11 [] := by
  decide +kernel

theorem h4n42_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p41).getD 12 []=h4p42.getD 12 [] := by
  decide +kernel

theorem h4n42_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p41).getD 13 []=h4p42.getD 13 [] := by
  decide +kernel

theorem h4n42_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p41).getD 14 []=h4p42.getD 14 [] := by
  decide +kernel

theorem h4n42_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p41).getD 15 []=h4p42.getD 15 [] := by
  decide +kernel

theorem h4n42_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p41).getD 16 []=h4p42.getD 16 [] := by
  decide +kernel

theorem h4n42_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p41).getD 17 []=h4p42.getD 17 [] := by
  decide +kernel

theorem h4n42_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p41).getD 18 []=h4p42.getD 18 [] := by
  decide +kernel

theorem h4n42_arithmetic : BiPoly.mul h4p13 h4p41=h4p42 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p41).getD j.val []=h4p42.getD j.val [] :=
      (fun j => Fin.cases h4n42_arithmetic_row0 (fun j => Fin.cases h4n42_arithmetic_row1 (fun j => Fin.cases h4n42_arithmetic_row2 (fun j => Fin.cases h4n42_arithmetic_row3 (fun j => Fin.cases h4n42_arithmetic_row4 (fun j => Fin.cases h4n42_arithmetic_row5 (fun j => Fin.cases h4n42_arithmetic_row6 (fun j => Fin.cases h4n42_arithmetic_row7 (fun j => Fin.cases h4n42_arithmetic_row8 (fun j => Fin.cases h4n42_arithmetic_row9 (fun j => Fin.cases h4n42_arithmetic_row10 (fun j => Fin.cases h4n42_arithmetic_row11 (fun j => Fin.cases h4n42_arithmetic_row12 (fun j => Fin.cases h4n42_arithmetic_row13 (fun j => Fin.cases h4n42_arithmetic_row14 (fun j => Fin.cases h4n42_arithmetic_row15 (fun j => Fin.cases h4n42_arithmetic_row16 (fun j => Fin.cases h4n42_arithmetic_row17 (fun j => Fin.cases h4n42_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n42 : h4e42.toBi mapPolyEnv=h4p42 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e41.toBi mapPolyEnv)=h4p42
  rw [h4n13, h4n41]
  exact h4n42_arithmetic

#print axioms h4n42_arithmetic
end StackSorting.RationalLift
