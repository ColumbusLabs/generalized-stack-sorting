import BivariateRowEquality
import Horner4Base
import Horner4Node018
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p19 : BiPoly.Poly := [[(Int.negSucc 12188377521271871999), (Int.negSucc 55599384275483800319), (Int.ofNat 80919709658290506240), (Int.ofNat 288074019497934412800), (Int.negSucc 527636452376348651519), (Int.ofNat 226430485016879404800)], [(Int.ofNat 112554732142843361280), (Int.ofNat 519557244390171311616), (Int.negSucc 698192677112350129919), (Int.negSucc 2584898257359577556735), (Int.ofNat 4731795833368066585344), (Int.negSucc 2244841104616736880383), (Int.ofNat 164024229187583308800)], [(Int.negSucc 489962957865347203199), (Int.negSucc 2188384925570977809599), (Int.ofNat 2810837421638326113984), (Int.ofNat 10001083514257160445312), (Int.negSucc 17745957747765723315455), (Int.ofNat 8383707661199797788480), (Int.negSucc 809779051625827514687), (Int.ofNat 38456085732591495168)], [(Int.ofNat 1332139476298302011520), (Int.ofNat 5485697818774397668800), (Int.negSucc 6763213437250502702015), (Int.negSucc 21377424834404375322239), (Int.ofNat 34268150007238013596800), (Int.negSucc 13206816256722774187967), (Int.ofNat 272397507821303500224), (Int.negSucc 13755289561384593023), (Int.ofNat 2825007807020027904)], [(Int.negSucc 2518433010451427425919), (Int.negSucc 9147752014288610069567), (Int.ofNat 10356470200156310496576), (Int.ofNat 26701113064708502634240), (Int.negSucc 30476782839003753884543), (Int.negSucc 150748171432332704063), (Int.ofNat 5734316553878685479616), (Int.negSucc 513573445040321499263), (Int.ofNat 15404718048324565248), (Int.negSucc 15056575377592319)], [(Int.ofNat 3480985317147694591680), (Int.ofNat 10832684844400312442976), (Int.negSucc 9751379401783354444415), (Int.negSucc 18030626154423386684639), (Int.negSucc 5540123142896340041279), (Int.ofNat 32060975259539802148128), (Int.negSucc 13822612565379589733759), (Int.ofNat 791575622193980871648), (Int.negSucc 21971750980376547071), (Int.ofNat 491972181257396736)], [(Int.negSucc 3600576742097602343999), (Int.negSucc 9634752780434238388703), (Int.ofNat 4077287558596862513952), (Int.ofNat 3270538896786609030528), (Int.ofNat 41580113859930664899648), (Int.negSucc 45472339823914433248031), (Int.ofNat 8373958768053606843360), (Int.ofNat 1527428586054990748992), (Int.negSucc 124593105070961035967), (Int.ofNat 2934782094500980224)], [(Int.ofNat 2809034540327461302720), (Int.ofNat 6867592394535418144416), (Int.ofNat 2717139887889074402304), (Int.ofNat 3662340118720659068064), (Int.negSucc 39811364202816811431743), (Int.ofNat 16347255575375617360800), (Int.ofNat 11992989042726673556544), (Int.negSucc 4758955136623797338783), (Int.ofNat 173870621744753280768), (Int.ofNat 97158120951654912)], [(Int.negSucc 1648380879885005242559), (Int.negSucc 4198470739627961654879), (Int.negSucc 6216924815675542200863), (Int.negSucc 1580096418129209644799), (Int.ofNat 11721966876935349862272), (Int.ofNat 20554726735310391241248), (Int.negSucc 21763004941133800216991), (Int.ofNat 2850054834164090931456), (Int.ofNat 295941270192953880768), (Int.negSucc 15811922151266955647)], [(Int.ofNat 718735019287944461760), (Int.ofNat 2266616040158293634208), (Int.ofNat 5749193555912972824608), (Int.negSucc 1086370788156830149247), (Int.ofNat 6523936783939706844960), (Int.negSucc 25463085591915610317983), (Int.ofNat 8970534168248218384224), (Int.ofNat 2975056741202420341344), (Int.negSucc 654019133693012404895), (Int.negSucc 596794984103618975)], [(Int.negSucc 227474907036787076159), (Int.negSucc 1039505835615696593567), (Int.negSucc 3497301298215913335551), (Int.ofNat 604350643440836278080), (Int.negSucc 6115343214467798829791), (Int.ofNat 8898879337957614532992), (Int.ofNat 5768840310646095975840), (Int.negSucc 4569896525393430560831), (Int.ofNat 142502917064862484320), (Int.ofNat 34948571620217124672)], [(Int.ofNat 50202890264633595840), (Int.ofNat 375766641689646535584), (Int.ofNat 1520467960190378939520), (Int.ofNat 630093140506273999968), (Int.ofNat 1056653991931935544320), (Int.ofNat 1731895368425492049216), (Int.negSucc 7060904464557307305407), (Int.ofNat 1252451082976804174080), (Int.ofNat 458594502410487686784), (Int.negSucc 15221113838345219903)], [(Int.negSucc 7201468323874219199), (Int.negSucc 99540803439624591455), (Int.negSucc 475643021881409303135), (Int.negSucc 802760194598680142399), (Int.ofNat 565358599894181557824), (Int.negSucc 2123278659353232083519), (Int.ofNat 2197376173978312710720), (Int.ofNat 1110860280151090391232), (Int.negSucc 340903369488599121023), (Int.negSucc 24267536938165199039)], [(Int.ofNat 585504088604492160), (Int.ofNat 17974079506289144064), (Int.ofNat 104260287138119659296), (Int.ofNat 397453087803229474848), (Int.negSucc 228085675469422099103), (Int.ofNat 399065629778288525664), (Int.ofNat 197939640040121916288), (Int.negSucc 896350587187828390271), (Int.negSucc 13272612699393937151), (Int.ofNat 20430647001991214208)], [(Int.negSucc 19136376168433919), (Int.negSucc 1985070331653089471), (Int.negSucc 15212187191104786079), (Int.negSucc 108169703477460131903), (Int.negSucc 28708567822101062303), (Int.ofNat 102728192520299404608), (Int.negSucc 258030904818948133247), (Int.ofNat 208483774792608708864), (Int.ofNat 100149132712219622784), (Int.ofNat 764469992307900672)], [(Int.ofNat 0), (Int.ofNat 102490129717115904), (Int.ofNat 1347216668984985984), (Int.ofNat 16503371115717604032), (Int.ofNat 32941411036816674816), (Int.negSucc 49784294142328646591), (Int.ofNat 39082602783894746112), (Int.ofNat 6967144377139022208), (Int.negSucc 41399962421487351551), (Int.negSucc 5759979548454150911)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 56958739143540479), (Int.negSucc 1228206277612672703), (Int.negSucc 7582512967253861759), (Int.ofNat 4811997245414516928), (Int.ofNat 5747674962002242176), (Int.negSucc 10190906871796714751), (Int.ofNat 6354846376934151168), (Int.ofNat 2144066271455879424)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 23969037185049600), (Int.ofNat 665037638628233472), (Int.ofNat 591859329188647680), (Int.negSucc 2238340401231439103), (Int.ofNat 1478538040668523776), (Int.negSucc 271280146896912383), (Int.negSucc 249783497542103039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7702665848626175), (Int.negSucc 116210552033523455), (Int.ofNat 204600718687859712), (Int.negSucc 80687500805710079)]]

theorem h4n19_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p18).getD 0 []=h4p19.getD 0 [] := by
  decide +kernel

theorem h4n19_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p18).getD 1 []=h4p19.getD 1 [] := by
  decide +kernel

theorem h4n19_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p18).getD 2 []=h4p19.getD 2 [] := by
  decide +kernel

theorem h4n19_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p18).getD 3 []=h4p19.getD 3 [] := by
  decide +kernel

theorem h4n19_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p18).getD 4 []=h4p19.getD 4 [] := by
  decide +kernel

theorem h4n19_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p18).getD 5 []=h4p19.getD 5 [] := by
  decide +kernel

theorem h4n19_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p18).getD 6 []=h4p19.getD 6 [] := by
  decide +kernel

theorem h4n19_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p18).getD 7 []=h4p19.getD 7 [] := by
  decide +kernel

theorem h4n19_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p18).getD 8 []=h4p19.getD 8 [] := by
  decide +kernel

theorem h4n19_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p18).getD 9 []=h4p19.getD 9 [] := by
  decide +kernel

theorem h4n19_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p18).getD 10 []=h4p19.getD 10 [] := by
  decide +kernel

theorem h4n19_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p18).getD 11 []=h4p19.getD 11 [] := by
  decide +kernel

theorem h4n19_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p18).getD 12 []=h4p19.getD 12 [] := by
  decide +kernel

theorem h4n19_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p18).getD 13 []=h4p19.getD 13 [] := by
  decide +kernel

theorem h4n19_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p18).getD 14 []=h4p19.getD 14 [] := by
  decide +kernel

theorem h4n19_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p18).getD 15 []=h4p19.getD 15 [] := by
  decide +kernel

theorem h4n19_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p18).getD 16 []=h4p19.getD 16 [] := by
  decide +kernel

theorem h4n19_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p18).getD 17 []=h4p19.getD 17 [] := by
  decide +kernel

theorem h4n19_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p18).getD 18 []=h4p19.getD 18 [] := by
  decide +kernel

theorem h4n19_arithmetic : BiPoly.mul h4p13 h4p18=h4p19 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p18).getD j.val []=h4p19.getD j.val [] :=
      (fun j => Fin.cases h4n19_arithmetic_row0 (fun j => Fin.cases h4n19_arithmetic_row1 (fun j => Fin.cases h4n19_arithmetic_row2 (fun j => Fin.cases h4n19_arithmetic_row3 (fun j => Fin.cases h4n19_arithmetic_row4 (fun j => Fin.cases h4n19_arithmetic_row5 (fun j => Fin.cases h4n19_arithmetic_row6 (fun j => Fin.cases h4n19_arithmetic_row7 (fun j => Fin.cases h4n19_arithmetic_row8 (fun j => Fin.cases h4n19_arithmetic_row9 (fun j => Fin.cases h4n19_arithmetic_row10 (fun j => Fin.cases h4n19_arithmetic_row11 (fun j => Fin.cases h4n19_arithmetic_row12 (fun j => Fin.cases h4n19_arithmetic_row13 (fun j => Fin.cases h4n19_arithmetic_row14 (fun j => Fin.cases h4n19_arithmetic_row15 (fun j => Fin.cases h4n19_arithmetic_row16 (fun j => Fin.cases h4n19_arithmetic_row17 (fun j => Fin.cases h4n19_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n19 : h4e19.toBi mapPolyEnv=h4p19 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e18.toBi mapPolyEnv)=h4p19
  rw [h4n13, h4n18]
  exact h4n19_arithmetic

#print axioms h4n19_arithmetic
end StackSorting.RationalLift
