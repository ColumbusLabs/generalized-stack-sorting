import BivariateRowEquality
import Horner4Base
import Horner4Node199
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p200 : BiPoly.Poly := [[(Int.ofNat 4062792507090624000), (Int.ofNat 18533128091827933440), (Int.negSucc 26973236552763502079), (Int.negSucc 96024673165978137599), (Int.ofNat 175878817458782883840), (Int.negSucc 75476828338959801599)], [(Int.negSucc 37518244047614453759), (Int.negSucc 173185748130057103871), (Int.ofNat 232730892370783376640), (Int.ofNat 861632752453192518912), (Int.negSucc 1577265277789355528447), (Int.ofNat 748280368205578960128), (Int.negSucc 54674743062527769599)], [(Int.ofNat 163320985955115734400), (Int.ofNat 729461641856992603200), (Int.negSucc 936945807212775371327), (Int.negSucc 3333694504752386815103), (Int.ofNat 5915319249255241105152), (Int.negSucc 2794569220399932596159), (Int.ofNat 269926350541942504896), (Int.negSucc 12818695244197165055)], [(Int.negSucc 444046492099434003839), (Int.negSucc 1828565939591465889599), (Int.ofNat 2254404479083500900672), (Int.ofNat 7125808278134791774080), (Int.negSucc 11422716669079337865599), (Int.ofNat 4402272085574258062656), (Int.negSucc 90799169273767833407), (Int.ofNat 4585096520461531008), (Int.negSucc 941669269006675967)], [(Int.ofNat 839477670150475808640), (Int.ofNat 3049250671429536689856), (Int.negSucc 3452156733385436832191), (Int.negSucc 8900371021569500878079), (Int.ofNat 10158927613001251294848), (Int.ofNat 50249390477444234688), (Int.negSucc 1911438851292895159871), (Int.ofNat 171191148346773833088), (Int.negSucc 5134906016108188415), (Int.ofNat 5018858459197440)], [(Int.negSucc 1160328439049231530559), (Int.negSucc 3610894948133437480991), (Int.ofNat 3250459800594451481472), (Int.ofNat 6010208718141128894880), (Int.ofNat 1846707714298780013760), (Int.negSucc 10686991753179934049375), (Int.ofNat 4607537521793196577920), (Int.negSucc 263858540731326957215), (Int.ofNat 7323916993458849024), (Int.negSucc 163990727085798911)], [(Int.ofNat 1200192247365867448000), (Int.ofNat 3211584260144746129568), (Int.negSucc 1359095852865620837983), (Int.negSucc 1090179632262203010175), (Int.negSucc 13860037953310221633215), (Int.ofNat 15157446607971477749344), (Int.negSucc 2791319589351202281119), (Int.negSucc 509142862018330249663), (Int.ofNat 41531035023653678656), (Int.negSucc 978260698166993407)], [(Int.negSucc 936344846775820434239), (Int.negSucc 2289197464845139381471), (Int.negSucc 905713295963024800767), (Int.negSucc 1220780039573553022687), (Int.ofNat 13270454734272270477248), (Int.negSucc 5449085191791872453599), (Int.negSucc 3997663014242224518847), (Int.ofNat 1586318378874599112928), (Int.negSucc 57956873914917760255), (Int.negSucc 32386040317218303)], [(Int.ofNat 549460293295001747520), (Int.ofNat 1399490246542653884960), (Int.ofNat 2072308271891847400288), (Int.ofNat 526698806043069881600), (Int.negSucc 3907322292311783287423), (Int.negSucc 6851575578436797080415), (Int.ofNat 7254334980377933405664), (Int.negSucc 950018278054696977151), (Int.negSucc 98647090064317960255), (Int.ofNat 5270640717088985216)], [(Int.negSucc 239578339762648153919), (Int.negSucc 755538680052764544735), (Int.negSucc 1916397851970990941535), (Int.ofNat 362123596052276716416), (Int.negSucc 2174645594646568948319), (Int.ofNat 8487695197305203439328), (Int.negSucc 2990178056082739461407), (Int.negSucc 991685580400806780447), (Int.ofNat 218006377897670801632), (Int.ofNat 198931661367872992)], [(Int.ofNat 75824969012262358720), (Int.ofNat 346501945205232197856), (Int.ofNat 1165767099405304445184), (Int.negSucc 201450214480278759359), (Int.ofNat 2038447738155932943264), (Int.negSucc 2966293112652538177663), (Int.negSucc 1922946770215365325279), (Int.ofNat 1523298841797810186944), (Int.negSucc 47500972354954161439), (Int.negSucc 11649523873405708223)], [(Int.negSucc 16734296754877865279), (Int.negSucc 125255547229882178527), (Int.negSucc 506822653396792979839), (Int.negSucc 210031046835424666655), (Int.negSucc 352217997310645181439), (Int.negSucc 577298456141830683071), (Int.ofNat 2353634821519102435136), (Int.negSucc 417483694325601391359), (Int.negSucc 152864834136829228927), (Int.ofNat 5073704612781739968)], [(Int.ofNat 2400489441291406400), (Int.ofNat 33180267813208197152), (Int.ofNat 158547673960469767712), (Int.ofNat 267586731532893380800), (Int.negSucc 188452866631393852607), (Int.ofNat 707759553117744027840), (Int.negSucc 732458724659437570239), (Int.negSucc 370286760050363463743), (Int.ofNat 113634456496199707008), (Int.ofNat 8089178979388399680)], [(Int.negSucc 195168029534830719), (Int.negSucc 5991359835429714687), (Int.negSucc 34753429046039886431), (Int.negSucc 132484362601076491615), (Int.ofNat 76028558489807366368), (Int.negSucc 133021876592762841887), (Int.negSucc 65979880013373972095), (Int.ofNat 298783529062609463424), (Int.ofNat 4424204233131312384), (Int.negSucc 6810215667330404735)], [(Int.ofNat 6378792056144640), (Int.ofNat 661690110551029824), (Int.ofNat 5070729063701595360), (Int.ofNat 36056567825820043968), (Int.ofNat 9569522607367020768), (Int.negSucc 34242730840099801535), (Int.ofNat 86010301606316044416), (Int.negSucc 69494591597536236287), (Int.negSucc 33383044237406540927), (Int.negSucc 254823330769300223)], [(Int.ofNat 0), (Int.negSucc 34163376572371967), (Int.negSucc 449072222994995327), (Int.negSucc 5501123705239201343), (Int.negSucc 10980470345605558271), (Int.ofNat 16594764714109548864), (Int.negSucc 13027534261298248703), (Int.negSucc 2322381459046340735), (Int.ofNat 13799987473829117184), (Int.ofNat 1919993182818050304)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 18986246381180160), (Int.ofNat 409402092537557568), (Int.ofNat 2527504322417953920), (Int.negSucc 1603999081804838975), (Int.negSucc 1915891654000747391), (Int.ofNat 3396968957265571584), (Int.negSucc 2118282125644717055), (Int.negSucc 714688757151959807)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7989679061683199), (Int.negSucc 221679212876077823), (Int.negSucc 197286443062882559), (Int.ofNat 746113467077146368), (Int.negSucc 492846013556174591), (Int.ofNat 90426715632304128), (Int.ofNat 83261165847367680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2567555282875392), (Int.ofNat 38736850677841152), (Int.negSucc 68200239562619903), (Int.ofNat 26895833601903360)]]

theorem h4n200_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p199).getD 0 []=h4p200.getD 0 [] := by
  decide +kernel

theorem h4n200_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p199).getD 1 []=h4p200.getD 1 [] := by
  decide +kernel

theorem h4n200_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p199).getD 2 []=h4p200.getD 2 [] := by
  decide +kernel

theorem h4n200_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p199).getD 3 []=h4p200.getD 3 [] := by
  decide +kernel

theorem h4n200_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p199).getD 4 []=h4p200.getD 4 [] := by
  decide +kernel

theorem h4n200_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p199).getD 5 []=h4p200.getD 5 [] := by
  decide +kernel

theorem h4n200_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p199).getD 6 []=h4p200.getD 6 [] := by
  decide +kernel

theorem h4n200_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p199).getD 7 []=h4p200.getD 7 [] := by
  decide +kernel

theorem h4n200_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p199).getD 8 []=h4p200.getD 8 [] := by
  decide +kernel

theorem h4n200_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p199).getD 9 []=h4p200.getD 9 [] := by
  decide +kernel

theorem h4n200_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p199).getD 10 []=h4p200.getD 10 [] := by
  decide +kernel

theorem h4n200_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p199).getD 11 []=h4p200.getD 11 [] := by
  decide +kernel

theorem h4n200_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p199).getD 12 []=h4p200.getD 12 [] := by
  decide +kernel

theorem h4n200_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p199).getD 13 []=h4p200.getD 13 [] := by
  decide +kernel

theorem h4n200_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p199).getD 14 []=h4p200.getD 14 [] := by
  decide +kernel

theorem h4n200_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p199).getD 15 []=h4p200.getD 15 [] := by
  decide +kernel

theorem h4n200_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p199).getD 16 []=h4p200.getD 16 [] := by
  decide +kernel

theorem h4n200_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p199).getD 17 []=h4p200.getD 17 [] := by
  decide +kernel

theorem h4n200_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p199).getD 18 []=h4p200.getD 18 [] := by
  decide +kernel

theorem h4n200_arithmetic : BiPoly.mul h4p13 h4p199=h4p200 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p199).getD j.val []=h4p200.getD j.val [] :=
      (fun j => Fin.cases h4n200_arithmetic_row0 (fun j => Fin.cases h4n200_arithmetic_row1 (fun j => Fin.cases h4n200_arithmetic_row2 (fun j => Fin.cases h4n200_arithmetic_row3 (fun j => Fin.cases h4n200_arithmetic_row4 (fun j => Fin.cases h4n200_arithmetic_row5 (fun j => Fin.cases h4n200_arithmetic_row6 (fun j => Fin.cases h4n200_arithmetic_row7 (fun j => Fin.cases h4n200_arithmetic_row8 (fun j => Fin.cases h4n200_arithmetic_row9 (fun j => Fin.cases h4n200_arithmetic_row10 (fun j => Fin.cases h4n200_arithmetic_row11 (fun j => Fin.cases h4n200_arithmetic_row12 (fun j => Fin.cases h4n200_arithmetic_row13 (fun j => Fin.cases h4n200_arithmetic_row14 (fun j => Fin.cases h4n200_arithmetic_row15 (fun j => Fin.cases h4n200_arithmetic_row16 (fun j => Fin.cases h4n200_arithmetic_row17 (fun j => Fin.cases h4n200_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n200 : h4e200.toBi mapPolyEnv=h4p200 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e199.toBi mapPolyEnv)=h4p200
  rw [h4n13, h4n199]
  exact h4n200_arithmetic

#print axioms h4n200_arithmetic
end StackSorting.RationalLift
