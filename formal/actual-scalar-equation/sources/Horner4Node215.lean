import BivariateRowEquality
import Horner4Base
import Horner4Node214
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p215 : BiPoly.Poly := [[(Int.negSucc 4062792507090623999), (Int.negSucc 18533128091827933439), (Int.ofNat 26973236552763502080), (Int.ofNat 96024673165978137600), (Int.negSucc 175878817458782883839), (Int.ofNat 75476828338959801600)], [(Int.ofNat 37518244047614453760), (Int.ofNat 173185748130057103872), (Int.negSucc 232730892370783376639), (Int.negSucc 861632752453192518911), (Int.ofNat 1577265277789355528448), (Int.negSucc 748280368205578960127), (Int.ofNat 54674743062527769600)], [(Int.negSucc 163320985955115734399), (Int.negSucc 729461641856992603199), (Int.ofNat 936945807212775371328), (Int.ofNat 3333694504752386815104), (Int.negSucc 5915319249255241105151), (Int.ofNat 2794569220399932596160), (Int.negSucc 269926350541942504895), (Int.ofNat 12818695244197165056)], [(Int.ofNat 444046492099434003840), (Int.ofNat 1828565939591465889600), (Int.negSucc 2254404479083500900671), (Int.negSucc 7125808278134791774079), (Int.ofNat 11422716669079337865600), (Int.negSucc 4402272085574258062655), (Int.ofNat 90799169273767833408), (Int.negSucc 4585096520461531007), (Int.ofNat 941669269006675968)], [(Int.negSucc 839477670150475808639), (Int.negSucc 3049250671429536689855), (Int.ofNat 3452156733385436832192), (Int.ofNat 8900371021569500878080), (Int.negSucc 10158927613001251294847), (Int.negSucc 50249390477444234687), (Int.ofNat 1911438851292895159872), (Int.negSucc 171191148346773833087), (Int.ofNat 5134906016108188416), (Int.negSucc 5018858459197439)], [(Int.ofNat 1160328439049231530560), (Int.ofNat 3610894948133437480992), (Int.negSucc 3250459800594451481471), (Int.negSucc 6010208718141128894879), (Int.negSucc 1846707714298780013759), (Int.ofNat 10686991753179934049376), (Int.negSucc 4607537521793196577919), (Int.ofNat 263858540731326957216), (Int.negSucc 7323916993458849023), (Int.ofNat 163990727085798912)], [(Int.negSucc 1200192247365867447999), (Int.negSucc 3211584260144746129567), (Int.ofNat 1359095852865620837984), (Int.ofNat 1090179632262203010176), (Int.ofNat 13860037953310221633216), (Int.negSucc 15157446607971477749343), (Int.ofNat 2791319589351202281120), (Int.ofNat 509142862018330249664), (Int.negSucc 41531035023653678655), (Int.ofNat 978260698166993408)], [(Int.ofNat 936344846775820434240), (Int.ofNat 2289197464845139381472), (Int.ofNat 905713295963024800768), (Int.ofNat 1220780039573553022688), (Int.negSucc 13270454734272270477247), (Int.ofNat 5449085191791872453600), (Int.ofNat 3997663014242224518848), (Int.negSucc 1586318378874599112927), (Int.ofNat 57956873914917760256), (Int.ofNat 32386040317218304)], [(Int.negSucc 549460293295001747519), (Int.negSucc 1399490246542653884959), (Int.negSucc 2072308271891847400287), (Int.negSucc 526698806043069881599), (Int.ofNat 3907322292311783287424), (Int.ofNat 6851575578436797080416), (Int.negSucc 7254334980377933405663), (Int.ofNat 950018278054696977152), (Int.ofNat 98647090064317960256), (Int.negSucc 5270640717088985215)], [(Int.ofNat 239578339762648153920), (Int.ofNat 755538680052764544736), (Int.ofNat 1916397851970990941536), (Int.negSucc 362123596052276716415), (Int.ofNat 2174645594646568948320), (Int.negSucc 8487695197305203439327), (Int.ofNat 2990178056082739461408), (Int.ofNat 991685580400806780448), (Int.negSucc 218006377897670801631), (Int.negSucc 198931661367872991)], [(Int.negSucc 75824969012262358719), (Int.negSucc 346501945205232197855), (Int.negSucc 1165767099405304445183), (Int.ofNat 201450214480278759360), (Int.negSucc 2038447738155932943263), (Int.ofNat 2966293112652538177664), (Int.ofNat 1922946770215365325280), (Int.negSucc 1523298841797810186943), (Int.ofNat 47500972354954161440), (Int.ofNat 11649523873405708224)], [(Int.ofNat 16734296754877865280), (Int.ofNat 125255547229882178528), (Int.ofNat 506822653396792979840), (Int.ofNat 210031046835424666656), (Int.ofNat 352217997310645181440), (Int.ofNat 577298456141830683072), (Int.negSucc 2353634821519102435135), (Int.ofNat 417483694325601391360), (Int.ofNat 152864834136829228928), (Int.negSucc 5073704612781739967)], [(Int.negSucc 2400489441291406399), (Int.negSucc 33180267813208197151), (Int.negSucc 158547673960469767711), (Int.negSucc 267586731532893380799), (Int.ofNat 188452866631393852608), (Int.negSucc 707759553117744027839), (Int.ofNat 732458724659437570240), (Int.ofNat 370286760050363463744), (Int.negSucc 113634456496199707007), (Int.negSucc 8089178979388399679)], [(Int.ofNat 195168029534830720), (Int.ofNat 5991359835429714688), (Int.ofNat 34753429046039886432), (Int.ofNat 132484362601076491616), (Int.negSucc 76028558489807366367), (Int.ofNat 133021876592762841888), (Int.ofNat 65979880013373972096), (Int.negSucc 298783529062609463423), (Int.negSucc 4424204233131312383), (Int.ofNat 6810215667330404736)], [(Int.negSucc 6378792056144639), (Int.negSucc 661690110551029823), (Int.negSucc 5070729063701595359), (Int.negSucc 36056567825820043967), (Int.negSucc 9569522607367020767), (Int.ofNat 34242730840099801536), (Int.negSucc 86010301606316044415), (Int.ofNat 69494591597536236288), (Int.ofNat 33383044237406540928), (Int.ofNat 254823330769300224)], [(Int.ofNat 0), (Int.ofNat 34163376572371968), (Int.ofNat 449072222994995328), (Int.ofNat 5501123705239201344), (Int.ofNat 10980470345605558272), (Int.negSucc 16594764714109548863), (Int.ofNat 13027534261298248704), (Int.ofNat 2322381459046340736), (Int.negSucc 13799987473829117183), (Int.negSucc 1919993182818050303)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 18986246381180159), (Int.negSucc 409402092537557567), (Int.negSucc 2527504322417953919), (Int.ofNat 1603999081804838976), (Int.ofNat 1915891654000747392), (Int.negSucc 3396968957265571583), (Int.ofNat 2118282125644717056), (Int.ofNat 714688757151959808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7989679061683200), (Int.ofNat 221679212876077824), (Int.ofNat 197286443062882560), (Int.negSucc 746113467077146367), (Int.ofNat 492846013556174592), (Int.negSucc 90426715632304127), (Int.negSucc 83261165847367679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2567555282875391), (Int.negSucc 38736850677841151), (Int.ofNat 68200239562619904), (Int.negSucc 26895833601903359)]]

theorem h4n215_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p214).getD 0 []=h4p215.getD 0 [] := by
  decide +kernel

theorem h4n215_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p214).getD 1 []=h4p215.getD 1 [] := by
  decide +kernel

theorem h4n215_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p214).getD 2 []=h4p215.getD 2 [] := by
  decide +kernel

theorem h4n215_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p214).getD 3 []=h4p215.getD 3 [] := by
  decide +kernel

theorem h4n215_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p214).getD 4 []=h4p215.getD 4 [] := by
  decide +kernel

theorem h4n215_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p214).getD 5 []=h4p215.getD 5 [] := by
  decide +kernel

theorem h4n215_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p214).getD 6 []=h4p215.getD 6 [] := by
  decide +kernel

theorem h4n215_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p214).getD 7 []=h4p215.getD 7 [] := by
  decide +kernel

theorem h4n215_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p214).getD 8 []=h4p215.getD 8 [] := by
  decide +kernel

theorem h4n215_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p214).getD 9 []=h4p215.getD 9 [] := by
  decide +kernel

theorem h4n215_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p214).getD 10 []=h4p215.getD 10 [] := by
  decide +kernel

theorem h4n215_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p214).getD 11 []=h4p215.getD 11 [] := by
  decide +kernel

theorem h4n215_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p214).getD 12 []=h4p215.getD 12 [] := by
  decide +kernel

theorem h4n215_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p214).getD 13 []=h4p215.getD 13 [] := by
  decide +kernel

theorem h4n215_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p214).getD 14 []=h4p215.getD 14 [] := by
  decide +kernel

theorem h4n215_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p214).getD 15 []=h4p215.getD 15 [] := by
  decide +kernel

theorem h4n215_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p214).getD 16 []=h4p215.getD 16 [] := by
  decide +kernel

theorem h4n215_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p214).getD 17 []=h4p215.getD 17 [] := by
  decide +kernel

theorem h4n215_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p214).getD 18 []=h4p215.getD 18 [] := by
  decide +kernel

theorem h4n215_arithmetic : BiPoly.mul h4p13 h4p214=h4p215 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p214).getD j.val []=h4p215.getD j.val [] :=
      (fun j => Fin.cases h4n215_arithmetic_row0 (fun j => Fin.cases h4n215_arithmetic_row1 (fun j => Fin.cases h4n215_arithmetic_row2 (fun j => Fin.cases h4n215_arithmetic_row3 (fun j => Fin.cases h4n215_arithmetic_row4 (fun j => Fin.cases h4n215_arithmetic_row5 (fun j => Fin.cases h4n215_arithmetic_row6 (fun j => Fin.cases h4n215_arithmetic_row7 (fun j => Fin.cases h4n215_arithmetic_row8 (fun j => Fin.cases h4n215_arithmetic_row9 (fun j => Fin.cases h4n215_arithmetic_row10 (fun j => Fin.cases h4n215_arithmetic_row11 (fun j => Fin.cases h4n215_arithmetic_row12 (fun j => Fin.cases h4n215_arithmetic_row13 (fun j => Fin.cases h4n215_arithmetic_row14 (fun j => Fin.cases h4n215_arithmetic_row15 (fun j => Fin.cases h4n215_arithmetic_row16 (fun j => Fin.cases h4n215_arithmetic_row17 (fun j => Fin.cases h4n215_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n215 : h4e215.toBi mapPolyEnv=h4p215 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e214.toBi mapPolyEnv)=h4p215
  rw [h4n13, h4n214]
  exact h4n215_arithmetic

#print axioms h4n215_arithmetic
end StackSorting.RationalLift
