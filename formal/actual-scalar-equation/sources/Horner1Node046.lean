import BivariateRowEquality
import Horner1Base
import Horner1Node045
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p46 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 78045037055999), (Int.negSucc 131898707631359), (Int.ofNat 2981617107108480), (Int.ofNat 7789170365164800), (Int.negSucc 15629551382361599), (Int.negSucc 33307403311503359), (Int.ofNat 35723774652382080)], [(Int.ofNat 0), (Int.ofNat 833984001037440), (Int.ofNat 242361356793408), (Int.negSucc 34264700101856447), (Int.negSucc 61674595165010303), (Int.ofNat 196104426620993280), (Int.ofNat 267854612148422208), (Int.negSucc 371816903878342847), (Int.ofNat 34338448802163456)], [(Int.ofNat 0), (Int.negSucc 4091329891681919), (Int.ofNat 4912087774381056), (Int.ofNat 176229199060954272), (Int.ofNat 194693360018572512), (Int.negSucc 1030731006361097663), (Int.negSucc 922583628977607359), (Int.ofNat 1520118039283738272), (Int.negSucc 154196239175226143), (Int.ofNat 11639819679731712)], [(Int.ofNat 0), (Int.ofNat 12201733451394720), (Int.negSucc 34377847207486127), (Int.negSucc 539725787246190239), (Int.negSucc 264862546465609871), (Int.ofNat 3090400691424074208), (Int.ofNat 1921783170536191152), (Int.negSucc 3092633209986418655), (Int.negSucc 241357017830185583), (Int.ofNat 32549578074648576), (Int.ofNat 1434595109584896)], [(Int.ofNat 0), (Int.negSucc 24689100526035839), (Int.ofNat 113786278621981056), (Int.ofNat 1102390016536380384), (Int.negSucc 68209499156567903), (Int.negSucc 6023822934418130879), (Int.negSucc 3302941825261801727), (Int.ofNat 2908540727837158176), (Int.ofNat 2852108521817406048), (Int.negSucc 406170478334384063), (Int.ofNat 24574488754938624), (Int.negSucc 24223498205183)], [(Int.ofNat 0), (Int.ofNat 35813077395710400), (Int.negSucc 238038375492264671), (Int.negSucc 1591784409062242511), (Int.ofNat 896067994713739920), (Int.ofNat 8310335187952114704), (Int.ofNat 6079962662870483520), (Int.ofNat 345046640629483152), (Int.negSucc 7343702267659422767), (Int.ofNat 509629213967304240), (Int.negSucc 30169788726523391), (Int.ofNat 3521120833797120), (Int.negSucc 15340269219839)], [(Int.ofNat 0), (Int.negSucc 38356742625340319), (Int.ofNat 346778710213833936), (Int.ofNat 1680178642623836208), (Int.negSucc 1707885956148656111), (Int.negSucc 8854017697348818191), (Int.negSucc 10787067381811073903), (Int.negSucc 4582469039217027407), (Int.ofNat 8417231121894519888), (Int.ofNat 2049301733741097840), (Int.negSucc 345616208507267423), (Int.ofNat 17654211714624768), (Int.ofNat 65162456004096), (Int.negSucc 565976825855)], [(Int.ofNat 0), (Int.ofNat 30770320840930560), (Int.negSucc 368129841271860287), (Int.negSucc 1323611323436324111), (Int.ofNat 1888952878756060992), (Int.ofNat 8131510849253780160), (Int.ofNat 15083919391936467744), (Int.ofNat 7753801340769194064), (Int.negSucc 2472333770749784879), (Int.negSucc 7022402338505389439), (Int.ofNat 732376997236116912), (Int.negSucc 48456518866209983), (Int.ofNat 2530193324830464), (Int.negSucc 9118112440319)], [(Int.ofNat 0), (Int.negSucc 18550180626029759), (Int.ofNat 291208953570891744), (Int.ofNat 790149573664292208), (Int.negSucc 1437795951774841871), (Int.negSucc 7042164830740470719), (Int.negSucc 15689380546200186911), (Int.negSucc 10630344391718404271), (Int.negSucc 5235978021152387759), (Int.ofNat 8127872042738587488), (Int.ofNat 749955068331542112), (Int.negSucc 146008111271992895), (Int.ofNat 5505353897030016), (Int.ofNat 49031403626496)], [(Int.ofNat 0), (Int.ofNat 8348688335862720), (Int.negSucc 173111892219905567), (Int.negSucc 363273161003555375), (Int.ofNat 835975351840066320), (Int.ofNat 5700391181304267456), (Int.ofNat 12517032202757688240), (Int.ofNat 13072993838830796976), (Int.ofNat 8221955735526734208), (Int.negSucc 2120077580378948399), (Int.negSucc 3715219466480510159), (Int.ofNat 385967138117639952), (Int.negSucc 20974767216512447), (Int.ofNat 579951621092352)], [(Int.ofNat 0), (Int.negSucc 2755840566019199), (Int.ofNat 77129232788428416), (Int.ofNat 131680135083854448), (Int.negSucc 424138794475669823), (Int.negSucc 3990254061335517695), (Int.negSucc 8279692691420371199), (Int.negSucc 12650704897796309423), (Int.negSucc 7576859575817271983), (Int.negSucc 4411909560788701007), (Int.ofNat 3952733860335786480), (Int.ofNat 177898163617357872), (Int.negSucc 34616165150606783), (Int.ofNat 731820015031296)], [(Int.ofNat 0), (Int.ofNat 645536778730080), (Int.negSucc 25393218626009423), (Int.negSucc 38790022039228943), (Int.ofNat 211136004831274848), (Int.ofNat 2272683206110273776), (Int.ofNat 4964960663262013104), (Int.ofNat 8985316129019085888), (Int.ofNat 6689961178160587536), (Int.ofNat 5453228735937959280), (Int.negSucc 496214083031902847), (Int.negSucc 1160710969160238815), (Int.ofNat 94216958531394624), (Int.negSucc 3048109401353471)], [(Int.ofNat 0), (Int.negSucc 101168316757439), (Int.ofNat 5997216017100192), (Int.ofNat 9429211989770160), (Int.negSucc 99588274197623615), (Int.negSucc 1028691632194420847), (Int.negSucc 2766088396708139423), (Int.negSucc 4759102686739657919), (Int.negSucc 5461118334524157551), (Int.negSucc 3359634294241652687), (Int.negSucc 2211434144475890399), (Int.ofNat 1000651579621522272), (Int.ofNat 38706592009489920), (Int.negSucc 4096312901793791)], [(Int.ofNat 0), (Int.ofNat 9463693578240), (Int.negSucc 961194887198015), (Int.negSucc 1817247675606527), (Int.ofNat 38671163555770272), (Int.ofNat 368279320123193424), (Int.ofNat 1341408505909451952), (Int.ofNat 2059692102375282192), (Int.ofNat 3324407780534834304), (Int.ofNat 1907130579775187328), (Int.ofNat 1940469441919706592), (Int.ofNat 85036360291900128), (Int.negSucc 197676224710967807), (Int.ofNat 8572925764597248)], [(Int.ofNat 0), (Int.negSucc 396908323679), (Int.ofNat 93605981656752), (Int.ofNat 246864852333312), (Int.negSucc 11003310291724847), (Int.negSucc 103448006024713967), (Int.negSucc 518707335596600015), (Int.negSucc 833285530780438319), (Int.negSucc 1375981676699887295), (Int.negSucc 1231469571186235295), (Int.negSucc 771253861159419551), (Int.negSucc 580735618246441151), (Int.ofNat 113121332874979200), (Int.ofNat 5301755605854720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4177912711103), (Int.negSucc 19136135477375), (Int.ofNat 2099219227194672), (Int.ofNat 22097520311749200), (Int.ofNat 149258726700731136), (Int.ofNat 320938850228672160), (Int.ofNat 402744588226128000), (Int.ofNat 618894938591569728), (Int.ofNat 255716162150112576), (Int.ofNat 332287156958211648), (Int.ofNat 46416394254274560), (Int.negSucc 13226911944947711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 525781952064), (Int.negSucc 238348001667023), (Int.negSucc 3340934413994735), (Int.negSucc 30010475625285023), (Int.negSucc 101208561253586783), (Int.negSucc 105445582444895039), (Int.negSucc 186646082310301823), (Int.negSucc 129992205363230591), (Int.negSucc 74149705277660159), (Int.negSucc 67613030675347967), (Int.ofNat 3185791897540608)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12132369527040), (Int.ofNat 311315733331200), (Int.ofNat 3862557266498784), (Int.ofNat 22102622363342304), (Int.ofNat 30754541120421888), (Int.ofNat 31430523453495552), (Int.ofNat 51719508712507392), (Int.ofNat 10800964822008960), (Int.ofNat 22290801295988736), (Int.ofNat 3961096093052928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13044614251103), (Int.negSucc 269373991633055), (Int.negSucc 2886053859157823), (Int.negSucc 7537570980024959), (Int.negSucc 4179229392947327), (Int.negSucc 9627494353978751), (Int.negSucc 5032639791521279), (Int.negSucc 1819686525378047), (Int.negSucc 2363329947064319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6565516254144), (Int.ofNat 179690368341312), (Int.ofNat 1071539662662144), (Int.ofNat 961159832581248), (Int.ofNat 542971195755264), (Int.ofNat 1416147669474048), (Int.negSucc 101053756984319), (Int.ofNat 362763015782400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2494032405119), (Int.negSucc 64209821433983), (Int.negSucc 160020107186687), (Int.negSucc 2171121283583), (Int.negSucc 102249988830719), (Int.negSucc 22672688486399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 508696899840), (Int.ofNat 8705736942336), (Int.ofNat 3400903272960)]]

theorem h1n46_arithmetic_row0 :
    (BiPoly.mul h1p4 h1p45).getD 0 []=h1p46.getD 0 [] := by
  decide +kernel

theorem h1n46_arithmetic_row1 :
    (BiPoly.mul h1p4 h1p45).getD 1 []=h1p46.getD 1 [] := by
  decide +kernel

theorem h1n46_arithmetic_row2 :
    (BiPoly.mul h1p4 h1p45).getD 2 []=h1p46.getD 2 [] := by
  decide +kernel

theorem h1n46_arithmetic_row3 :
    (BiPoly.mul h1p4 h1p45).getD 3 []=h1p46.getD 3 [] := by
  decide +kernel

theorem h1n46_arithmetic_row4 :
    (BiPoly.mul h1p4 h1p45).getD 4 []=h1p46.getD 4 [] := by
  decide +kernel

theorem h1n46_arithmetic_row5 :
    (BiPoly.mul h1p4 h1p45).getD 5 []=h1p46.getD 5 [] := by
  decide +kernel

theorem h1n46_arithmetic_row6 :
    (BiPoly.mul h1p4 h1p45).getD 6 []=h1p46.getD 6 [] := by
  decide +kernel

theorem h1n46_arithmetic_row7 :
    (BiPoly.mul h1p4 h1p45).getD 7 []=h1p46.getD 7 [] := by
  decide +kernel

theorem h1n46_arithmetic_row8 :
    (BiPoly.mul h1p4 h1p45).getD 8 []=h1p46.getD 8 [] := by
  decide +kernel

theorem h1n46_arithmetic_row9 :
    (BiPoly.mul h1p4 h1p45).getD 9 []=h1p46.getD 9 [] := by
  decide +kernel

theorem h1n46_arithmetic_row10 :
    (BiPoly.mul h1p4 h1p45).getD 10 []=h1p46.getD 10 [] := by
  decide +kernel

theorem h1n46_arithmetic_row11 :
    (BiPoly.mul h1p4 h1p45).getD 11 []=h1p46.getD 11 [] := by
  decide +kernel

theorem h1n46_arithmetic_row12 :
    (BiPoly.mul h1p4 h1p45).getD 12 []=h1p46.getD 12 [] := by
  decide +kernel

theorem h1n46_arithmetic_row13 :
    (BiPoly.mul h1p4 h1p45).getD 13 []=h1p46.getD 13 [] := by
  decide +kernel

theorem h1n46_arithmetic_row14 :
    (BiPoly.mul h1p4 h1p45).getD 14 []=h1p46.getD 14 [] := by
  decide +kernel

theorem h1n46_arithmetic_row15 :
    (BiPoly.mul h1p4 h1p45).getD 15 []=h1p46.getD 15 [] := by
  decide +kernel

theorem h1n46_arithmetic_row16 :
    (BiPoly.mul h1p4 h1p45).getD 16 []=h1p46.getD 16 [] := by
  decide +kernel

theorem h1n46_arithmetic_row17 :
    (BiPoly.mul h1p4 h1p45).getD 17 []=h1p46.getD 17 [] := by
  decide +kernel

theorem h1n46_arithmetic_row18 :
    (BiPoly.mul h1p4 h1p45).getD 18 []=h1p46.getD 18 [] := by
  decide +kernel

theorem h1n46_arithmetic_row19 :
    (BiPoly.mul h1p4 h1p45).getD 19 []=h1p46.getD 19 [] := by
  decide +kernel

theorem h1n46_arithmetic_row20 :
    (BiPoly.mul h1p4 h1p45).getD 20 []=h1p46.getD 20 [] := by
  decide +kernel

theorem h1n46_arithmetic_row21 :
    (BiPoly.mul h1p4 h1p45).getD 21 []=h1p46.getD 21 [] := by
  decide +kernel

theorem h1n46_arithmetic : BiPoly.mul h1p4 h1p45=h1p46 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p4 h1p45).getD j.val []=h1p46.getD j.val [] :=
      (fun j => Fin.cases h1n46_arithmetic_row0 (fun j => Fin.cases h1n46_arithmetic_row1 (fun j => Fin.cases h1n46_arithmetic_row2 (fun j => Fin.cases h1n46_arithmetic_row3 (fun j => Fin.cases h1n46_arithmetic_row4 (fun j => Fin.cases h1n46_arithmetic_row5 (fun j => Fin.cases h1n46_arithmetic_row6 (fun j => Fin.cases h1n46_arithmetic_row7 (fun j => Fin.cases h1n46_arithmetic_row8 (fun j => Fin.cases h1n46_arithmetic_row9 (fun j => Fin.cases h1n46_arithmetic_row10 (fun j => Fin.cases h1n46_arithmetic_row11 (fun j => Fin.cases h1n46_arithmetic_row12 (fun j => Fin.cases h1n46_arithmetic_row13 (fun j => Fin.cases h1n46_arithmetic_row14 (fun j => Fin.cases h1n46_arithmetic_row15 (fun j => Fin.cases h1n46_arithmetic_row16 (fun j => Fin.cases h1n46_arithmetic_row17 (fun j => Fin.cases h1n46_arithmetic_row18 (fun j => Fin.cases h1n46_arithmetic_row19 (fun j => Fin.cases h1n46_arithmetic_row20 (fun j => Fin.cases h1n46_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n46 : h1e46.toBi mapPolyEnv=h1p46 := by
  change BiPoly.mul (h1e4.toBi mapPolyEnv) (h1e45.toBi mapPolyEnv)=h1p46
  rw [h1n4, h1n45]
  exact h1n46_arithmetic

#print axioms h1n46_arithmetic
end StackSorting.RationalLift
