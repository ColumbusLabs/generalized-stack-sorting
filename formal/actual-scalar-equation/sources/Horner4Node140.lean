import BivariateRowEquality
import Horner4Base
import Horner4Node139
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p140 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 18282566281907808000), (Int.ofNat 138246775258949124480), (Int.ofNat 183665363597964766080), (Int.negSucc 491204794623808371839), (Int.negSucc 563972174553088632959), (Int.ofNat 679291455050638214400)], [(Int.ofNat 0), (Int.negSucc 168832098214265041919), (Int.negSucc 1285832161228052093183), (Int.negSucc 1797214878730040833151), (Int.ofNat 4174710538646375891712), (Int.ofNat 4831711560673008683904), (Int.negSucc 5996414282506085751551), (Int.ofNat 492072687562749926400)], [(Int.ofNat 0), (Int.ofNat 734944436798020804800), (Int.ofNat 5487410698750529128800), (Int.ofNat 7836309343005973386624), (Int.negSucc 15597828193294745623295), (Int.negSucc 18982142114417641986047), (Int.ofNat 21680169637079831277600), (Int.negSucc 2256284769080820815807), (Int.ofNat 115368257197774485504)], [(Int.ofNat 0), (Int.negSucc 1998209214447453017279), (Int.negSucc 14223174371503955555039), (Int.negSucc 20535447671951394508415), (Int.ofNat 31820329891406676580992), (Int.ofNat 44550379383762782152512), (Int.negSucc 38443846252867097355935), (Int.ofNat 768006255569269957632), (Int.negSucc 28553333552563653503), (Int.ofNat 8475023421060083712)], [(Int.ofNat 0), (Int.ofNat 3777649515677141138880), (Int.ofNat 25054576568464338520992), (Int.ofNat 36963127311095702984832), (Int.negSucc 34157952886435982456255), (Int.negSucc 68546117822055859532159), (Int.ofNat 23110352952103901177568), (Int.ofNat 14961122635582871070336), (Int.negSucc 1471466858492703119615), (Int.ofNat 46146399555774530304), (Int.negSucc 45169726132776959)], [(Int.ofNat 0), (Int.negSucc 5221477975721541887519), (Int.negSucc 31913461193765094327023), (Int.negSucc 49784446624290999989327), (Int.ofNat 6515630812694143370880), (Int.ofNat 68917693990308813486720), (Int.ofNat 37446600529688130388368), (Int.negSucc 38002406400861891455375), (Int.ofNat 2278067861985906438432), (Int.negSucc 63701378125471355903), (Int.ofNat 1475916543772190208)], [(Int.ofNat 0), (Int.ofNat 5400865113146403516000), (Int.ofNat 30654724510090568131056), (Int.ofNat 53443051513497989526240), (Int.ofNat 36305380492527488438592), (Int.negSucc 35876406987728336002463), (Int.negSucc 92408238831648680829359), (Int.ofNat 31447842488014208649696), (Int.ofNat 4034823304770901996128), (Int.negSucc 360572795787628696895), (Int.ofNat 8804346283502940672)], [(Int.ofNat 0), (Int.negSucc 4213551810491191954079), (Int.negSucc 22942044023276703078863), (Int.negSucc 47620531038716569115567), (Int.negSucc 61265460880464780924575), (Int.negSucc 12535434932401540981151), (Int.ofNat 82377774312985467272880), (Int.ofNat 15346524022768604855664), (Int.negSucc 13494010400475719805791), (Int.ofNat 522049076778542289408), (Int.ofNat 291474362854964736)], [(Int.ofNat 0), (Int.ofNat 2472571319827507863840), (Int.ofNat 13715420068924466073840), (Int.ofNat 35636219511321664339776), (Int.ofNat 56657138585542105409568), (Int.ofNat 43814477524526709550560), (Int.negSucc 22183513209244926898127), (Int.negSucc 51203186003475400296383), (Int.ofNat 9810746568679863957408), (Int.ofNat 816670160898160341888), (Int.negSucc 47435766453800866943)], [(Int.ofNat 0), (Int.negSucc 1078102528931916692639), (Int.negSucc 6634231647033190529231), (Int.negSucc 22057870101377530668767), (Int.negSucc 37675894586881203918719), (Int.negSucc 44202687398320273738415), (Int.negSucc 25579869362265978796319), (Int.ofNat 37353586161108524581296), (Int.ofNat 5979398544560238916608), (Int.negSucc 1964742978507503500079), (Int.negSucc 1790384952310856927)], [(Int.ofNat 0), (Int.ofNat 341212360555180614240), (Int.ofNat 2582895835089086733072), (Int.ofNat 10947365289260046517104), (Int.ofNat 20532743218746532106640), (Int.ofNat 27892706110125721517088), (Int.ofNat 32890416746592696206976), (Int.negSucc 2459481733249291355759), (Int.negSucc 12911157877097433442031), (Int.ofNat 584777323485564513984), (Int.ofNat 104845714860651374016)], [(Int.ofNat 0), (Int.negSucc 75304335396950393759), (Int.negSucc 789562968725320984655), (Int.negSucc 4197564834079829000687), (Int.negSucc 9704108425410376819199), (Int.negSucc 13179368834827102135583), (Int.negSucc 18947173863261146842367), (Int.negSucc 13551503271701662031903), (Int.ofNat 5752533497505053623200), (Int.ofNat 1307288494958909570784), (Int.negSucc 45663341515035659711)], [(Int.ofNat 0), (Int.ofNat 10802202485811328800), (Int.ofNat 181717812616870873584), (Int.ofNat 1193804755757858602656), (Int.ofNat 3824874113300106725664), (Int.ofNat 5385116797254874816128), (Int.ofNat 6873958986602178267936), (Int.ofNat 9947730703694405452416), (Int.ofNat 1689311761532831733408), (Int.negSucc 1131914024687540758751), (Int.negSucc 72802610814495597119)], [(Int.ofNat 0), (Int.negSucc 878256132906738239), (Int.negSucc 29595887658153930815), (Int.negSucc 239908556884200851951), (Int.negSucc 1148869050003404042111), (Int.negSucc 1999099800208959317999), (Int.negSucc 1913441218468125809183), (Int.negSucc 3407547567863174260607), (Int.negSucc 2656840607201797424063), (Int.ofNat 52120073410778652480), (Int.ofNat 61291941005973642624)], [(Int.ofNat 0), (Int.ofNat 28704564252650880), (Int.ofNat 3063719190237586848), (Int.ofNat 31837210971854034384), (Int.ofNat 239728327761358590480), (Int.ofNat 607300289926890579648), (Int.ofNat 539333704612744659648), (Int.ofNat 618195484280268645696), (Int.ofNat 1079562536548199982144), (Int.ofNat 303887513102044421376), (Int.ofNat 2293409976923702016)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 153735194575673855), (Int.negSucc 2482030587204500543), (Int.negSucc 31278737267735864543), (Int.negSucc 130200967170113688863), (Int.negSucc 154348759067070743423), (Int.negSucc 63619780815926922815), (Int.negSucc 191318305733319694463), (Int.negSucc 150119795232505733759), (Int.negSucc 17279938645362452735)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 85438108715310720), (Int.ofNat 2098623742564941216), (Int.ofNat 17157012026283751968), (Int.ofNat 32686555059923561856), (Int.ofNat 9629050880676647808), (Int.ofNat 7672386302364993408), (Int.ofNat 28712837352353910912), (Int.ofNat 6432198814367638272)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 35953555777574399), (Int.negSucc 1105417125275073407), (Int.negSucc 3988319034942745343), (Int.negSucc 2406386420661529727), (Int.ofNat 2090827722030001920), (Int.negSucc 1937866179630200831), (Int.negSucc 749350492626309119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11553998772939264), (Int.ofNat 208977824369102976), (Int.ofNat 250708402437883776), (Int.negSucc 242062502417130239)]]

theorem h4n140_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p139).getD 0 []=h4p140.getD 0 [] := by
  decide +kernel

theorem h4n140_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p139).getD 1 []=h4p140.getD 1 [] := by
  decide +kernel

theorem h4n140_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p139).getD 2 []=h4p140.getD 2 [] := by
  decide +kernel

theorem h4n140_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p139).getD 3 []=h4p140.getD 3 [] := by
  decide +kernel

theorem h4n140_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p139).getD 4 []=h4p140.getD 4 [] := by
  decide +kernel

theorem h4n140_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p139).getD 5 []=h4p140.getD 5 [] := by
  decide +kernel

theorem h4n140_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p139).getD 6 []=h4p140.getD 6 [] := by
  decide +kernel

theorem h4n140_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p139).getD 7 []=h4p140.getD 7 [] := by
  decide +kernel

theorem h4n140_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p139).getD 8 []=h4p140.getD 8 [] := by
  decide +kernel

theorem h4n140_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p139).getD 9 []=h4p140.getD 9 [] := by
  decide +kernel

theorem h4n140_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p139).getD 10 []=h4p140.getD 10 [] := by
  decide +kernel

theorem h4n140_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p139).getD 11 []=h4p140.getD 11 [] := by
  decide +kernel

theorem h4n140_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p139).getD 12 []=h4p140.getD 12 [] := by
  decide +kernel

theorem h4n140_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p139).getD 13 []=h4p140.getD 13 [] := by
  decide +kernel

theorem h4n140_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p139).getD 14 []=h4p140.getD 14 [] := by
  decide +kernel

theorem h4n140_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p139).getD 15 []=h4p140.getD 15 [] := by
  decide +kernel

theorem h4n140_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p139).getD 16 []=h4p140.getD 16 [] := by
  decide +kernel

theorem h4n140_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p139).getD 17 []=h4p140.getD 17 [] := by
  decide +kernel

theorem h4n140_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p139).getD 18 []=h4p140.getD 18 [] := by
  decide +kernel

theorem h4n140_arithmetic : BiPoly.mul h4p13 h4p139=h4p140 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p139).getD j.val []=h4p140.getD j.val [] :=
      (fun j => Fin.cases h4n140_arithmetic_row0 (fun j => Fin.cases h4n140_arithmetic_row1 (fun j => Fin.cases h4n140_arithmetic_row2 (fun j => Fin.cases h4n140_arithmetic_row3 (fun j => Fin.cases h4n140_arithmetic_row4 (fun j => Fin.cases h4n140_arithmetic_row5 (fun j => Fin.cases h4n140_arithmetic_row6 (fun j => Fin.cases h4n140_arithmetic_row7 (fun j => Fin.cases h4n140_arithmetic_row8 (fun j => Fin.cases h4n140_arithmetic_row9 (fun j => Fin.cases h4n140_arithmetic_row10 (fun j => Fin.cases h4n140_arithmetic_row11 (fun j => Fin.cases h4n140_arithmetic_row12 (fun j => Fin.cases h4n140_arithmetic_row13 (fun j => Fin.cases h4n140_arithmetic_row14 (fun j => Fin.cases h4n140_arithmetic_row15 (fun j => Fin.cases h4n140_arithmetic_row16 (fun j => Fin.cases h4n140_arithmetic_row17 (fun j => Fin.cases h4n140_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n140 : h4e140.toBi mapPolyEnv=h4p140 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e139.toBi mapPolyEnv)=h4p140
  rw [h4n13, h4n139]
  exact h4n140_arithmetic

#print axioms h4n140_arithmetic
end StackSorting.RationalLift
